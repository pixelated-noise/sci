(ns sci.core
  "Public API for SCI — backed by the explicit stack VM."
  (:refer-clojure :exclude [eval read read-string alter-var-root intern resolve
                            read+string with-redefs binding assert
                            with-in-str with-out-str future pmap
                            with-bindings create-ns find-ns ns])
  (:require [sci.vm.machine :as machine]
            [sci.vm.step :as step]
            [sci.vm.host :as host]
            [sci.vm.freeze :as vm-freeze]
            [edamame.core :as edamame]
            [sci.lang]
            [sci.impl.types]
            #?(:clj [clojure.string :as str])))

(declare read-eval)

;; ============================================================
;; Reader
;; ============================================================

(def ^:private special-forms-sq
  #{'if 'do 'let 'fn 'def 'quote 'var 'loop 'recur
    'try 'catch 'finally 'throw 'new 'set! 'monitor-enter
    'monitor-exit '& 'binding
    ;; Special reader symbols that should not be namespace-qualified
    '... '__})

(defn- sq-resolve-class
  "Try to resolve sym as a Java class; returns fully-qualified symbol or nil."
  [sym]
  #?(:clj (let [resolved (clojure.core/resolve sym)]
             (when (instance? Class resolved)
               (symbol (.getName ^Class resolved))))
     :cljs nil))

(defn- make-syntax-quote-resolver
  "Returns a :resolve-symbol fn for edamame syntax-quote.
   heap-atom may be nil (for contexts without a live heap).
   ns-atom, if provided, supplies :refer-clojure-excludes."
  ([current-ns heap-atom] (make-syntax-quote-resolver current-ns heap-atom nil))
  ([current-ns heap-atom ns-atom]
  (fn [sym]
    (let [sym-name (name sym)]
      (cond
        ;; Already namespace-qualified → keep as-is
        (namespace sym) sym

        ;; Special forms → keep as-is
        (contains? special-forms-sq sym) sym

        ;; Constructor form: Foo. → resolve class, add . back
        #?(:clj  (.endsWith sym-name ".")
           :cljs (= "." (last sym-name)))
        (let [class-sym (symbol (subs sym-name 0 (dec (count sym-name))))]
          (if-let [fq (sq-resolve-class class-sym)]
            (symbol (str (name fq) "."))
            (symbol (str current-ns "." sym-name))))

        ;; Already has dots in the middle → fully qualified host class, keep as-is
        #?(:clj  (> (.indexOf sym-name ".") -1)
           :cljs (clojure.string/includes? sym-name "."))
        sym

        ;; Fallback: heap → Java class → host Clojure var → current-ns qualify
        :else
        (or
         ;; Check SCI type (deftype/defrecord) in ns-table — use dotted form like Clojure
         (when ns-atom
           (let [types (get-in @ns-atom [current-ns :types])
                 type-obj (get types (symbol sym-name))]
             (when (instance? sci.lang.Type type-obj)
               ;; Use the type's own name (which is the dotted form: ns.Name)
               (symbol (.getName ^sci.lang.Type type-obj)))))
         ;; Check SCI heap: sym defined/referred in current ns?
         (when heap-atom
           (let [h     @heap-atom
                 entry (get h (symbol (str current-ns) sym-name))]
             (when entry
               (or (when-let [orig (:sci.impl/var-sym (:meta entry))]
                     ;; referred from another ns
                     (when (not= (namespace orig) (str current-ns))
                       (symbol (namespace orig) sym-name)))
                   ;; defined in current ns
                   (symbol (str current-ns) sym-name)))))
         ;; Java class?
         (sq-resolve-class sym)
         ;; Host Clojure var from standard namespaces (clojure.core etc.) only.
         ;; We restrict to standard namespaces to avoid picking up host-level vars
         ;; that happen to shadow SCI user-defined symbols (e.g. sci.copy-ns-test-ns/bar).
         (let [excluded? (when ns-atom
                           (let [excludes (get-in @ns-atom [current-ns :refer-clojure-excludes])]
                             (and excludes (contains? excludes (symbol sym-name)))))
               resolved (when-not excluded?
                          #?(:clj (clojure.core/resolve sym) :cljs nil))]
           (when resolved
             (let [m (meta resolved)
                   resolved-ns (str (:ns m))]
               ;; Only use resolution from standard SCI-accessible namespaces
               (when (contains? #{"clojure.core" "clojure.string" "clojure.set"
                                  "clojure.walk" "clojure.edn" "clojure.repl"
                                  "cljs.core" "cljs.string"}
                                resolved-ns)
                 (symbol resolved-ns (str (:name m)))))))
         ;; Default: qualify with current ns
         (symbol (str current-ns) sym-name)))))))

(defn- make-reader-opts
  "Create edamame reader options, optionally with a current namespace for ::keyword resolution."
  ([] (make-reader-opts 'user nil nil nil))
  ([current-ns] (make-reader-opts current-ns nil nil nil))
  ([current-ns ns-aliases] (make-reader-opts current-ns ns-aliases nil nil))
  ([current-ns ns-aliases heap-atom] (make-reader-opts current-ns ns-aliases heap-atom nil))
  ([current-ns ns-aliases heap-atom ns-atom]
   {:all true
    :row-key :line
    :col-key :column
    :end-row-key :end-line
    :end-col-key :end-column
    :location? seq?
    :read-cond :allow
    :features #{:clj}
    :fn true
    :quote true
    :syntax-quote {:resolve-symbol (make-syntax-quote-resolver current-ns heap-atom ns-atom)}
    :var true
    :deref true
    :regex true
    :auto-resolve (merge {:current (or current-ns 'user)}
                        ns-aliases)}))

(defn read-all
  "Read all forms from a string."
  ([s] (read-all s 'user nil))
  ([s current-ns] (read-all s current-ns nil))
  ([s current-ns extra-opts]
   (let [opts (make-reader-opts current-ns)]
     (edamame/parse-string-all s (if extra-opts
                                   (merge opts extra-opts)
                                   opts)))))

;; ============================================================
;; Context / init
;; ============================================================

(defn init
  "Create an SCI context (the machine's initial state)."
  [opts]
  (let [{:keys [bindings namespaces classes aliases ns-aliases imports
                features load-fn readers deny allow file initial-ns
                disable-arity-checks]} opts
        heap (host/default-heap)
        ns-table (host/default-ns-table)
        ;; Override satisfies? to handle SCI protocols
        heap (assoc heap (symbol "clojure.core" "satisfies?")
                    {:val (fn sci-satisfies? [protocol x]
                            (cond
                              (and (map? protocol) (= :sci/protocol (:type protocol)))
                              (let [impls @(:impls protocol)
                                    target-type (type x)]
                                (boolean
                                 (or (get impls target-type)
                                     (some (fn [[t _]]
                                             (and (class? t)
                                                  (instance? t x)))
                                           impls)
                                     (when (nil? x) (get impls nil))
                                     (get impls Object)
                                     (get impls :default))))
                              ;; Host protocol wrapped in a map (from sci/new-var)
                              (and (map? protocol) (:protocol protocol))
                              (clojure.core/satisfies? (:protocol protocol) x)
                              ;; Fall back to clojure.core/satisfies? for real protocols
                              :else
                              (clojure.core/satisfies? protocol x)))
                     :meta {:name 'satisfies? :doc #?(:clj (:doc (meta #'clojure.core/satisfies?)) :cljs nil)}
                     :dynamic? false})
        ;; Override deref to handle SCI type instances with deref methods
        heap (assoc heap (symbol "clojure.core" "deref")
                    {:val (fn sci-deref
                            ([ref]
                             (if-let [type-obj (:type (clojure.core/meta ref))]
                               (if (instance? sci.lang.Type type-obj)
                                 (let [methods (.-methods ^sci.lang.Type type-obj)
                                       deref-fn (get methods 'deref)]
                                   (if deref-fn
                                     (deref-fn ref)
                                     (clojure.core/deref ref)))
                                 (clojure.core/deref ref))
                               (clojure.core/deref ref)))
                            ([ref timeout-ms timeout-val]
                             (clojure.core/deref ref timeout-ms timeout-val)))
                     :meta {:name 'deref}
                     :dynamic? false})
        ;; Override swap! and reset! to handle SCI type instances with swap/reset methods
        heap (assoc heap (symbol "clojure.core" "swap!")
                    {:val (fn sci-swap!
                            ([ref f]
                             (if-let [type-obj (:type (clojure.core/meta ref))]
                               (if (instance? sci.lang.Type type-obj)
                                 (let [methods (.-methods ^sci.lang.Type type-obj)
                                       swap-fn (get methods 'swap)]
                                   (if swap-fn
                                     (swap-fn ref f)
                                     (clojure.core/swap! ref f)))
                                 (clojure.core/swap! ref f))
                               (clojure.core/swap! ref f)))
                            ([ref f a]
                             (if-let [type-obj (:type (clojure.core/meta ref))]
                               (if (instance? sci.lang.Type type-obj)
                                 (let [methods (.-methods ^sci.lang.Type type-obj)
                                       swap-fn (get methods 'swap)]
                                   (if swap-fn
                                     (swap-fn ref f a)
                                     (clojure.core/swap! ref f a)))
                                 (clojure.core/swap! ref f a))
                               (clojure.core/swap! ref f a)))
                            ([ref f a b]
                             (if-let [type-obj (:type (clojure.core/meta ref))]
                               (if (instance? sci.lang.Type type-obj)
                                 (let [methods (.-methods ^sci.lang.Type type-obj)
                                       swap-fn (get methods 'swap)]
                                   (if swap-fn
                                     (swap-fn ref f a b)
                                     (clojure.core/swap! ref f a b)))
                                 (clojure.core/swap! ref f a b))
                               (clojure.core/swap! ref f a b)))
                            ([ref f a b & args]
                             (if-let [type-obj (:type (clojure.core/meta ref))]
                               (if (instance? sci.lang.Type type-obj)
                                 (let [methods (.-methods ^sci.lang.Type type-obj)
                                       swap-fn (get methods 'swap)]
                                   (if swap-fn
                                     (apply swap-fn ref f a b args)
                                     (apply clojure.core/swap! ref f a b args)))
                                 (apply clojure.core/swap! ref f a b args))
                               (apply clojure.core/swap! ref f a b args))))
                     :meta {:name 'swap!}
                     :dynamic? false})
        heap (assoc heap (symbol "clojure.core" "reset!")
                    {:val (fn sci-reset! [ref v]
                            (if-let [type-obj (:type (clojure.core/meta ref))]
                              (if (instance? sci.lang.Type type-obj)
                                (let [methods (.-methods ^sci.lang.Type type-obj)
                                      reset-fn (get methods 'reset)]
                                  (if reset-fn
                                    (reset-fn ref v)
                                    (clojure.core/reset! ref v)))
                                (clojure.core/reset! ref v))
                              (clojure.core/reset! ref v)))
                     :meta {:name 'reset!}
                     :dynamic? false})
        ;; Override reset-vals! and swap-vals! to handle SCI type instances
        heap (assoc heap (symbol "clojure.core" "reset-vals!")
                    {:val (fn sci-reset-vals! [ref newval]
                            (if-let [type-obj (:type (clojure.core/meta ref))]
                              (if (instance? sci.lang.Type type-obj)
                                (let [methods (.-methods ^sci.lang.Type type-obj)
                                      rv-fn (get methods 'resetVals)]
                                  (if rv-fn
                                    (rv-fn ref newval)
                                    (clojure.core/reset-vals! ref newval)))
                                (clojure.core/reset-vals! ref newval))
                              (clojure.core/reset-vals! ref newval)))
                     :meta {:name 'reset-vals! :doc #?(:clj (:doc (meta #'clojure.core/reset-vals!)) :cljs nil)}
                     :dynamic? false})
        heap (assoc heap (symbol "clojure.core" "swap-vals!")
                    {:val (fn sci-swap-vals!
                            ([ref f]
                             (if-let [type-obj (:type (clojure.core/meta ref))]
                               (if (instance? sci.lang.Type type-obj)
                                 (let [methods (.-methods ^sci.lang.Type type-obj)
                                       sv-fn (get methods 'swapVals)]
                                   (if sv-fn
                                     (sv-fn ref f)
                                     (clojure.core/swap-vals! ref f)))
                                 (clojure.core/swap-vals! ref f))
                               (clojure.core/swap-vals! ref f)))
                            ([ref f a] (clojure.core/swap-vals! ref f a))
                            ([ref f a b] (clojure.core/swap-vals! ref f a b))
                            ([ref f a b & args] (apply clojure.core/swap-vals! ref f a b args)))
                     :meta {:name 'swap-vals! :doc #?(:clj (:doc (meta #'clojure.core/swap-vals!)) :cljs nil)}
                     :dynamic? false})
        heap (assoc heap (symbol "clojure.core" "compare-and-set!")
                    {:val (fn sci-compare-and-set! [ref oldval newval]
                            (if-let [type-obj (:type (clojure.core/meta ref))]
                              (if (instance? sci.lang.Type type-obj)
                                (let [methods (.-methods ^sci.lang.Type type-obj)
                                      cas-fn (get methods 'compareAndSet)]
                                  (if cas-fn
                                    (cas-fn ref oldval newval)
                                    (clojure.core/compare-and-set! ref oldval newval)))
                                (clojure.core/compare-and-set! ref oldval newval))
                              (clojure.core/compare-and-set! ref oldval newval)))
                     :meta {:name 'compare-and-set! :doc #?(:clj (:doc (meta #'clojure.core/compare-and-set!)) :cljs nil)}
                     :dynamic? false})
        ;; Override derive/underive/isa?/parents/ancestors/descendants to:
        ;; 1. Handle SCI types (sci.lang.Type) by converting to qualified symbols
        ;; 2. Use a per-context hierarchy atom instead of the global one
        hierarchy-atom (atom (clojure.core/make-hierarchy))
        heap (let [type->tag (fn [t]
                               (if (instance? sci.lang.Type t)
                                 (let [n (.getName ^sci.lang.Type t)
                                       idx (.lastIndexOf ^String n ".")]
                                   (if (pos? idx)
                                     (symbol (subs n 0 idx) (subs n (inc idx)))
                                     (symbol "user" n)))
                                 t))]
               (-> heap
                   (assoc (symbol "clojure.core" "make-hierarchy")
                          {:val clojure.core/make-hierarchy
                           :meta {:name 'make-hierarchy}})
                   (assoc (symbol "clojure.core" "derive")
                          {:val (fn sci-derive
                                  ([tag parent]
                                   (swap! hierarchy-atom clojure.core/derive (type->tag tag) (type->tag parent))
                                   nil)
                                  ([h tag parent] (clojure.core/derive h (type->tag tag) (type->tag parent))))
                           :meta {:name 'derive :doc #?(:clj (:doc (meta #'clojure.core/derive)) :cljs nil)}
                           :dynamic? false})
                   (assoc (symbol "clojure.core" "underive")
                          {:val (fn sci-underive
                                  ([tag parent]
                                   (swap! hierarchy-atom clojure.core/underive (type->tag tag) (type->tag parent))
                                   nil)
                                  ([h tag parent] (clojure.core/underive h (type->tag tag) (type->tag parent))))
                           :meta {:name 'underive :doc #?(:clj (:doc (meta #'clojure.core/underive)) :cljs nil)}
                           :dynamic? false})
                   (assoc (symbol "clojure.core" "isa?")
                          {:val (fn sci-isa?
                                  ([child parent] (clojure.core/isa? @hierarchy-atom (type->tag child) (type->tag parent)))
                                  ([h child parent] (clojure.core/isa? h (type->tag child) (type->tag parent))))
                           :meta {:name 'isa? :doc #?(:clj (:doc (meta #'clojure.core/isa?)) :cljs nil)}
                           :dynamic? false})
                   (assoc (symbol "clojure.core" "parents")
                          {:val (fn sci-parents
                                  ([tag] (clojure.core/parents @hierarchy-atom (type->tag tag)))
                                  ([h tag] (clojure.core/parents h (type->tag tag))))
                           :meta {:name 'parents :doc #?(:clj (:doc (meta #'clojure.core/parents)) :cljs nil)}
                           :dynamic? false})
                   (assoc (symbol "clojure.core" "ancestors")
                          {:val (fn sci-ancestors
                                  ([tag] (clojure.core/ancestors @hierarchy-atom (type->tag tag)))
                                  ([h tag] (clojure.core/ancestors h (type->tag tag))))
                           :meta {:name 'ancestors :doc #?(:clj (:doc (meta #'clojure.core/ancestors)) :cljs nil)}
                           :dynamic? false})
                   (assoc (symbol "clojure.core" "descendants")
                          {:val (fn sci-descendants
                                  ([tag] (clojure.core/descendants @hierarchy-atom (type->tag tag)))
                                  ([h tag] (clojure.core/descendants h (type->tag tag))))
                           :meta {:name 'descendants :doc #?(:clj (:doc (meta #'clojure.core/descendants)) :cljs nil)}
                           :dynamic? false})))
        ;; Install user bindings into heap as user/sym vars
        ;; :dynamic? true so thread-local bindings (sci/binding, sci/with-bindings) work.
        ;; Atom-backed vars (from new-dynamic-var) are stored as atoms; resolve-symbol derefs them.
        heap (reduce-kv
              (fn [h sym val]
                (let [sym-name (if (symbol? sym) (name sym) (str sym))
                      qualified (symbol "user" sym-name)
                      ;; Unwrap sci.lang.Var (from copy-var) to get actual value + meta
                      sci-var? (instance? sci.lang.Var val)
                      actual-val (if sci-var? @val val)
                      vm (meta val)
                      is-macro? (or (:macro vm) (:sci/macro vm))
                      ;; Check for :sci/built-in in DynamicVar meta-map
                      built-in? (and (instance? sci.lang.DynamicVar val)
                                     (:sci/built-in (meta val)))]
                  (assoc h qualified (cond-> {:val actual-val
                                              :meta (or vm {})
                                              :macro? (boolean is-macro?)
                                              :dynamic? true
                                              ;; Mark as raw binding so (var x) doesn't inject :name/:ns
                                              :user-binding? (not sci-var?)}
                                       is-macro? (assoc :host-macro? true)
                                       built-in? (assoc :sci/built-in true)))))
              heap
              (or bindings {}))
        ;; Install custom namespaces — mark entries as user overrides so special forms
        ;; like (ns ...) can be overridden: {:namespaces {'clojure.core {'ns inc}}}
        heap (reduce-kv
              (fn [h ns-sym ns-map]
                (reduce-kv
                 (fn [h2 sym val]
                   (let [sym-name (if (symbol? sym) (name sym) (str sym))
                         qualified (symbol (str ns-sym) sym-name)
                         ;; Unwrap sci.lang.Var (from copy-var) to get actual value + meta
                         sci-var? (instance? sci.lang.Var val)
                         actual-val (if sci-var? @val val)
                         vm (meta val)
                         is-macro? (or (:macro vm) (:sci/macro vm))
                         is-dynamic? (or (boolean (:dynamic? val))
                                         (boolean (:dynamic vm)))]
                     (assoc h2 qualified (cond-> {:val actual-val
                                                   :meta (or vm {})
                                                   :macro? (boolean is-macro?)
                                                   :dynamic? is-dynamic?
                                                   :user-override? true}
                                           is-macro? (assoc :host-macro? true)))))
                 h
                 ns-map))
              heap
              (or namespaces {}))
        ;; Set up aliases in user namespace
        ns-table (if aliases
                   (update ns-table 'user assoc :aliases
                           (reduce-kv (fn [a k v] (assoc a k v)) {} aliases))
                   ns-table)]
    {:heap heap
     :heap-atom (atom heap)
     :ns-table ns-table
     :ns-atom (atom ns-table)
     :ns-objects (atom {})
     :current-ns-atom (atom (or initial-ns 'user))
     :loaded-libs (atom #{})
     :hierarchy-atom hierarchy-atom
     :classes (or classes {})
     :features (or features #{:clj})
     :load-fn load-fn
     :readers readers
     :ns-aliases ns-aliases
     :deny deny
     :allow allow
     :file file
     :disable-arity-checks (boolean disable-arity-checks)
     #?@(:clj [:inverse-registry (host/inverse-registry heap)])}))

(defn fork
  "Create a fork of a context — an independent copy."
  [ctx]
  (let [heap @(:heap-atom ctx)
        ns-table @(:ns-atom ctx)]
    (assoc ctx
           :heap heap
           :heap-atom (atom heap)
           :ns-table ns-table
           :ns-atom (atom ns-table)
           :current-ns-atom (atom @(:current-ns-atom ctx)))))

;; ============================================================
;; Evaluation
;; ============================================================

(defn- var-qualified-sym
  "Get the qualified heap key for a sci.lang.Var."
  [^sci.lang.Var v]
  (or (:sci.impl/var-sym (.-meta-map v))
      (.-sym v)))

;; ============================================================
;; make-machine-from-ctx helpers — extracted top-level functions
;; ============================================================

(defn- make-resolve-fn [ctx heap-atom]
  (fn sci-resolve
    ([sym]
     (let [ns-sym (if-let [a (:current-ns-atom ctx)] @a 'user)]
       (sci-resolve ns-sym sym)))
    ([ns-sym sym]
     (let [heap     @heap-atom
           ns-data  (if-let [a (:ns-atom ctx)]
                      (get @a ns-sym)
                      (get (:ns-table ctx) ns-sym))
           excludes (:refer-clojure-excludes ns-data)
           [qualified core-q]
           (if (qualified-symbol? sym)
             [sym nil]
             [(symbol (str ns-sym) (str sym))
              (when-not (and excludes (contains? excludes sym))
                (symbol "clojure.core" (str sym)))])
           entry    (or (get heap qualified) (when core-q (get heap core-q)))
           type-obj (when-not entry
                      (let [ns-d (if-let [a (:ns-atom ctx)]
                                   (get @a ns-sym)
                                   (get (:ns-table ctx) ns-sym))]
                        (get (:types ns-d) (if (qualified-symbol? sym)
                                             (symbol (name sym))
                                             sym))))]
       (cond
         entry
         (let [found-key (if (get heap qualified) qualified core-q)]
           (sci.lang/->Var (symbol (name found-key))
                           (:val entry)
                           (assoc (:meta entry)
                                  :name (symbol (name found-key))
                                  :ns (symbol (namespace found-key))
                                  :sci.impl/var-sym found-key)
                           (:dynamic? entry)))
         type-obj type-obj)))))

(defn- make-eval-fn [ctx heap-atom]
  (fn sci-eval [form]
    (let [ns-atom (:ns-atom ctx)
          ns-table (if ns-atom @ns-atom (:ns-table ctx))
          m2 (machine/make-machine {:heap        @heap-atom
                                    :ns-table    ns-table
                                    :permissions {:allow (:allow ctx)
                                                  :deny  (:deny ctx)}})
          m2 (cond-> (assoc m2 :heap-atom heap-atom :ctx ctx)
               ns-atom (assoc :ns-atom ns-atom)
               (:current-ns-atom ctx) (assoc :current-ns-atom (:current-ns-atom ctx)
                                             :current-ns @(:current-ns-atom ctx))
               (:load-fn ctx) (assoc :load-fn (:load-fn ctx))
               (:classes ctx) (assoc :classes (:classes ctx))
               (:hierarchy-atom ctx) (assoc :hierarchy-atom (:hierarchy-atom ctx)))
          m2 (machine/push-frame m2 {:op :eval :expr form})]
      (step/run m2))))

(defn- make-with-redefs-fn [heap-atom]
  (fn sci-with-redefs-fn [binding-map func]
    (let [sci-bindings (filter (fn [[v _]] (instance? sci.lang.Var v)) binding-map)
          clj-bindings (remove (fn [[v _]] (instance? sci.lang.Var v)) binding-map)
          old-vals     (into {} (map (fn [[v _]]
                                       (let [sym (var-qualified-sym v)]
                                         [sym (:val (get @heap-atom sym))]))
                                     sci-bindings))]
      (doseq [[v _] sci-bindings]
        (let [sym   (var-qualified-sym v)
              entry (get @heap-atom sym)]
          (when (:sci/built-in entry)
            (throw (ex-info (str "Built-in var " sym " cannot be redefined")
                            {:type :sci/error})))))
      (doseq [[v new-val] sci-bindings]
        (let [sym   (var-qualified-sym v)
              entry (assoc (get @heap-atom sym) :val new-val)]
          (swap! heap-atom assoc sym entry)))
      (try
        (if (seq clj-bindings)
          (with-redefs-fn (into {} clj-bindings) func)
          (func))
        (finally
          (doseq [[sym old-val] old-vals]
            (let [entry (assoc (get @heap-atom sym) :val old-val)]
              (swap! heap-atom assoc sym entry))))))))

(defn- make-alter-var-root-fn [heap-atom]
  (fn sci-alter-var-root [v f & args]
    (if (instance? sci.lang.Var v)
      (let [sym    (var-qualified-sym v)
            ns-str (when sym (namespace sym))]
        (when (and ns-str (contains? (set (map str host/default-namespaces)) ns-str))
          (throw (ex-info (str "Var " sym " is read-only") {:type :sci/error})))
        (let [result (atom nil)
              old-val-atom (atom nil)]
          (swap! heap-atom
                 (fn [h]
                   (let [entry   (get h sym)
                         old-val (:val entry)
                         new-val (apply f old-val args)]
                     (reset! result new-val)
                     (reset! old-val-atom old-val)
                     (assoc h sym (assoc entry :val new-val)))))
          ;; Notify watchers
          (let [watchers (:watchers (get @heap-atom sym))]
            (doseq [[k wf] watchers]
              (wf k v @old-val-atom @result)))
          @result))
      (apply clojure.core/alter-var-root v f args))))

(defn- make-alter-meta!-fn [heap-atom]
  (fn sci-alter-meta! [ref f & args]
    (if (instance? sci.lang.Var ref)
      (let [qualified (var-qualified-sym ref)
            ns-str    (when qualified (namespace qualified))]
        (when (and ns-str (contains? (set (map str host/default-namespaces)) ns-str))
          (throw (ex-info (str "Var " qualified " is read-only") {:type :sci/error})))
        (let [old-meta (.-meta-map ^sci.lang.Var ref)
              new-meta (apply f old-meta args)
              entry    (get @heap-atom qualified)]
          (swap! heap-atom assoc qualified (assoc entry :meta new-meta))
          new-meta))
      (apply clojure.core/alter-meta! ref f args))))

(defn- make-macroexpand-1-fn [heap-atom]
  (fn sci-macroexpand-1
    ([form]
     (if-not (and (seq? form) (symbol? (first form)))
       form
       (let [head (first form)
             n    (name head)]
         (cond
           (and #?(:clj  (.startsWith ^String n ".")
                   :cljs (= "." (subs n 0 1)))
                (not= n "..")
                (> (count n) 1))
           (let [method         (symbol (subs n 1))
                 [_ obj & args] form
                 ;; Wrap obj in (clojure.core/identity ...) only when it's a class symbol
                 ;; (uppercase initial letter), matching Clojure's macroexpand-1 behavior.
                 wrapped-obj #?(:clj (if (and (symbol? obj)
                                              (nil? (namespace obj))
                                              (let [s (name obj)]
                                                (Character/isUpperCase (.charAt s 0))))
                                       (list 'clojure.core/identity obj)
                                       obj)
                                :cljs obj)]
             (list* '. wrapped-obj method args))

           (and #?(:clj  (.endsWith ^String n ".")
                   :cljs (= "." (subs n (dec (count n)))))
                (not= n "..")
                (> (count n) 1))
           (let [class-name (symbol (subs n 0 (dec (count n))))]
             (list* 'new class-name (rest form)))

           :else
           (let [heap        @heap-atom
                 sym-ns      (clojure.core/namespace head)
                 candidates  (if sym-ns
                               [(symbol sym-ns n)]
                               [(symbol "user" n) (symbol "clojure.core" n)])
                 macro-entry (some #(let [e (get heap %)] (when (:macro? e) e)) candidates)]
             (if macro-entry
               (let [mv (:val macro-entry)
                     mf (if (var? mv) @mv mv)]
                 (if (or (var? mv) (:sci/closure (meta mf)) (:host-macro? macro-entry))
                   ;; Host macros (Clojure vars), SCI closures (defmacro), and
                   ;; internal host-style macros (defrecord/deftype) get &form &env
                   (apply mf form {} (rest form))
                   ;; Internal SCI functions (not closures): just args
                   (apply mf (rest form))))
               form))))))
    ([env form]
     (if (and (seq? form) (symbol? (first form)) (contains? env (first form)))
       form
       (sci-macroexpand-1 form)))))

(defn- make-ns-vars-fn
  "Returns a function that collects all vars for a given namespace from heap."
  [heap-atom]
  (fn [ns-sym]
    (let [heap   @heap-atom
          ns-str (str ns-sym)]
      (reduce-kv (fn [m k v]
                   (if (= ns-str (namespace k))
                     (let [var-meta (merge {:name (symbol (name k))
                                            :ns   (symbol (namespace k))}
                                           (:meta v)
                                           {:sci.impl/var-sym k})]
                       (assoc m (symbol (name k))
                              (sci.lang/->Var (symbol (name k)) (:val v) var-meta (:dynamic? v))))
                     m))
                 {} heap))))

(defn- make-ns-map-fn [heap-atom ctx]
  (fn [ns-sym]
    (let [heap   @heap-atom
          ns-str (str ns-sym)
          ;; Start with imports from the ns-table
          ns-data (when-let [a (:ns-atom ctx)] @a)
          imports (get-in ns-data [ns-sym :imports])]
      (reduce-kv (fn [m k v]
                   (let [k-ns (namespace k)]
                     (if (or (= ns-str k-ns) (= "clojure.core" k-ns))
                       (let [var-meta (merge {:name (symbol (name k))
                                              :ns   (symbol (namespace k))}
                                             (:meta v)
                                             {:sci.impl/var-sym k})]
                         (assoc m (symbol (name k))
                                (sci.lang/->Var (symbol (name k)) (:val v) var-meta (:dynamic? v))))
                       m)))
                 (or imports {}) heap))))

(defn- make-ns-refers-fn [heap-atom]
  (fn [ns-sym]
    (let [heap   @heap-atom
          ns-str (str ns-sym)]
      (reduce-kv (fn [m k v]
                   (let [k-ns   (namespace k)
                         k-name (name k)]
                     (if (and (not= ns-str k-ns)
                              (or (= "clojure.core" k-ns)
                                  (get heap (symbol ns-str k-name))))
                       (let [var-meta (merge {:name (symbol k-name) :ns (symbol k-ns)}
                                             (:meta v)
                                             {:sci.impl/var-sym k})]
                         (assoc m (symbol k-name)
                                (sci.lang/->Var (symbol k-name) (:val v) var-meta (:dynamic? v))))
                       m)))
                 {} heap))))

(defn- make-intern-fn [heap-atom]
  (fn sci-intern
    ([ns-sym name-sym]
     (let [qualified  (symbol (str ns-sym) (str name-sym))
           existing   (get @heap-atom qualified)
           name-meta  (meta name-sym)
           entry      (if existing
                        (update existing :meta merge name-meta)
                        {:val nil :meta (or name-meta {}) :dynamic? false :bound? false})]
       (swap! heap-atom assoc qualified entry)
       (sci.lang/->Var (symbol (str name-sym)) (:val entry)
                       (assoc (:meta entry) :name name-sym :ns ns-sym :sci.impl/var-sym qualified)
                       (:dynamic? entry))))
    ([ns-sym name-sym val]
     (let [qualified  (symbol (str ns-sym) (str name-sym))
           existing   (get @heap-atom qualified)
           name-meta  (meta name-sym)
           entry      (if existing
                        (-> existing (assoc :val val) (update :meta merge name-meta))
                        {:val val :meta (or name-meta {}) :dynamic? false})]
       (swap! heap-atom assoc qualified entry)
       (sci.lang/->Var (symbol (str name-sym)) val
                       (assoc (:meta entry) :name name-sym :ns ns-sym :sci.impl/var-sym qualified)
                       (:dynamic? entry))))))

(defn- get-or-create-ns-object
  "Return a stable namespace object for the given sym from the ns-objects cache."
  [ns-objects-atom sym]
  (or (get @ns-objects-atom sym)
      (let [obj (sci.lang/->Namespace sym {} {} {} {})]
        (swap! ns-objects-atom assoc sym obj)
        (get @ns-objects-atom sym))))

(defn- sci-namespace?
  "Duck-type check for sci.lang.Namespace records.
   Uses field presence instead of instance? to avoid classloader identity issues
   when the namespace is reloaded (e.g. :reload-all in tests)."
  [x]
  (and (map? x)
       (contains? x :name)
       (symbol? (:name x))
       (contains? x :aliases)))

(defn- ns-meta-from-info
  "Extract user-facing metadata from a ns-table entry (exclude structural keys)."
  [ns-info]
  (not-empty (dissoc ns-info :aliases :refers :imports :types :refer-clojure-excludes)))

(defn- make-find-ns-fn [ctx]
  (fn [sym]
    (let [ns-data (if-let [a (:ns-atom ctx)] @a (:ns-table ctx))
          ns-info (get ns-data sym)]
      (when ns-info
        (let [ns-objs (or (:ns-objects ctx) (atom {}))
              ns-obj (get-or-create-ns-object ns-objs sym)
              ns-meta (ns-meta-from-info ns-info)]
          ;; Update cached object's metadata and store back in cache
          ;; so that identical? works (ns-aliases reads from same cache)
          (if ns-meta
            (let [updated (with-meta ns-obj ns-meta)]
              (swap! ns-objs assoc sym updated)
              updated)
            ns-obj))))))

(defn- make-the-ns-fn [ctx]
  (fn [sym-or-ns]
    (let [sym (cond
                (sci-namespace? sym-or-ns) (:name sym-or-ns)
                (symbol? sym-or-ns) sym-or-ns
                :else (throw (ex-info (str "Not a namespace or symbol: " sym-or-ns) {:type :sci/error})))
          ns-data (if-let [a (:ns-atom ctx)] @a (:ns-table ctx))
          ns-info (get ns-data sym)]
      (if ns-info
        (let [ns-obj (get-or-create-ns-object (or (:ns-objects ctx) (atom {})) sym)
              ns-meta (ns-meta-from-info ns-info)]
          (if ns-meta
            (with-meta ns-obj ns-meta)
            ns-obj))
        (throw (ex-info (str "No namespace: " sym " found") {:type :sci/error}))))))

(defn- make-create-ns-fn [ctx]
  (fn [sym]
    (let [sym (if (string? sym) (symbol sym) sym)]
      (when-let [a (:ns-atom ctx)]
        (swap! a (fn [ns-table]
                   (if (get ns-table sym)
                     ns-table
                     (assoc ns-table sym {:aliases {} :refers {} :imports {}})))))
      (get-or-create-ns-object (or (:ns-objects ctx) (atom {})) sym))))

(defn- make-all-ns-fn [ctx]
  (fn []
    (let [ns-data (if-let [a (:ns-atom ctx)] @a (:ns-table ctx))]
      (keys ns-data))))

(defn- make-load-string-fn [ctx heap-atom]
  (fn sci-load-string [s]
    (let [forms (read-all s)
          expr  (if (= 1 (count forms)) (first forms) (cons 'do forms))
          eval-file (when (= 1 (count forms))
                      (get (meta (first forms)) :clojure.core/eval-file))
          m2    (cond-> (machine/make-machine {:heap        @heap-atom
                                               :ns-table    (:ns-table ctx)
                                               :permissions {:allow (:allow ctx)
                                                             :deny  (:deny ctx)}})
                  true       (assoc :heap-atom heap-atom)
                  eval-file  (assoc :current-file eval-file)
                  eval-file  (update :dynamic-bindings assoc 'clojure.core/*file* eval-file)
                  true       (machine/push-frame {:op :eval :expr expr}))]
      (step/run m2))))

(defn- make-find-var-fn [ctx heap-atom]
  (fn [sym]
    (when-not (qualified-symbol? sym)
      (throw (ex-info (str "Not a qualified symbol: " sym) {:type :sci/error})))
    (let [ns-sym  (symbol (namespace sym))
          ns-data (if-let [a (:ns-atom ctx)] @a (:ns-table ctx))]
      (when-not (get ns-data ns-sym)
        (throw (ex-info (str "No such namespace: " ns-sym) {:type :sci/error})))
      (let [entry (get @heap-atom sym)]
        (when entry
          (sci.lang/->Var (symbol (name sym)) (:val entry)
                          (assoc (:meta entry) :sci.impl/var-sym sym)
                          (:dynamic? entry)))))))

(defn- make-alias-fn [ctx]
  (fn [alias-sym ns-sym-or-obj]
    (let [ns-sym (if (sci-namespace? ns-sym-or-obj)
                   (:name ns-sym-or-obj)
                   ns-sym-or-obj)]
      ;; Verify the namespace exists
      (let [ns-data (if-let [a (:ns-atom ctx)] @a (:ns-table ctx))]
        (when-not (or (get ns-data ns-sym)
                      (contains? (set host/default-namespaces) ns-sym))
          (throw (ex-info (str "No namespace: " ns-sym " found") {:type :sci/error}))))
      (when-let [a (:ns-atom ctx)]
        (let [current-ns (if-let [cna (:current-ns-atom ctx)] @cna 'user)]
          (swap! a update-in [current-ns :aliases] assoc alias-sym ns-sym)))
      nil)))

(defn- make-ns-unalias-fn [ctx]
  (fn [ns-sym alias-sym]
    (let [ns-sym (if (symbol? ns-sym) ns-sym (clojure.core/ns-name ns-sym))]
      (when-let [a (:ns-atom ctx)]
        (swap! a update-in [ns-sym :aliases] dissoc alias-sym))
      nil)))

(defn- make-remove-ns-fn [ctx heap-atom]
  (fn [ns-sym]
    (when-let [a (:ns-atom ctx)]
      (swap! a dissoc ns-sym))
    (let [ns-str (str ns-sym)]
      (swap! heap-atom (fn [h]
                         (reduce-kv (fn [acc k v]
                                      (if (= ns-str (namespace k)) acc (assoc acc k v)))
                                    {} h))))
    nil))

(defn- make-refer-fn [ctx heap-atom]
  (fn sci-refer
    ([ns-sym] (sci-refer ns-sym :only nil))
    ([ns-sym & filters]
     (let [opts         (apply hash-map filters)
           only-syms    (:only opts)
           exclude-syms (set (:exclude opts))
           heap         @heap-atom
           ns-str       (str ns-sym)
           entries      (filter (fn [[k _]] (= ns-str (namespace k))) heap)
           current-ns   (if-let [a (:current-ns-atom ctx)] @a 'user)]
       (doseq [[k entry] entries]
         (let [sym-name (symbol (name k))]
           (when (and (or (nil? only-syms) (contains? (set only-syms) sym-name))
                      (not (contains? exclude-syms sym-name)))
             (let [entry' (update entry :meta #(assoc (or % {}) :sci.impl/var-sym k))]
               (swap! heap-atom assoc (symbol (str current-ns) (str sym-name)) entry')))))
       nil))))

(defn- sci-print-doc
  "Print documentation for a SCI var entry's metadata, compatible with
   clojure.repl/print-doc but using SCI-side symbol/string instead of Clojure namespace."
  [{:keys [ns name arglists macro doc special-form]}]
  (println "-------------------------")
  (println (str (when ns (str (clojure.core/name (clojure.core/symbol (str ns))) "/")) name))
  (when arglists (println (pr-str arglists)))
  (when macro (println "Macro"))
  (when special-form (println "Special Form"))
  (when doc (println " " doc))
  nil)

(defn- make-doc-fn [ctx heap-atom]
  (fn sci-doc [sym-name]
    (let [heap         @heap-atom
          sym-str      (str sym-name)
          candidates   (if (qualified-symbol? sym-name)
                         [sym-name]
                         [(symbol "user" sym-str) (symbol "clojure.core" sym-str)])
          entry        (some (fn [q] (when-let [e (get heap q)] [q e])) candidates)
          ns-data      (when-let [na (:ns-atom ctx)] (get @na sym-name))]
      (cond
        (and entry (not (:user-binding? (second entry))))
        (let [[qualified e] entry
              m (:meta e)
              doc-map (merge {:name (or (:name m) (symbol (name qualified)))
                               :ns (symbol (namespace qualified))}
                              (select-keys m [:arglists :macro :doc :special-form]))]
          (list 'do
                (list (list 'var 'sci.core/sci-print-doc)
                      (list 'quote doc-map))
                nil))
        ns-data
        (list 'do
              (list (list 'var 'sci.core/sci-print-doc)
                    (list 'quote {:name sym-name :doc (:doc ns-data)}))
              nil)
        :else nil))))

(defn- make-find-doc-fn [ctx heap-atom]
  (fn sci-find-doc [re-string-or-pattern]
    (let [re      (re-pattern re-string-or-pattern)
          heap    @heap-atom
          matches (->> heap
                       (filter (fn [[_ entry]]
                                 (let [m (:meta entry)]
                                   (and m (or (when-let [d (:doc m)] (re-find re d))
                                              (re-find re (str (:name m))))))))
                       (sort-by first))]
      (doseq [[qualified-sym entry] matches]
        (#'clojure.repl/print-doc (merge (dissoc (:meta entry) :ns) {:name qualified-sym})))
      (when-let [ns-data @(or (:ns-atom ctx) (atom {}))]
        (doseq [[ns-sym ns-info] (sort-by first ns-data)]
          (when-let [doc-str (:doc ns-info)]
            (when (re-find re doc-str)
              (#'clojure.repl/print-doc {:name ns-sym :doc doc-str}))))))))

(defn- make-defrecord-fn [ctx]
  ;; Called as a macro: (defrecord Name [fields] & specs)
  ;; When invoked via (apply #'defrecord &form &env name fields & specs),
  ;; the first two args are form/env and should be skipped.
  (fn [_form _env name-sym fields & specs]
    (let [ns-sym     (if-let [a (:current-ns-atom ctx)] @a 'user)
          qualified  (symbol (str ns-sym) (str name-sym))
          dotted     (symbol (str ns-sym "." name-sym))
          proto-syms (vec (keep #(when (symbol? %) %) specs))
          methods    (vec (keep #(when (seq? %) %) specs))]
      (list 'do
            (with-meta
              (apply list 'deftype* qualified dotted fields :implements proto-syms methods)
              {:sci.impl/record true})
            (list 'def (symbol (str "->" name-sym))
                  (list 'var (symbol (str ns-sym) (str "->" name-sym))))
            (list 'def (symbol (str "map->" name-sym))
                  (list 'var (symbol (str ns-sym) (str "map->" name-sym))))))))

(defn- make-deftype-fn [ctx]
  ;; Called as a macro: (deftype Name [fields] & specs)
  ;; When invoked via (apply #'deftype &form &env name fields & specs),
  ;; the first two args are form/env and should be skipped.
  (fn [_form _env name-sym fields & specs]
    (let [ns-sym     (if-let [a (:current-ns-atom ctx)] @a 'user)
          qualified  (symbol (str ns-sym) (str name-sym))
          dotted     (symbol (str ns-sym "." name-sym))
          proto-syms (vec (keep #(when (symbol? %) %) specs))
          methods    (vec (keep #(when (seq? %) %) specs))]
      (list 'do
            (apply list 'deftype* qualified dotted fields :implements proto-syms methods)
            (list 'def (symbol (str "->" name-sym))
                  (list 'var (symbol (str ns-sym) (str "->" name-sym))))))))

;; ============================================================

(defn- make-machine-from-ctx
  "Create a fresh machine from a context and a list of forms."
  [ctx forms]
  (let [heap-atom   (or (:heap-atom ctx) (atom (:heap ctx)))
        resolve-fn  (make-resolve-fn ctx heap-atom)
        eval-fn     (make-eval-fn ctx heap-atom)
        ns-vars-fn  (make-ns-vars-fn heap-atom)
        extra-heap  {(symbol "sci.core" "sci-print-doc")
                    {:val sci-print-doc :meta {:name 'sci-print-doc}}
                    (symbol "clojure.core" "symbol")
                    {:val (fn sci-symbol
                            ([name]
                             (if (instance? sci.lang.Var name)
                               (or (:sci.impl/var-sym (.-meta-map ^sci.lang.Var name))
                                   (.-sym ^sci.lang.Var name))
                               (clojure.core/symbol name)))
                            ([ns name]
                             (clojure.core/symbol ns name)))
                     :meta {:name 'symbol}}
                    (symbol "clojure.core" "var?")
                    {:val (fn sci-var? [x]
                            (or (var? x) (instance? sci.lang.Var x)))
                     :meta {:name 'var?}}
                    (symbol "clojure.core" "var-get")
                    {:val (fn sci-var-get [v]
                            (if (instance? sci.lang.Var v)
                              ;; Check dynamic bindings first, then heap
                              (let [sym (var-qualified-sym v)
                                    dyn step/current-dynamic-bindings]
                                (if (and dyn (contains? dyn sym))
                                  (get dyn sym)
                                  (let [entry (get @heap-atom sym)]
                                    (if entry (:val entry) (.-val ^sci.lang.Var v)))))
                              (var-get v)))
                     :meta {:name 'var-get :doc #?(:clj (:doc (meta #'clojure.core/var-get)) :cljs nil)}}
                    (symbol "clojure.core" "thread-bound?")
                    {:val (fn sci-thread-bound? [& vars]
                            (every? (fn [v]
                                      (if (instance? sci.lang.Var v)
                                        (let [sym (var-qualified-sym v)
                                              dyn step/current-dynamic-bindings]
                                          (and dyn (contains? dyn sym)))
                                        (clojure.core/thread-bound? v)))
                                    vars))
                     :meta {:name 'thread-bound?}}
                    (symbol "clojure.core" "var-set")
                    {:val (fn sci-var-set [v val]
                            (if (instance? sci.lang.Var v)
                              (let [sym (var-qualified-sym v)
                                    dyn step/current-dynamic-bindings]
                                (if (and dyn (contains? dyn sym))
                                  ;; Update dynamic binding
                                  (do (set! step/current-dynamic-bindings (assoc dyn sym val))
                                      val)
                                  ;; Update heap
                                  (let [entry (assoc (get @heap-atom sym) :val val)]
                                    (swap! heap-atom assoc sym entry)
                                    val)))
                              (var-set v val)))
                     :meta {:name 'var-set :doc #?(:clj (:doc (meta #'clojure.core/var-set)) :cljs nil)}}
                    (symbol "clojure.core" "add-watch")
                    {:val (fn sci-add-watch [ref key callback]
                            (if (instance? sci.lang.Var ref)
                              (let [sym (var-qualified-sym ref)]
                                (swap! heap-atom update-in [sym :watchers] assoc key callback)
                                ref)
                              (clojure.core/add-watch ref key callback)))
                     :meta {:name 'add-watch}}
                    (symbol "clojure.core" "remove-watch")
                    {:val (fn sci-remove-watch [ref key]
                            (if (instance? sci.lang.Var ref)
                              (let [sym (var-qualified-sym ref)]
                                (swap! heap-atom update-in [sym :watchers] dissoc key)
                                ref)
                              (clojure.core/remove-watch ref key)))
                     :meta {:name 'remove-watch}}
                    (symbol "clojure.core" "with-redefs-fn")
                    {:val (make-with-redefs-fn heap-atom) :meta {:name 'with-redefs-fn}}
                    (symbol "clojure.core" "alter-var-root")
                    {:val (make-alter-var-root-fn heap-atom) :meta {:name 'alter-var-root}}
                    (symbol "clojure.core" "meta")
                    {:val (fn sci-meta [obj]
                            (let [m (clojure.core/meta obj)]
                              (cond
                                ;; SCI closures: user-visible meta is stored in :user-meta key
                                (:sci/closure m) (:user-meta m)
                                ;; SCI Vars: strip internal :sci.impl/var-sym key
                                (:sci.impl/var-sym m) (dissoc m :sci.impl/var-sym)
                                :else m)))
                     :meta {:name 'meta}}
                    ;; with-meta and vary-meta are overridden later in the heap build
                    ;; to handle both closures and SCI type metadata preservation
                    (symbol "clojure.core" "alter-meta!")
                    {:val (make-alter-meta!-fn heap-atom) :meta {:name 'alter-meta!}}
                    (symbol "clojure.core" "reset-meta!")
                    {:val (fn sci-reset-meta! [ref m]
                            (if (instance? sci.lang.Var ref)
                              (let [sym (var-qualified-sym ref)
                                    entry (get @heap-atom sym)]
                                (swap! heap-atom assoc sym (assoc entry :meta m))
                                m)
                              (clojure.core/reset-meta! ref m)))
                     :meta {:name 'reset-meta!}}
                    (symbol "clojure.core" "resolve")
                    {:val resolve-fn :meta {:name 'resolve}}
                    (symbol "clojure.core" "ns-resolve")
                    {:val (fn [ns-sym sym] (resolve-fn ns-sym sym)) :meta {:name 'ns-resolve}}
                    (symbol "clojure.core" "eval")
                    {:val eval-fn :meta {:name 'eval :doc #?(:clj (:doc (meta #'clojure.core/eval)) :cljs nil)}}
                    (symbol "clojure.core" "macroexpand-1")
                    {:val (make-macroexpand-1-fn heap-atom) :meta {:name 'macroexpand-1}}
                    (symbol "clojure.core" "macroexpand")
                    {:val (fn sci-macroexpand [form]
                            (let [me1-fn (:val (get @heap-atom (symbol "clojure.core" "macroexpand-1")))]
                              (loop [f form]
                                (let [expanded (me1-fn f)]
                                  (if (= expanded f) f (recur expanded))))))
                     :meta {:name 'macroexpand :doc #?(:clj (:doc (meta #'clojure.core/macroexpand)) :cljs nil)}}
                    (symbol "clojure.core" "bound?")
                    {:val (fn [& vars]
                            (every? (fn [v]
                                      (if (instance? sci.lang.Var v)
                                        (let [sym   (var-qualified-sym v)
                                              entry (get @heap-atom sym)
                                              dyn   step/current-dynamic-bindings]
                                          (or (:bound? entry)
                                              (and dyn (contains? dyn sym))
                                              (some? (.-val ^sci.lang.Var v))))
                                        (clojure.core/bound? v)))
                                    vars))
                     :meta {:name 'bound?}}
                    (symbol "clojure.core" "intern")
                    {:val (make-intern-fn heap-atom) :meta {:name 'intern}}
                    (symbol "clojure.core" "find-ns")
                    {:val (make-find-ns-fn ctx) :meta {:name 'find-ns :doc #?(:clj (:doc (meta #'clojure.core/find-ns)) :cljs nil)}}
                    (symbol "clojure.core" "create-ns")
                    {:val (make-create-ns-fn ctx) :meta {:name 'create-ns}}
                    (symbol "clojure.core" "the-ns")
                    {:val (make-the-ns-fn ctx) :meta {:name 'the-ns}}
                    (symbol "clojure.core" "ns-name")
                    {:val (fn [ns-sym]
                            (cond
                              (sci-namespace? ns-sym) (:name ns-sym)
                              (symbol? ns-sym) ns-sym
                              (string? ns-sym) (symbol ns-sym)
                              :else (clojure.core/ns-name ns-sym)))
                     :meta {:name 'ns-name}}
                    (symbol "clojure.core" "all-ns")
                    {:val (make-all-ns-fn ctx) :meta {:name 'all-ns}}
                    (symbol "clojure.core" "ns-publics")
                    {:val ns-vars-fn :meta {:name 'ns-publics :doc #?(:clj (:doc (meta #'clojure.core/ns-publics)) :cljs nil)}}
                    (symbol "clojure.core" "ns-interns")
                    {:val ns-vars-fn :meta {:name 'ns-interns}}
                    (symbol "clojure.core" "*clojure-version*")
                    {:val {:major (:major *clojure-version*)
                           :minor (:minor *clojure-version*)
                           :incremental (:incremental *clojure-version*)
                           :qualifier "SCI"}
                     :meta {:name '*clojure-version*}
                     :dynamic? true}
                    (symbol "clojure.core" "clojure-version")
                    {:val (fn [] (clojure.core/str (:major *clojure-version*) "."
                                      (:minor *clojure-version*) "."
                                      (:incremental *clojure-version*) "-SCI"))
                     :meta {:name 'clojure-version}}
                    (symbol "clojure.core" "ns-map")
                    {:val (make-ns-map-fn heap-atom ctx) :meta {:name 'ns-map}}
                    (symbol "clojure.core" "ns-refers")
                    {:val (make-ns-refers-fn heap-atom) :meta {:name 'ns-refers}}
                    (symbol "clojure.core" "with-in-str")
                    {:val (fn sci-with-in-str [s & body]
                            (list 'let ['s__in (list 'new 'clojure.lang.LineNumberingPushbackReader
                                                     (list 'new 'java.io.StringReader s))]
                                  (list* 'binding ['*in* 's__in] body)))
                     :meta {:macro true :name 'with-in-str}
                     :macro? true}
                    (symbol "clojure.core" "alias")
                    {:val (make-alias-fn ctx) :meta {:name 'alias}}
                    (symbol "clojure.core" "ns-unalias")
                    {:val (make-ns-unalias-fn ctx) :meta {:name 'ns-unalias :doc #?(:clj (:doc (meta #'clojure.core/ns-unalias)) :cljs nil)}}
                    (symbol "clojure.core" "ns-unmap")
                    {:val (fn [ns-sym sym]
                            (let [qualified (symbol (str ns-sym) (str sym))]
                              (swap! heap-atom dissoc qualified)
                              nil))
                     :meta {:name 'ns-unmap :doc #?(:clj (:doc (meta #'clojure.core/ns-unmap)) :cljs nil)}}
                    (symbol "clojure.core" "ns-imports")
                    {:val (fn [ns-sym-or-obj]
                            (let [ns-sym (if (symbol? ns-sym-or-obj)
                                           ns-sym-or-obj
                                           (if (and (instance? clojure.lang.Named ns-sym-or-obj))
                                             (symbol (name ns-sym-or-obj))
                                             ns-sym-or-obj))
                                  ns-a (:ns-atom ctx)
                                  ns-table (if ns-a @ns-a {})]
                              (get-in ns-table [ns-sym :imports] {})))
                     :meta {:name 'ns-imports :doc #?(:clj (:doc (meta #'clojure.core/ns-imports)) :cljs nil)}}
                    (symbol "clojure.core" "remove-ns")
                    {:val (make-remove-ns-fn ctx heap-atom) :meta {:name 'remove-ns :doc #?(:clj (:doc (meta #'clojure.core/remove-ns)) :cljs nil)}}
                    (symbol "clojure.core" "find-var")
                    {:val (make-find-var-fn ctx heap-atom) :meta {:name 'find-var :doc #?(:clj (:doc (meta #'clojure.core/find-var)) :cljs nil)}}
                    (symbol "clojure.core" "refer")
                    {:val (make-refer-fn ctx heap-atom) :meta {:name 'refer :doc #?(:clj (:doc (meta #'clojure.core/refer)) :cljs nil)}}
                    (symbol "clojure.core" "ns-aliases")
                    {:val (fn [ns-sym-or-obj]
                            (let [ns-sym (if (sci-namespace? ns-sym-or-obj)
                                           (:name ns-sym-or-obj)
                                           ns-sym-or-obj)
                                  ns-data (if-let [a (:ns-atom ctx)]
                                            (get @a ns-sym)
                                            (get (:ns-table ctx) ns-sym))
                                  aliases (or (:aliases ns-data) {})
                                  ns-objs (or (:ns-objects ctx) (atom {}))]
                              ;; Return namespace objects as values (for identical? support)
                              (reduce-kv (fn [m k v]
                                           (assoc m k (get-or-create-ns-object ns-objs v)))
                                         {} aliases)))
                     :meta {:name 'ns-aliases}}
                    (symbol "clojure.core" "require")
                    {:val (fn sci-require [& specs]
                            (let [eval-f (fn [form]
                                           (let [ns-atom (:ns-atom ctx)
                                                 ns-table (if ns-atom @ns-atom (:ns-table ctx))
                                                 m2 (machine/make-machine
                                                     {:heap @heap-atom
                                                      :ns-table ns-table
                                                      :permissions {:allow (:allow ctx)
                                                                    :deny  (:deny ctx)}})
                                                 m2 (cond-> (assoc m2 :heap-atom heap-atom :ctx ctx)
                                                      ns-atom (assoc :ns-atom ns-atom)
                                                      (:current-ns-atom ctx)
                                                      (assoc :current-ns-atom (:current-ns-atom ctx)
                                                             :current-ns @(:current-ns-atom ctx))
                                                      (:load-fn ctx) (assoc :load-fn (:load-fn ctx)))
                                                 m2 (machine/push-frame m2 {:op :eval :expr form})]
                                             (step/run m2)))]
                              ;; Build require form from function args and evaluate via the VM
                              (eval-f (cons 'require (map (fn [s] (list 'quote s)) specs)))
                              nil))
                     :meta {:name 'require :doc #?(:clj (:doc (meta #'clojure.core/require)) :cljs nil)}}
                    (symbol "clojure.core" "use")
                    {:val (fn sci-use [& specs]
                            (let [eval-f (fn [form]
                                           (let [ns-atom (:ns-atom ctx)
                                                 ns-table (if ns-atom @ns-atom (:ns-table ctx))
                                                 m2 (machine/make-machine
                                                     {:heap @heap-atom
                                                      :ns-table ns-table
                                                      :permissions {:allow (:allow ctx)
                                                                    :deny  (:deny ctx)}})
                                                 m2 (cond-> (assoc m2 :heap-atom heap-atom :ctx ctx)
                                                      ns-atom (assoc :ns-atom ns-atom)
                                                      (:current-ns-atom ctx)
                                                      (assoc :current-ns-atom (:current-ns-atom ctx)
                                                             :current-ns @(:current-ns-atom ctx))
                                                      (:load-fn ctx) (assoc :load-fn (:load-fn ctx)))
                                                 m2 (machine/push-frame m2 {:op :eval :expr form})]
                                             (step/run m2)))]
                              (doseq [spec specs]
                                (let [spec (if (and (seq? spec) (= 'quote (first spec)))
                                             (second spec)
                                             spec)
                                      [ns-sym opts] (if (sequential? spec)
                                                      [(first spec) (apply hash-map (rest spec))]
                                                      [spec {}])
                                      only-syms (:only opts)
                                      exclude-syms (set (:exclude opts))]
                                  ;; Load the namespace via eval (uses SCI's require mechanism)
                                  (eval-f (list 'require (list 'quote ns-sym)))
                                  ;; Refer all public vars (or :only) to current ns
                                  (let [current-ns (if-let [a (:current-ns-atom ctx)] @a 'user)
                                        heap @heap-atom
                                        ns-str (str ns-sym)]
                                    (doseq [[k entry] heap
                                            :when (= ns-str (namespace k))
                                            :let [sym-name (symbol (name k))]
                                            :when (and (or (nil? only-syms)
                                                           (contains? (set only-syms) sym-name))
                                                       (not (contains? exclude-syms sym-name)))]
                                      (let [entry' (update entry :meta
                                                           #(assoc (or % {}) :sci.impl/var-sym k))]
                                        (swap! heap-atom assoc
                                               (symbol (str current-ns) (str sym-name)) entry'))))))
                              nil))
                     :meta {:name 'use}}
                    (symbol "clojure.core" "requiring-resolve")
                    {:val (fn sci-requiring-resolve [sym]
                            (when-not (qualified-symbol? sym)
                              (throw (ex-info (str "Not a qualified symbol: " sym) {:type :sci/error})))
                            (let [ns-sym (symbol (namespace sym))
                                  eval-f (fn [form]
                                           (let [ns-atom (:ns-atom ctx)
                                                 ns-table (if ns-atom @ns-atom (:ns-table ctx))
                                                 m2 (machine/make-machine
                                                     {:heap @heap-atom
                                                      :ns-table ns-table
                                                      :permissions {:allow (:allow ctx)
                                                                    :deny  (:deny ctx)}})
                                                 m2 (cond-> (assoc m2 :heap-atom heap-atom :ctx ctx)
                                                      ns-atom (assoc :ns-atom ns-atom)
                                                      (:current-ns-atom ctx)
                                                      (assoc :current-ns-atom (:current-ns-atom ctx)
                                                             :current-ns @(:current-ns-atom ctx))
                                                      (:load-fn ctx) (assoc :load-fn (:load-fn ctx)))
                                                 m2 (machine/push-frame m2 {:op :eval :expr form})]
                                             (step/run m2)))]
                              ;; Load the namespace
                              (eval-f (list 'require (list 'quote ns-sym)))
                              ;; Resolve the var
                              (let [heap @heap-atom
                                    entry (get heap sym)]
                                (when entry
                                  (sci.lang/->Var (symbol (name sym)) (:val entry)
                                                  (assoc (:meta entry) :sci.impl/var-sym sym)
                                                  (:dynamic? entry))))))
                     :meta {:name 'requiring-resolve}}
                    (symbol "clojure.core" "loaded-libs")
                    {:val (fn [] @(:loaded-libs ctx))
                     :meta {:name 'loaded-libs :doc "Returns a sorted set of symbols naming the currently loaded libs"}}
                    (symbol "clojure.core" "*loaded-libs*")
                    {:val (:loaded-libs ctx)
                     :meta {:name '*loaded-libs* :doc "A ref to a sorted set of symbols naming loaded libs"}
                     :dynamic? true}
                    (symbol "clojure.core" "defonce")
                    {:val (fn sci-defonce [name expr]
                            (list 'do
                                  (list 'when-not (list 'resolve (list 'quote name))
                                        (list 'def name expr))
                                  (list 'var name)))
                     :meta {:macro true :name 'defonce}
                     :macro? true}
                    (symbol "clojure.repl" "doc")
                    {:val (make-doc-fn ctx heap-atom)
                     :meta {:macro true :name 'doc
                            :doc "Prints documentation for a var or special form given its name,\n   or for a spec if given a keyword"}
                     :macro? true}
                    (symbol "clojure.repl" "find-doc")
                    {:val (make-find-doc-fn ctx heap-atom)
                     :meta {:name 'find-doc
                            :doc "Prints documentation for any var whose documentation or name\n contains a match for re-string-or-pattern"}}
                    (symbol "clojure.repl" "source-fn")
                    {:val (fn [_] nil) :meta {:name 'source-fn}}
                    (symbol "clojure.core" "load-string")
                    {:val (make-load-string-fn ctx heap-atom) :meta {:name 'load-string}}
                    (symbol "clojure.core" "read-string")
                    {:val (fn sci-read-string
                            ([s]
                             (let [suppress? *suppress-read*
                                   re-val    (or *read-eval* @read-eval)
                                   default-fn *default-data-reader-fn*
                                   resolver  *reader-resolver*
                                   opts (cond-> (assoc (make-reader-opts) :location? (constantly false))
                                          suppress? (assoc :suppress-read true)
                                          re-val    (assoc :read-eval clojure.core/eval)
                                          default-fn (assoc :readers
                                                        #?(:clj (fn [tag]
                                                                   (or (get clojure.core/default-data-readers tag)
                                                                       (fn [val] (default-fn tag val))))
                                                           :cljs nil))
                                          resolver  (assoc :auto-resolve
                                                       #?(:clj (fn [alias]
                                                                  (if (= alias :current)
                                                                    (.currentNS ^clojure.lang.LispReader$Resolver resolver)
                                                                    (.resolveAlias ^clojure.lang.LispReader$Resolver resolver alias)))
                                                          :cljs nil)))]
                               (edamame/parse-string s opts)))
                            ([opts s]
                             (let [eof-val   (:eof opts ::none)
                                   suppress? *suppress-read*
                                   re-val    (or *read-eval* @read-eval)
                                   default-fn *default-data-reader-fn*
                                   resolver  *reader-resolver*
                                   reader-opts (cond-> (merge (assoc (make-reader-opts) :location? (constantly false))
                                                              (dissoc opts :eof))
                                                 suppress? (assoc :suppress-read true)
                                                 re-val    (assoc :read-eval clojure.core/eval)
                                                 default-fn (assoc :readers
                                                               #?(:clj (fn [tag]
                                                                          (or (get clojure.core/default-data-readers tag)
                                                                              (fn [val] (default-fn tag val))))
                                                                  :cljs nil))
                                                 resolver  (assoc :auto-resolve
                                                              #?(:clj (fn [alias]
                                                                         (if (= alias :current)
                                                                           (.currentNS ^clojure.lang.LispReader$Resolver resolver)
                                                                           (.resolveAlias ^clojure.lang.LispReader$Resolver resolver alias)))
                                                                 :cljs nil)))
                                   result (try
                                            (edamame/parse-string s reader-opts)
                                            (catch Exception e
                                              (if (and (not= eof-val ::none)
                                                       (re-find #"EOF" (str (ex-message e))))
                                                eof-val
                                                (throw e))))]
                               (if (and (nil? result)
                                        (not= eof-val ::none)
                                        (clojure.string/blank? s))
                                 eof-val
                                 result))))
                     :meta {:name 'read-string}}
                    #?@(:clj
                        [(symbol "clojure.core" "read")
                         {:val (fn sci-read
                                 ([]
                                  (let [re-val (or *read-eval* @read-eval)
                                        do-read (fn [] (if (and re-val (not *read-eval*))
                                                         (clojure.core/binding [clojure.core/*read-eval* true]
                                                           (clojure.core/read *in*))
                                                         (clojure.core/read *in*)))]
                                    (try (do-read)
                                         (catch clojure.lang.LispReader$ReaderException e
                                           (throw (or (.getCause ^Throwable e) e))))))
                                 ([stream]
                                  (let [re-val (or *read-eval* @read-eval)
                                        do-read (fn [] (if (and re-val (not *read-eval*))
                                                         (clojure.core/binding [clojure.core/*read-eval* true]
                                                           (clojure.core/read stream))
                                                         (clojure.core/read stream)))]
                                    (try (do-read)
                                         (catch clojure.lang.LispReader$ReaderException e
                                           (throw (or (.getCause ^Throwable e) e))))))
                                 ([stream eof-error? eof-value]
                                  (let [re-val (or *read-eval* @read-eval)
                                        do-read (fn [] (if (and re-val (not *read-eval*))
                                                         (clojure.core/binding [clojure.core/*read-eval* true]
                                                           (clojure.core/read stream eof-error? eof-value))
                                                         (clojure.core/read stream eof-error? eof-value)))]
                                    (try (do-read)
                                         (catch clojure.lang.LispReader$ReaderException e
                                           (throw (or (.getCause ^Throwable e) e))))))
                                 ([opts stream]
                                  ;; Normalize :features from vector/seq to set (Clojure requires a set)
                                  (let [opts (cond-> opts
                                               (:features opts) (update :features (fn [f] (if (set? f) f (set f)))))
                                        re-val (or *read-eval* @read-eval)
                                        do-read (fn [] (if (and re-val (not *read-eval*))
                                                         (clojure.core/binding [clojure.core/*read-eval* true]
                                                           (clojure.core/read opts stream))
                                                         (clojure.core/read opts stream)))]
                                    (try (do-read)
                                         (catch clojure.lang.LispReader$ReaderException e
                                           (throw (or (.getCause ^Throwable e) e)))))))
                          :meta {:name 'read}}])}
        ns-atom (or (:ns-atom ctx) (atom (:ns-table ctx)))
        ;; Override ns-aliases to read from ns-atom
        heap (assoc (merge @heap-atom extra-heap)
                    (symbol "clojure.core" "ns-aliases")
                    {:val (fn [ns-sym-or-obj]
                            (let [ns-sym (if (sci-namespace? ns-sym-or-obj)
                                           (:name ns-sym-or-obj)
                                           ns-sym-or-obj)
                                  aliases (or (:aliases (get @ns-atom ns-sym)) {})
                                  ns-objs (or (:ns-objects ctx) (atom {}))]
                              (reduce-kv (fn [m k v]
                                           (assoc m k (get-or-create-ns-object ns-objs v)))
                                         {} aliases)))
                     :meta {:name 'ns-aliases}}
                    (symbol "clojure.core" "defrecord")
                    {:val (make-defrecord-fn ctx)
                     :meta {:macro true :name 'defrecord}
                     :macro? true
                     :host-macro? true}
                    (symbol "clojure.core" "deftype")
                    {:val (make-deftype-fn ctx)
                     :meta {:macro true :name 'deftype}
                     :macro? true
                     :host-macro? true}
                    ;; instance? — check SCI types too
                    (symbol "clojure.core" "instance?")
                    {:val (fn [cls obj]
                            (cond
                              (instance? sci.lang.Type cls)
                              ;; SCI type — check :type metadata
                              (= cls (:type (clojure.core/meta obj)))
                              ;; SCI protocol — check if protocol is satisfied
                              (and (map? cls) (= :sci/protocol (:type cls)))
                              (let [type-obj (or (:type (clojure.core/meta obj)) (clojure.core/type obj))
                                    impls @(:impls cls)]
                                (boolean (get impls type-obj)))
                              :else
                              ;; Host class — check real instance first, then SCI type interfaces
                              (boolean
                               (or (clojure.core/instance? cls obj)
                                   #?(:clj (when-let [type-obj (:type (clojure.core/meta obj))]
                                             (when (instance? sci.lang.Type type-obj)
                                               (contains? (:interfaces (.-opts ^sci.lang.Type type-obj)) cls)))
                                      :cljs false)))))
                     :meta {:name 'instance?}}
                    ;; type — check SCI type metadata
                    (symbol "clojure.core" "type")
                    {:val (fn [x]
                            (or (:type (clojure.core/meta x))
                                (clojure.core/type x)))
                     :meta {:name 'type}}
                    ;; record? — check SCI record flag
                    (symbol "clojure.core" "record?")
                    {:val (fn [x]
                            (or (:sci.impl/record (clojure.core/meta x))
                                (clojure.core/record? x)))
                     :meta {:name 'record?}}
                    ;; str — dispatch toString for SCI type instances
                    (symbol "clojure.core" "str")
                    {:val (fn [& args]
                            (if (empty? args)
                              ""
                              (clojure.string/join
                                (map (fn [x]
                                       (if (nil? x) ""
                                         (if-let [sci-type (:type (clojure.core/meta x))]
                                           (let [methods (.-methods ^sci.lang.Type sci-type)]
                                             (if-let [toString-fn (get methods 'toString)]
                                               (toString-fn x)
                                               (clojure.core/str "#object[" (.-name ^sci.lang.Type sci-type) "]")))
                                           (clojure.core/str x))))
                                     args))))
                     :meta {:name 'str}}
                    ;; with-meta — preserve :type and :sci.impl/record unless user explicitly sets them
                    (symbol "clojure.core" "with-meta")
                    {:val (fn [obj m]
                            (let [old-meta (clojure.core/meta obj)]
                              (if (and (fn? obj) old-meta (:sci/closure old-meta))
                                ;; SCI closure: update :user-meta, keep internal closure info intact
                                (clojure.core/with-meta obj (assoc old-meta :user-meta m))
                                ;; Only preserve impl keys that user didn't explicitly provide
                                (let [preserved (cond-> {}
                                                  (and (contains? old-meta :type)
                                                       (not (contains? m :type)))
                                                  (assoc :type (:type old-meta))
                                                  (and (contains? old-meta :sci.impl/record)
                                                       (not (contains? m :sci.impl/record)))
                                                  (assoc :sci.impl/record (:sci.impl/record old-meta)))]
                                  (clojure.core/with-meta obj (merge m preserved))))))
                     :meta {:name 'with-meta :doc #?(:clj (:doc (meta #'clojure.core/with-meta)) :cljs nil)}}
                    (symbol "clojure.core" "vary-meta")
                    {:val (fn [obj f & args]
                            (let [old-meta (clojure.core/meta obj)]
                              (if (and (fn? obj) old-meta (:sci/closure old-meta))
                                ;; SCI closure: apply f to :user-meta only
                                (let [new-user-meta (apply f (:user-meta old-meta) args)]
                                  (clojure.core/with-meta obj (assoc old-meta :user-meta new-user-meta)))
                                ;; Only preserve impl keys that the fn didn't explicitly set
                                (let [new-meta (apply f old-meta args)
                                      preserved (cond-> {}
                                                  (and (contains? old-meta :type)
                                                       (not (contains? new-meta :type)))
                                                  (assoc :type (:type old-meta))
                                                  (and (contains? old-meta :sci.impl/record)
                                                       (not (contains? new-meta :sci.impl/record)))
                                                  (assoc :sci.impl/record (:sci.impl/record old-meta)))]
                                  (clojure.core/with-meta obj (merge new-meta preserved))))))
                     :meta {:name 'vary-meta :doc #?(:clj (:doc (meta #'clojure.core/vary-meta)) :cljs nil)}}
                    ;; meta — hide :type and :sci.impl/record implementation keys from user code
                    (symbol "clojure.core" "meta")
                    {:val (fn [obj]
                            (let [m (clojure.core/meta obj)]
                              (cond
                                ;; SCI closure — return :user-meta if present, else strip impl keys
                                (:sci/closure m)
                                (or (:user-meta m)
                                    (let [cleaned (dissoc m :sci/closure :type :sci.impl/record
                                                          :ns :env :arities :file :name :line :column
                                                          :sci.impl/var-sym :user-meta)]
                                      (when (seq cleaned) cleaned)))
                                ;; SCI type/record — strip type identity keys
                                (and m (or (contains? m :type) (contains? m :sci.impl/record)))
                                (let [cleaned (dissoc m :type :sci.impl/record :sci.impl/var-sym)]
                                  (when (seq cleaned) cleaned))
                                ;; Any map with :sci.impl/var-sym — strip it
                                (contains? m :sci.impl/var-sym)
                                (let [cleaned (dissoc m :sci.impl/var-sym)]
                                  (when (seq cleaned) cleaned))
                                :else m)))
                     :meta {:name 'meta :doc #?(:clj (:doc (meta #'clojure.core/meta)) :cljs nil)}}
                    ;; class? — true for SCI types too
                    (symbol "clojure.core" "class?")
                    {:val (fn [x]
                            (or (clojure.core/class? x)
                                (instance? sci.lang.Type x)))
                     :meta {:name 'class?}}
                    ;; extends? — check SCI protocol impls for SCI types
                    (symbol "clojure.core" "extends?")
                    {:val (fn [protocol atype]
                            (if (and (map? protocol) (= :sci/protocol (:type protocol)))
                              ;; SCI protocol — check impls atom
                              (contains? @(:impls protocol) atype)
                              ;; Real protocol — atype must be a Class
                              (if (clojure.core/class? atype)
                                (clojure.core/extends? protocol atype)
                                false)))
                     :meta {:name 'extends? :doc #?(:clj (:doc (meta #'clojure.core/extends?)) :cljs nil)}})
        ;; Override pmap to capture SCI dynamic bindings at call time.
        ;; pmap is lazy — futures may be created after the binding form exits, so we must
        ;; snapshot current-dynamic-bindings when pmap is called and restore it in each thread.
        heap #?(:clj (assoc heap
                            (symbol "clojure.core" "pmap")
                            {:val (fn sci-pmap [f & colls]
                                    (let [dyn-bindings step/current-dynamic-bindings]
                                      (apply clojure.core/pmap
                                             (fn [& args]
                                               (clojure.core/binding [step/current-dynamic-bindings dyn-bindings]
                                                 (apply f args)))
                                             colls)))
                             :meta {:name 'pmap}})
                 :cljs heap)
        m (machine/make-machine
           {:heap heap
            :ns-table @ns-atom
            :permissions {:allow (:allow ctx)
                          :deny (:deny ctx)
                          :disable-arity-checks (:disable-arity-checks ctx)}})]
    (let [expr (if (= 1 (count forms))
                 (first forms)
                 (cons 'do forms))
          current-ns-atom (or (:current-ns-atom ctx) (atom 'user))
          m (cond-> (assoc m :heap-atom heap-atom :ns-atom ns-atom
                             :current-ns-atom current-ns-atom
                             :current-ns @current-ns-atom
                             :ctx ctx)
                (:load-fn ctx) (assoc :load-fn (:load-fn ctx))
                (:ns-aliases ctx) (assoc :ns-aliases (:ns-aliases ctx))
                (:classes ctx) (assoc :classes (:classes ctx))
                (:inverse-registry ctx) (assoc :inverse-registry (:inverse-registry ctx))
                (:hierarchy-atom ctx) (assoc :hierarchy-atom (:hierarchy-atom ctx))
                true (as-> m' m'
                      (let [f (or (:file ctx) @(clojure.core/resolve 'sci.core/file))]
                        (if f (assoc m' :current-file f) m'))))]
      (reset! heap-atom heap)
      (machine/push-frame m {:op :eval :expr expr}))))

(defn eval-string
  "Evaluate a string of Clojure code."
  ([s] (eval-string s nil))
  ([s opts]
   (let [;; When sci/ns atom has been bound to a symbol (via sci/binding), use it
         ;; as the initial namespace for the context.
         ;; sci.core/ns is a var holding an atom — double deref: var→atom→value.
         ;; Use find-var for runtime lookup to avoid compile-time "No such var: sci.core/ns"
         ;; (sci.core/ns is defined later in this file)
         sci-ns-val (some-> (clojure.core/find-var 'sci.core/ns) deref deref)
         initial-ns (when (symbol? sci-ns-val) sci-ns-val)
         ctx (if (and opts (:heap opts))
               opts  ;; already initialized
               (init (cond-> (or opts {})
                       initial-ns (assoc :initial-ns initial-ns))))
         current-ns-atom (or (:current-ns-atom ctx) (atom 'user))
         reader-extra (cond-> {}
                        (:features ctx) (assoc :features (:features ctx))
                        (:readers ctx) (assoc :readers (:readers ctx)))
         ;; Parse forms one at a time, evaluating between reads
         ;; so that (ns ...) affects ::keyword resolution
         reader (edamame/reader s)
         eof (Object.)]
     (loop [result nil]
       (let [current-ns @current-ns-atom
             ;; Get current namespace aliases for ::alias/keyword resolution
             ns-atom (or (:ns-atom ctx) (atom {}))
             ns-info (get @ns-atom current-ns)
             aliases (:aliases ns-info)
             read-opts (merge (make-reader-opts current-ns aliases (:heap-atom ctx) ns-atom) reader-extra {:eof eof})
             form (edamame/parse-next reader read-opts)]
         (if (identical? form eof)
           (if (and (map? result) (contains? #{:suspend :effect} (:status result)))
             result  ;; Return suspended machine as-is
             result)
           (let [eval-file (get (meta form) :clojure.core/eval-file)
                 machine (make-machine-from-ctx ctx [form])
                 machine (if eval-file
                           (-> machine
                               (assoc :current-file eval-file)
                               (update :dynamic-bindings assoc 'clojure.core/*file* eval-file))
                           machine)
                 res (step/run machine)]
             (recur res))))))))

(defn eval-string*
  "Same as eval-string but takes an already-initialized context.
   Context is first arg (unlike eval-string where string is first)."
  [ctx s]
  (eval-string s ctx))

(defn eval-form
  "Evaluate a single form."
  ([ctx form]
   (let [machine (make-machine-from-ctx ctx [form])]
     (step/run machine))))

;; ============================================================
;; Reader API
;; ============================================================

(defn reader
  "Create a reader from a string."
  [s]
  ;; Use edamame's reader for proper position tracking
  (edamame/reader s))

(defn source-reader
  "Create a source reader from a string that tracks original source text for parse-next+string."
  [s]
  (edamame/source-reader s))

(defn parse-next
  "Parse the next form from a reader."
  [ctx rdr]
  (let [eof ::eof
        opts (merge (make-reader-opts)
                    {:eof eof})
        form (edamame/parse-next rdr opts)]
    (if (identical? form eof) ::eof form)))

(defn get-line-number [rdr]
  (edamame/get-line-number rdr))

(defn get-column-number [rdr]
  (edamame/get-column-number rdr))

;; ============================================================
;; Vars API
;; ============================================================

(defn new-var
  "Create a new SCI var."
  ([name] (new-var name nil nil))
  ([name init-val] (new-var name init-val nil))
  ([name init-val opts]
   init-val))

(defn new-dynamic-var
  "Create a new dynamic SCI var. Returns a DynamicVar that wraps an atom for thread-local storage."
  ([name] (new-dynamic-var name nil nil))
  ([name init-val] (new-dynamic-var name init-val nil))
  ([name init-val opts]
   (sci.lang/->DynamicVar (atom init-val) (or opts {}))))

(defmacro copy-var
  "Copy a Clojure var into an SCI namespace."
  ([clj-var sci-ns]
   `(copy-var ~clj-var ~sci-ns nil))
  ([clj-var sci-ns opts]
   (let [copy-meta-from (when (map? opts) (:copy-meta-from opts))
         opts-expr (if copy-meta-from
                     (let [clean-opts (dissoc opts :copy-meta-from)]
                       `(merge (meta (var ~copy-meta-from)) ~clean-opts))
                     opts)]
     `(let [v# (var ~clj-var)
            m# (meta v#)
            val# (deref v#)
            merged-meta# (merge m# ~opts-expr)]
        ;; Return a sci.lang.Var so non-IObj values (e.g. Long) can carry metadata.
        (sci.lang/->Var (quote ~clj-var) val# merged-meta# (boolean (:dynamic m#)))))))

(defn copy-var*
  "Copy a Clojure var into an SCI namespace (runtime version, takes a var)."
  ([clj-var sci-ns] (copy-var* clj-var sci-ns nil))
  ([clj-var sci-ns opts]
   (let [m (meta clj-var)
         val (deref clj-var)
         merged-meta (merge m opts)]
     (sci.lang/->Var (.-sym clj-var) val merged-meta (boolean (:dynamic m))))))

(defmacro copy-ns
  "Copy a Clojure namespace into SCI."
  ([ns-sym sci-ns]
   `(copy-ns ~ns-sym ~sci-ns nil))
  ([ns-sym sci-ns opts]
   (let [;; Extract opts at compile time to quote symbols properly
         opts-map (when (map? opts) opts)
         exclude-syms (when opts-map (:exclude opts-map))
         exclude-when-meta-keys (when opts-map (:exclude-when-meta opts-map))
         copy-meta-val (when opts-map (:copy-meta opts-map))]
     `(let [ns# (the-ns '~ns-sym)
            publics# (clojure.core/ns-publics ns#)
            exclude# '~(set exclude-syms)
            exclude-when-meta# '~(set exclude-when-meta-keys)
          copy-meta-val# ~(if (= :all copy-meta-val) :all
                              (when copy-meta-val `'~(vec copy-meta-val)))]
        (reduce-kv
         (fn [m# sym# v#]
           (let [vm# (meta v#)]
             (if (or (contains? exclude# sym#)
                     (and (not= :all copy-meta-val#)
                          (:skip-wiki vm#))
                     (some #(get vm# %) exclude-when-meta#))
               m#
               (let [val# (deref v#)
                     selected-meta# (cond
                                      (= :all copy-meta-val#) vm#
                                      copy-meta-val#
                                      (select-keys vm# (concat [:name :arglists :macro :sci/macro] copy-meta-val#))
                                      :else
                                      (select-keys vm# [:name :arglists :macro :sci/macro :doc]))]
                 (assoc m# sym# (with-meta
                                  (if (or (:macro vm#) (:sci/macro vm#))
                                    val#
                                    (fn [& args#] (apply val# args#)))
                                  selected-meta#))))))
         {}
         publics#)))))

(defn alter-var-root
  "Alter the root value of a var."
  [v f & args]
  (apply f @v args))

(defn intern
  "Intern a var."
  [ctx ns-sym var-name val]
  (let [qualified (symbol (str ns-sym) (str var-name))
        entry {:val val :meta {} :dynamic? false :bound? true}]
    (when-let [a (:heap-atom ctx)]
      (swap! a assoc qualified entry))
    (update ctx :heap assoc qualified entry)))

;; ============================================================
;; Dynamic binding macros
;; ============================================================

(def ^:private sci-var->clj-var
  "Mapping from SCI atom vars to their corresponding Clojure dynamic vars."
  {'sci.core/out       #'*out*
   'sci.core/in        #'*in*
   'sci.core/err       #'*err*
   'sci.core/print-length #'*print-length*})

(defmacro binding
  "Dynamic binding form for SCI vars.
   Supports both real Clojure vars and SCI dynamic vars (atoms)."
  [bindings & body]
  (let [pairs (partition 2 bindings)
        ;; Check at compile time if the binding targets are vars
        all-vars? (every? (fn [[target _]]
                            (let [v (clojure.core/resolve target)]
                              (and (symbol? target) v (var? v)
                                   (.isDynamic ^clojure.lang.Var v))))
                          pairs)]
    (if all-vars?
      `(clojure.core/binding ~bindings ~@body)
      ;; For SCI dynamic vars (atoms), save/restore manually
      ;; Also push real JVM thread bindings for vars like *out*, *print-length*
      (let [sym-pairs (mapv (fn [[target val-expr]]
                              [(gensym "old") target val-expr])
                            pairs)
            ;; Find corresponding real Clojure vars to thread-bind
            thread-binds (keep (fn [[_ target val-expr]]
                                 (let [resolved (clojure.core/resolve target)
                                       fq (when resolved
                                             (symbol (str (.ns ^clojure.lang.Var resolved))
                                                     (str (.sym ^clojure.lang.Var resolved))))]
                                   (when-let [clj-var (get sci-var->clj-var fq)]
                                     [clj-var val-expr])))
                               sym-pairs)
            has-thread-binds? (seq thread-binds)]
        (if has-thread-binds?
          ;; Wrap in clojure.core/binding for the real vars, plus atom save/restore
          (let [clj-bindings (vec (mapcat (fn [[v expr]]
                                            [(symbol (str (.ns ^clojure.lang.Var v))
                                                     (str (.sym ^clojure.lang.Var v)))
                                             expr])
                                          thread-binds))]
            `(let [~@(mapcat (fn [[old-sym target _]] [old-sym `(deref ~target)]) sym-pairs)]
               ~@(mapv (fn [[_ target val-expr]] `(reset! ~target ~val-expr)) sym-pairs)
               (try
                 (clojure.core/binding ~clj-bindings
                   ~@body)
                 (finally
                   ~@(mapv (fn [[old-sym target _]] `(reset! ~target ~old-sym)) sym-pairs)))))
          `(let [~@(mapcat (fn [[old-sym target _]] [old-sym `(deref ~target)]) sym-pairs)]
             ~@(mapv (fn [[_ target val-expr]] `(reset! ~target ~val-expr)) sym-pairs)
             (try
               (do ~@body)
               (finally
                 ~@(mapv (fn [[old-sym target _]] `(reset! ~target ~old-sym)) sym-pairs)))))))))

(defmacro with-bindings
  "Execute body with SCI var bindings. Keys must be dynamic vars (atoms from new-dynamic-var)."
  [binding-map & body]
  `(let [bmap# ~binding-map]
     (doseq [[k# _#] bmap#]
       (when-not #?(:clj (or (instance? clojure.lang.Atom k#) (instance? sci.lang.DynamicVar k#))
                    :cljs (or (instance? cljs.core/Atom k#) (instance? sci.lang.DynamicVar k#)))
         (throw (ex-info (str "Cannot bind non-dynamic var: " k#)
                         {:type :bind-non-dynamic}))))
     (let [saved# (into {} (map (fn [[v# _#]] [v# @v#]) bmap#))]
       (try
         (doseq [[v# val#] bmap#]
           (reset! v# val#))
         ~@body
         (finally
           (doseq [[v# old#] saved#]
             (reset! v# old#)))))))

(defmacro with-redefs
  "Temporarily redefine vars."
  [bindings & body]
  `(clojure.core/with-redefs ~bindings ~@body))

;; ============================================================
;; Namespace operations
;; ============================================================

(defn create-ns
  "Create a namespace in the SCI context."
  [sym]
  sym)

(defn find-ns
  "Find a namespace."
  [ctx sym]
  nil)

(defn add-namespace!
  "Add a namespace to a context."
  [ctx ns-sym ns-map]
  ctx)

(defn add-class!
  "Add a class to a context."
  [ctx class-sym class]
  ctx)

(defn add-import!
  "Add an import to a context."
  [ctx ns-sym class-sym class]
  ctx)

(defn merge-opts
  "Merge additional options into a context."
  [ctx opts]
  (let [ctx (merge ctx (dissoc opts :namespaces :bindings))]
    ;; Merge custom namespaces into heap
    (if-let [namespaces (:namespaces opts)]
      (let [heap (reduce-kv
                  (fn [h ns-sym ns-map]
                    (reduce-kv
                     (fn [h2 sym val]
                       (let [sym-name (if (symbol? sym) (name sym) (str sym))
                             qualified (symbol (str ns-sym) sym-name)]
                         (assoc h2 qualified {:val val :meta {} :dynamic? false})))
                     h ns-map))
                  (:heap ctx)
                  namespaces)]
        ;; Update both the context heap and shared heap-atom
        (let [new-entries (reduce-kv
                           (fn [acc k v]
                             (if (not= v (get (:heap ctx) k))
                               (assoc acc k v) acc))
                           {} heap)]
          (when-let [a (:heap-atom ctx)]
            (swap! a merge new-entries))
          (assoc ctx :heap heap)))
      ctx)))

;; ============================================================
;; IO vars
;; ============================================================

(def in (atom *in*))
(def out (atom *out*))
(def err (atom *err*))
(def print-fn (atom nil))
(def print-length (atom nil))
(def print-namespace-maps (atom true))
(def ns (atom (clojure.core/find-ns 'user)))
(def read-eval (atom false))
(def assert (atom true))
(def ^:dynamic file nil)

;; ============================================================
;; IO wrappers
;; ============================================================

(defmacro with-out-str [& body]
  `(let [sw# (java.io.StringWriter.)
         old-out# @out]
     (reset! out sw#)
     (try
       (binding [*out* sw#]
         ~@body)
       (finally
         (reset! out old-out#)))
     (str sw#)))

(defmacro with-in-str [s & body]
  `(let [sr# (java.io.StringReader. ~s)
         old-in# @in]
     (reset! in sr#)
     (try
       (binding [*in* (clojure.java.io/reader sr#)]
         ~@body)
       (finally
         (reset! in old-in#)))))

(defmacro future [& body]
  `(clojure.core/future ~@body))

(defmacro pmap [f & colls]
  `(clojure.core/pmap ~f ~@colls))

;; ============================================================
;; Stacktrace / error support
;; ============================================================

(defn stacktrace [e]
  (when-let [data (ex-data e)]
    (:sci.impl/callstack data)))

(defn format-stacktrace [st]
  (when st
    (let [entries (->> st
                       (filter :line)
                       (mapv (fn [{:keys [ns name line column file]}]
                               (let [ns-str (str (or ns "user"))
                                     name-str (if name (str ns-str "/" name) ns-str)
                                     file-str (or file "NO_SOURCE_PATH")]
                                 {:name-str name-str
                                  :loc (str file-str ":" line ":" column)}))))
          max-len (reduce max 0 (map (comp count :name-str) entries))]
      (mapv (fn [{:keys [name-str loc]}]
              (str name-str
                   (apply str (repeat (- max-len (count name-str)) " "))
                   " - "
                   loc))
            entries))))

;; ============================================================
;; set! for dynamic vars
;; ============================================================

(defn set!
  "Set a dynamic var's value."
  [v val]
  (if (or (instance? #?(:clj clojure.lang.Atom :cljs Atom) v)
          (instance? sci.lang.DynamicVar v))
    (reset! v val)
    val))

;; resolve is defined at the bottom of the file

;; ============================================================
;; EOF sentinel
;; ============================================================

(def eof ::eof)

(defn parse-next+string
  "Parse the next form from a reader, returning [form string].
   rdr must be created with source-reader to get the original source text."
  [ctx rdr]
  (let [eof ::eof
        opts (edamame/normalize-opts (merge (make-reader-opts) {:eof eof}))
        [form s] (edamame/parse-next+string rdr opts)]
    (if (identical? form eof)
      [::eof nil]
      [form s])))

;; ============================================================
;; Additional API functions
;; ============================================================

(defn var->symbol
  "Get the fully qualified symbol for a var-like value."
  [v]
  (cond
    (instance? sci.lang.Var v) (or (:sci.impl/var-sym (.-meta-map ^sci.lang.Var v))
                                   (.-sym ^sci.lang.Var v))
    (var? v) (let [m (meta v)] (symbol (str (:ns m)) (str (:name m))))
    :else nil))

(defn eval-string+
  "Like eval-string but returns a map with :val and :ns."
  ([ctx s] (eval-string+ ctx s nil))
  ([ctx s opts]
   (let [reader-opts (cond-> {}
                       (:features ctx) (assoc :features (:features ctx))
                       (:readers ctx) (assoc :readers (:readers ctx)))
         forms (read-all s 'user reader-opts)
         machine (make-machine-from-ctx ctx forms)
         current-ns-atom (:current-ns-atom machine)
         result (step/run machine)]
     {:val result
      :ns @current-ns-atom})))

(defn resolve
  "Resolve a symbol in a context."
  ([ctx sym]
   (when-let [heap (:heap ctx)]
     (let [qualified (if (qualified-symbol? sym)
                       sym
                       (symbol "clojure.core" (str sym)))]
       (when-let [entry (get heap qualified)]
         (:val entry))))))

;; ============================================================
;; Suspend / Freeze / Thaw / Resume
;; ============================================================

(defn resume
  "Resume a suspended machine, optionally providing a return value for (suspend!).
   Returns the final result if the computation completes, or a new suspended machine."
  ([machine] (resume machine nil))
  ([machine value]
   (step/run (machine/resume machine value))))

(defn freeze
  "Serialize a suspended machine to an EDN string."
  [machine]
  (vm-freeze/freeze machine))

(defn thaw
  "Deserialize an EDN string back into a live (suspended) machine."
  [edn-str]
  (vm-freeze/thaw edn-str))
