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
            [clojure.string :as str])
  #?(:cljs (:require-macros [sci.core])))

(declare read-eval)
(declare out print-fn)

(defn- type-methods
  "Get the methods map from a sci.lang.Type instance.
   Works around CLJS field munging where `methods` becomes `methods$`."
  [^sci.lang.Type type-obj]
  #?(:clj (.-methods type-obj)
     :cljs (unchecked-get type-obj "methods$")))

(defn- type-name
  "Get the name from a sci.lang.Type instance.
   Uses HasName protocol to work across CLJ/CLJS."
  [^sci.lang.Type type-obj]
  #?(:clj (.getName type-obj)
     :cljs (sci.impl.types/getName type-obj)))

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
        ;; Already namespace-qualified → check for array type notation first
         (namespace sym)
         #?(:clj
            (let [ns-part (namespace sym)
                  name-part (name sym)]
              (if-let [dims (try (let [d (Integer/parseInt name-part)]
                                   (when (pos? d) d))
                                 (catch NumberFormatException _ nil))]
               ;; Clojure 1.12 array notation: type/N → resolve to array class name symbol
                (let [prim->prefix {"long" "[J" "int" "[I" "double" "[D" "float" "[F"
                                    "short" "[S" "byte" "[B" "boolean" "[Z" "char" "[C"}]
                  (or
                   ;; Primitive types
                   (when-let [prim-prefix (get prim->prefix ns-part)]
                     (symbol (str (apply str (repeat (dec dims) \[)) prim-prefix)))
                   ;; java.lang classes (default imports) — both short and FQ forms
                   (let [klass (if (> (.indexOf ^String ns-part ".") -1)
                                 ;; Fully qualified: only resolve java.lang.* classes
                                 (when (.startsWith ^String ns-part "java.lang.")
                                   (try (Class/forName ns-part)
                                        (catch ClassNotFoundException _ nil)))
                                 ;; Short name: try java.lang.* prefix
                                 (try (Class/forName (str "java.lang." ns-part))
                                      (catch ClassNotFoundException _ nil)))]
                     (when klass
                       (symbol (str (apply str (repeat dims \[))
                                    "L" (.getName ^Class klass) ";"))))
                   ;; Not resolvable as array type → keep as-is
                   sym))
               ;; Not array notation → resolve namespace aliases
                (or (when ns-atom
                      (let [aliases (get-in @ns-atom [current-ns :aliases])
                            resolved-ns (get aliases (symbol ns-part))]
                        (when resolved-ns
                          (symbol (str resolved-ns) name-part))))
                   ;; Check if ns-part is a known namespace in the heap
                    (when heap-atom
                      (let [h @heap-atom
                           ;; Check if any var exists with this namespace
                            qualified (symbol ns-part name-part)]
                        (when (get h qualified) qualified)))
                    sym)))
            :cljs
            (let [ns-part (namespace sym)
                  name-part (name sym)]
              (or (when ns-atom
                    (let [aliases (get-in @ns-atom [current-ns :aliases])
                          resolved-ns (get aliases (symbol ns-part))]
                      (when resolved-ns
                        (symbol (str resolved-ns) name-part))))
                  ;; Check if ns-part is a known namespace in the heap
                  (when heap-atom
                    (let [h @heap-atom
                          qualified (symbol ns-part name-part)]
                      (when (get h qualified) qualified)))
                  sym)))

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
                (symbol (type-name type-obj)))))
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
         ;; Java class? (but not if explicitly unmapped)
          (when-not (and ns-atom
                         (contains? (get-in @ns-atom [current-ns :unmapped]) sym))
            (sq-resolve-class sym))
         ;; Host Clojure var from standard namespaces (clojure.core etc.) only.
         ;; We restrict to standard namespaces to avoid picking up host-level vars
         ;; that happen to shadow SCI user-defined symbols (e.g. sci.copy-ns-test-ns/bar).
          (let [unmapped? (and ns-atom
                               (contains? (get-in @ns-atom [current-ns :unmapped]) sym))
                excluded? (or unmapped?
                              (when ns-atom
                                (let [excludes (get-in @ns-atom [current-ns :refer-clojure-excludes])]
                                  (and excludes (contains? excludes (symbol sym-name))))))
                resolved (when-not excluded?
                           #?(:clj (clojure.core/resolve sym)
                              :cljs ;; On CLJS, resolve is a macro. Check the heap instead.
                              (when heap-atom
                                (let [h @heap-atom]
                                  (some (fn [ns-str]
                                          (let [q (symbol ns-str sym-name)]
                                            (when (get h q)
                                              (with-meta (symbol sym-name)
                                                {:ns (symbol ns-str) :name (symbol sym-name)}))))
                                        ["clojure.core" "clojure.string" "clojure.set"
                                         "clojure.walk" "clojure.edn" "clojure.repl"])))))]
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
   (cond->
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
                          ns-aliases)}
    ;; Add SCI record tagged literal readers when heap is available
     heap-atom (assoc :readers
                      #?(:clj (fn [tag]
                                (or (get clojure.core/default-data-readers tag)
                                    (let [tag-str (str tag)
                                          idx (.lastIndexOf ^String tag-str ".")]
                                      (when (> idx 0)
                                        (let [ns-str (subs tag-str 0 idx)
                                              type-str (subs tag-str (inc idx))
                                              map-ctor-sym (symbol ns-str (str "map->" type-str))
                                              entry (get @heap-atom map-ctor-sym)]
                                          (when entry (:val entry)))))))
                         :cljs (fn [tag]
                                 (cond
                                   (= 'js tag)
                                   (fn [v]
                                     (if (map? v)
                                       (apply list 'js-obj
                                              (mapcat (fn [[k val]]
                                                        [(if (keyword? k) (name k) (str k)) val])
                                                      v))
                                       (apply list 'array (seq v))))
                                   (= 'queue tag)
                                   (fn [v] (into cljs.core/PersistentQueue.EMPTY v))
                                   :else
                                  ;; SCI record tagged literal readers (e.g. #foo.A{...})
                                   (let [tag-str (str tag)
                                         idx (.lastIndexOf tag-str ".")]
                                     (when (> idx 0)
                                       (let [ns-str (subs tag-str 0 idx)
                                             type-str (subs tag-str (inc idx))
                                             map-ctor-sym (symbol ns-str (str "map->" type-str))
                                             entry (get @heap-atom map-ctor-sym)]
                                         (when entry (:val entry))))))))))))

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
                disable-arity-checks deftype-fn reify-fn]} opts
        heap (host/default-heap)
        ns-table (host/default-ns-table)
        ;; Helper: get existing :doc from heap for an entry we're about to override
        existing-doc (fn [sym] (get-in heap [sym :meta :doc]))
        ;; Override satisfies? to handle SCI protocols
        heap (assoc heap (symbol "clojure.core" "satisfies?")
                    {:val (fn sci-satisfies? [protocol x]
                            (cond
                              (and (map? protocol) (= :sci/protocol (:type protocol)))
                              (let [impls @(:impls protocol)
                                    sci-type (when (map? x) (:type (clojure.core/meta x)))
                                    target-type (or sci-type (type x))]
                                (boolean
                                 (or (get impls target-type)
                                     (some (fn [[t _]]
                                             (and #?(:clj (class? t) :cljs (fn? t))
                                                  #?(:clj (instance? t x)
                                                     :cljs (or (instance? t x)
                                                               (and (= t js/String) (string? x))
                                                               (and (= t js/Number) (number? x))
                                                               (and (= t js/Boolean) (boolean? x))
                                                               (and (= t js/Function) (fn? x))
                                                               (and (= t js/Array) (array? x))))))
                                           impls)
                                     (when (nil? x) (get impls nil))
                                     (get impls #?(:clj Object :cljs js/Object))
                                     (get impls :default)
                                     ;; For CLJS: check if object satisfies the corresponding host protocol
                                     #?(:cljs (let [pname (:name protocol)]
                                                (case pname
                                                  clojure.core/IDeref (clojure.core/satisfies? IDeref x)
                                                  clojure.core/ISwap (clojure.core/satisfies? ISwap x)
                                                  clojure.core/IReset (clojure.core/satisfies? IReset x)
                                                  clojure.core/IWriter (clojure.core/satisfies? IWriter x)
                                                  clojure.core/IPrintWithWriter (clojure.core/satisfies? IPrintWithWriter x)
                                                  clojure.core/IRecord (boolean (:sci.impl/record (clojure.core/meta x)))
                                                  false))
                                        :clj nil))))
                              ;; Host protocol wrapped in a map (from sci/new-var)
                              ;; clojure.core/satisfies? is a macro in CLJS — can't call with runtime protocol
                              #?@(:clj [(and (map? protocol) (:protocol protocol))
                                        (clojure.core/satisfies? (:protocol protocol) x)
                                        ;; Fall back to clojure.core/satisfies? for real protocols
                                        :else
                                        (clojure.core/satisfies? protocol x)]
                                  :cljs [:else false])))
                     :meta {:name 'satisfies? :doc #?(:clj (:doc (meta #'clojure.core/satisfies?)) :cljs "Returns true if x satisfies the protocol")}
                     :dynamic? false})
        ;; Override deref to handle SCI type instances with deref methods
        heap (assoc heap (symbol "clojure.core" "deref")
                    {:val (fn sci-deref
                            ([ref]
                             (if-let [type-obj (:type (clojure.core/meta ref))]
                               (if (instance? sci.lang.Type type-obj)
                                 (let [methods (type-methods type-obj)
                                       deref-fn (or (get methods 'deref)
                                                    (get methods '-deref))]
                                   (if deref-fn
                                     (deref-fn ref)
                                     (clojure.core/deref ref)))
                                 (clojure.core/deref ref))
                               (clojure.core/deref ref)))
                            #?@(:clj [([ref timeout-ms timeout-val]
                                       (clojure.core/deref ref timeout-ms timeout-val))]))
                     :meta {:name 'deref :doc #?(:clj (:doc (meta #'clojure.core/deref)) :cljs (existing-doc (symbol "clojure.core" "deref")))}
                     :dynamic? false})
        ;; Override swap! and reset! to handle SCI type instances with swap/reset methods
        heap (assoc heap (symbol "clojure.core" "swap!")
                    {:val (fn sci-swap!
                            ([ref f]
                             (if-let [type-obj (:type (clojure.core/meta ref))]
                               (if (instance? sci.lang.Type type-obj)
                                 (let [methods (type-methods type-obj)
                                       swap-fn (or (get methods 'swap) (get methods '-swap!))]
                                   (if swap-fn
                                     (swap-fn ref f)
                                     (clojure.core/swap! ref f)))
                                 (clojure.core/swap! ref f))
                               (clojure.core/swap! ref f)))
                            ([ref f a]
                             (if-let [type-obj (:type (clojure.core/meta ref))]
                               (if (instance? sci.lang.Type type-obj)
                                 (let [methods (type-methods type-obj)
                                       swap-fn (or (get methods 'swap) (get methods '-swap!))]
                                   (if swap-fn
                                     (swap-fn ref f a)
                                     (clojure.core/swap! ref f a)))
                                 (clojure.core/swap! ref f a))
                               (clojure.core/swap! ref f a)))
                            ([ref f a b]
                             (if-let [type-obj (:type (clojure.core/meta ref))]
                               (if (instance? sci.lang.Type type-obj)
                                 (let [methods (type-methods type-obj)
                                       swap-fn (or (get methods 'swap) (get methods '-swap!))]
                                   (if swap-fn
                                     (swap-fn ref f a b)
                                     (clojure.core/swap! ref f a b)))
                                 (clojure.core/swap! ref f a b))
                               (clojure.core/swap! ref f a b)))
                            ([ref f a b & args]
                             (if-let [type-obj (:type (clojure.core/meta ref))]
                               (if (instance? sci.lang.Type type-obj)
                                 (let [methods (type-methods type-obj)
                                       swap-fn (or (get methods 'swap) (get methods '-swap!))]
                                   (if swap-fn
                                     (apply swap-fn ref f a b args)
                                     (apply clojure.core/swap! ref f a b args)))
                                 (apply clojure.core/swap! ref f a b args))
                               (apply clojure.core/swap! ref f a b args))))
                     :meta {:name 'swap! :doc #?(:clj (:doc (meta #'clojure.core/swap!)) :cljs (existing-doc (symbol "clojure.core" "swap!")))}
                     :dynamic? false})
        heap (assoc heap (symbol "clojure.core" "reset!")
                    {:val (fn sci-reset! [ref v]
                            (if-let [type-obj (:type (clojure.core/meta ref))]
                              (if (instance? sci.lang.Type type-obj)
                                (let [methods (type-methods type-obj)
                                      reset-fn (or (get methods 'reset) (get methods '-reset!))]
                                  (if reset-fn
                                    (reset-fn ref v)
                                    (clojure.core/reset! ref v)))
                                (clojure.core/reset! ref v))
                              (clojure.core/reset! ref v)))
                     :meta {:name 'reset! :doc #?(:clj (:doc (meta #'clojure.core/reset!)) :cljs (existing-doc (symbol "clojure.core" "reset!")))}
                     :dynamic? false})
        ;; Override reset-vals! and swap-vals! to handle SCI type instances
        heap (assoc heap (symbol "clojure.core" "reset-vals!")
                    {:val (fn sci-reset-vals! [ref newval]
                            (if-let [type-obj (:type (clojure.core/meta ref))]
                              (if (instance? sci.lang.Type type-obj)
                                (let [methods (type-methods type-obj)
                                      rv-fn (get methods 'resetVals)]
                                  (if rv-fn
                                    (rv-fn ref newval)
                                    (clojure.core/reset-vals! ref newval)))
                                (clojure.core/reset-vals! ref newval))
                              (clojure.core/reset-vals! ref newval)))
                     :meta {:name 'reset-vals! :doc #?(:clj (:doc (meta #'clojure.core/reset-vals!)) :cljs (existing-doc (symbol "clojure.core" "reset-vals!")))}
                     :dynamic? false})
        heap (assoc heap (symbol "clojure.core" "swap-vals!")
                    {:val (fn sci-swap-vals!
                            ([ref f]
                             (if-let [type-obj (:type (clojure.core/meta ref))]
                               (if (instance? sci.lang.Type type-obj)
                                 (let [methods (type-methods type-obj)
                                       sv-fn (get methods 'swapVals)]
                                   (if sv-fn
                                     (sv-fn ref f)
                                     (clojure.core/swap-vals! ref f)))
                                 (clojure.core/swap-vals! ref f))
                               (clojure.core/swap-vals! ref f)))
                            ([ref f a] (clojure.core/swap-vals! ref f a))
                            ([ref f a b] (clojure.core/swap-vals! ref f a b))
                            ([ref f a b & args] (apply clojure.core/swap-vals! ref f a b args)))
                     :meta {:name 'swap-vals! :doc #?(:clj (:doc (meta #'clojure.core/swap-vals!)) :cljs (existing-doc (symbol "clojure.core" "swap-vals!")))}
                     :dynamic? false})
        heap (assoc heap (symbol "clojure.core" "compare-and-set!")
                    {:val (fn sci-compare-and-set! [ref oldval newval]
                            (if-let [type-obj (:type (clojure.core/meta ref))]
                              (if (instance? sci.lang.Type type-obj)
                                (let [methods (type-methods type-obj)
                                      cas-fn (get methods 'compareAndSet)]
                                  (if cas-fn
                                    (cas-fn ref oldval newval)
                                    (clojure.core/compare-and-set! ref oldval newval)))
                                (clojure.core/compare-and-set! ref oldval newval))
                              (clojure.core/compare-and-set! ref oldval newval)))
                     :meta {:name 'compare-and-set! :doc #?(:clj (:doc (meta #'clojure.core/compare-and-set!)) :cljs (existing-doc (symbol "clojure.core" "compare-and-set!")))}
                     :dynamic? false})
        ;; Override derive/underive/isa?/parents/ancestors/descendants to:
        ;; 1. Handle SCI types (sci.lang.Type) by converting to qualified symbols
        ;; 2. Use a per-context hierarchy atom instead of the global one
        hierarchy-atom (atom (clojure.core/make-hierarchy))
        heap (let [type->tag (fn [t]
                               (if (instance? sci.lang.Type t)
                                 (let [n (type-name t)
                                       idx (.lastIndexOf ^String n ".")]
                                   (if (pos? idx)
                                     (symbol (subs n 0 idx) (subs n (inc idx)))
                                     (symbol "user" n)))
                                 t))]
               (-> heap
                   (assoc (symbol "clojure.core" "make-hierarchy")
                          {:val clojure.core/make-hierarchy
                           :meta {:name 'make-hierarchy :doc #?(:clj (:doc (meta #'clojure.core/make-hierarchy)) :cljs (existing-doc (symbol "clojure.core" "make-hierarchy")))}})
                   (assoc (symbol "clojure.core" "derive")
                          {:val (fn sci-derive
                                  ([tag parent]
                                   (swap! hierarchy-atom clojure.core/derive (type->tag tag) (type->tag parent))
                                   nil)
                                  ([h tag parent] (clojure.core/derive h (type->tag tag) (type->tag parent))))
                           :meta {:name 'derive :doc #?(:clj (:doc (meta #'clojure.core/derive)) :cljs (existing-doc (symbol "clojure.core" "derive")))}
                           :dynamic? false})
                   (assoc (symbol "clojure.core" "underive")
                          {:val (fn sci-underive
                                  ([tag parent]
                                   (swap! hierarchy-atom clojure.core/underive (type->tag tag) (type->tag parent))
                                   nil)
                                  ([h tag parent] (clojure.core/underive h (type->tag tag) (type->tag parent))))
                           :meta {:name 'underive :doc #?(:clj (:doc (meta #'clojure.core/underive)) :cljs (existing-doc (symbol "clojure.core" "underive")))}
                           :dynamic? false})
                   (assoc (symbol "clojure.core" "isa?")
                          {:val (fn sci-isa?
                                  ([child parent] (clojure.core/isa? @hierarchy-atom (type->tag child) (type->tag parent)))
                                  ([h child parent] (clojure.core/isa? h (type->tag child) (type->tag parent))))
                           :meta {:name 'isa? :doc #?(:clj (:doc (meta #'clojure.core/isa?)) :cljs "Returns true if (= child parent), or child is directly or indirectly derived from parent")}
                           :dynamic? false})
                   (assoc (symbol "clojure.core" "parents")
                          {:val (fn sci-parents
                                  ([tag] (clojure.core/parents @hierarchy-atom (type->tag tag)))
                                  ([h tag] (clojure.core/parents h (type->tag tag))))
                           :meta {:name 'parents :doc #?(:clj (:doc (meta #'clojure.core/parents)) :cljs (existing-doc (symbol "clojure.core" "parents")))}
                           :dynamic? false})
                   (assoc (symbol "clojure.core" "ancestors")
                          {:val (fn sci-ancestors
                                  ([tag] (clojure.core/ancestors @hierarchy-atom (type->tag tag)))
                                  ([h tag] (clojure.core/ancestors h (type->tag tag))))
                           :meta {:name 'ancestors :doc #?(:clj (:doc (meta #'clojure.core/ancestors)) :cljs (existing-doc (symbol "clojure.core" "ancestors")))}
                           :dynamic? false})
                   (assoc (symbol "clojure.core" "descendants")
                          {:val (fn sci-descendants
                                  ([tag] (clojure.core/descendants @hierarchy-atom (type->tag tag)))
                                  ([h tag] (clojure.core/descendants h (type->tag tag))))
                           :meta {:name 'descendants :doc #?(:clj (:doc (meta #'clojure.core/descendants)) :cljs (existing-doc (symbol "clojure.core" "descendants")))}
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
    (let [heap-atom (atom heap)
          ;; Build :env for backwards compatibility — provides (-> ctx :env deref :namespaces)
          env (atom {:namespaces
                     (reduce-kv
                      (fn [nss sym entry]
                        (let [ns-sym (symbol (namespace sym))
                              var-name (symbol (name sym))
                              v (sci.lang.Var. sym (:val entry)
                                               (or (:meta entry) {}) (:dynamic? entry))]
                          (update nss ns-sym assoc var-name v)))
                      {} heap)})]
      {:heap heap
       :heap-atom heap-atom
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
       :deftype-fn deftype-fn
       :reify-fn reify-fn
       :env env
       #?@(:clj [:inverse-registry (host/inverse-registry heap)])})))

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
         type-obj type-obj
         ;; Check imports (e.g. java.lang.Object imported as Object)
         :else
         (when-not (qualified-symbol? sym)
           (get (:imports ns-data) sym)))))))

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
          #?(:clj (with-redefs-fn (into {} clj-bindings) func)
             :cljs (func)) ;; host var redefs not supported in CLJS
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
      #?(:clj (apply clojure.core/alter-var-root v f args)
         :cljs (throw (ex-info "alter-var-root not supported for host vars in CLJS" {:type :sci/error}))))))

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

(def ^:private vm-special-forms
  "Special forms handled directly by the VM step dispatcher — macroexpand-1 must not expand these."
  #{'ns 'in-ns 'def 'do 'if 'let 'let* 'fn 'fn* 'quote 'var 'try 'catch 'finally
    'throw 'loop 'loop* 'recur 'new 'set! 'import* 'deftype* 'reify*
    '. 'binding 'case*})

(defn- make-macroexpand-1-fn [heap-atom]
  (fn sci-macroexpand-1
    ([form]
     (if-not (and (seq? form) (symbol? (first form)))
       form
       (let [head (first form)
             n    (name head)]
         ;; Don't expand VM special forms
         (if (contains? vm-special-forms head)
           form
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
                 form)))))))
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

(defn- sci-write-line
  "Write a line to the current SCI output destination."
  [s]
  #?(:clj (do (.write ^java.io.Writer *out* ^String (str s))
              (.write ^java.io.Writer *out* "\n"))
     :cljs (if-let [w @out]
             (do (-write w (str s)) (-write w "\n"))
             (if-let [pf @print-fn]
               (do (pf (str s)) (pf "\n"))
               (when *print-fn*
                 (*print-fn* (str s))
                 (*print-fn* "\n"))))))

(defn- sci-print-doc
  "Print documentation for a SCI var entry's metadata, compatible with
   clojure.repl/print-doc but using SCI-side symbol/string instead of Clojure namespace."
  [{:keys [ns name arglists macro doc special-form]}]
  (sci-write-line "-------------------------")
  (sci-write-line (str (when ns (str (clojure.core/name (clojure.core/symbol (str ns))) "/")) name))
  (when arglists (sci-write-line (pr-str arglists)))
  (when macro (sci-write-line "Macro"))
  (when special-form (sci-write-line "Special Form"))
  (when doc (sci-write-line (str "  " doc)))
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

(defn- sci-print-doc* [m]
  #?(:clj (#'clojure.repl/print-doc m)
     :cljs (do (sci-write-line "-------------------------")
               (sci-write-line (str (:name m)))
               (when-let [arglists (:arglists m)]
                 ;; arglists may be (quote ([x])) from macro output; unwrap
                 (let [arglists (if (and (seq? arglists) (= 'quote (first arglists)))
                                  (second arglists)
                                  arglists)]
                   (sci-write-line (pr-str arglists))))
               (when (:macro m)
                 (sci-write-line "Macro"))
               (when-let [doc (:doc m)]
                 (sci-write-line (str "  " doc))))))

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
        (sci-print-doc* (merge (dissoc (:meta entry) :ns) {:name qualified-sym})))
      (when-let [ns-data @(or (:ns-atom ctx) (atom {}))]
        (doseq [[ns-sym ns-info] (sort-by first ns-data)]
          (when-let [doc-str (:doc ns-info)]
            (when (re-find re doc-str)
              (sci-print-doc* {:name ns-sym :doc doc-str}))))))))

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
            (list 'declare (symbol (str "->" name-sym)))
            (apply list 'deftype* qualified dotted fields :implements proto-syms methods)))))

;; ============================================================
;; IO vars (defined early so heap entries can reference `out`)
;; ============================================================

(def in (atom #?(:clj *in* :cljs nil)))
(def out (atom #?(:clj *out* :cljs nil)))
(def err (atom #?(:clj *err* :cljs nil)))
(def print-fn (atom nil))
(def print-length (atom nil))
(def print-namespace-maps (atom true))
(def ns (atom #?(:clj (clojure.core/find-ns 'user) :cljs 'user)))
(def read-eval (atom false))
(def assert (atom true))
(def file (atom nil))

;; ============================================================

(defn- make-machine-from-ctx
  "Create a fresh machine from a context and a list of forms."
  [ctx forms]
  (let [heap-atom   (or (:heap-atom ctx) (atom (:heap ctx)))
        existing-doc (fn [sym] (get-in @heap-atom [sym :meta :doc]))
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
                               #?(:clj (var-get v)
                                  :cljs (if (satisfies? IDeref v)
                                          @v
                                          (throw (ex-info "var-get not supported for host vars in CLJS" {:type :sci/error}))))))
                      :meta {:name 'var-get :doc #?(:clj (:doc (meta #'clojure.core/var-get)) :cljs (existing-doc (symbol "clojure.core" "var-get")))}}
                     (symbol "clojure.core" "thread-bound?")
                     {:val (fn sci-thread-bound? [& vars]
                             (every? (fn [v]
                                       (if (instance? sci.lang.Var v)
                                         (let [sym (var-qualified-sym v)
                                               dyn step/current-dynamic-bindings]
                                           (and dyn (contains? dyn sym)))
                                         #?(:clj (clojure.core/thread-bound? v)
                                            :cljs false)))
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
                               #?(:clj (var-set v val)
                                  :cljs (throw (ex-info "var-set not supported for host vars in CLJS" {:type :sci/error})))))
                      :meta {:name 'var-set :doc #?(:clj (:doc (meta #'clojure.core/var-set)) :cljs (existing-doc (symbol "clojure.core" "var-set")))}}
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
                     {:val eval-fn :meta {:name 'eval :doc #?(:clj (:doc (meta #'clojure.core/eval)) :cljs "Evaluates the form data structure and returns the result.")}}
                     (symbol "clojure.core" "macroexpand-1")
                     {:val (make-macroexpand-1-fn heap-atom) :meta {:name 'macroexpand-1}}
                     (symbol "clojure.core" "macroexpand")
                     {:val (fn sci-macroexpand [form]
                             (let [me1-fn (:val (get @heap-atom (symbol "clojure.core" "macroexpand-1")))]
                               (loop [f form]
                                 (let [expanded (me1-fn f)]
                                   (if (= expanded f) f (recur expanded))))))
                      :meta {:name 'macroexpand :doc #?(:clj (:doc (meta #'clojure.core/macroexpand)) :cljs "Repeatedly calls macroexpand-1 on form until it no longer represents a macro form, then returns it.")}}
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
                                         #?(:clj (clojure.core/bound? v)
                                            :cljs false)))
                                     vars))
                      :meta {:name 'bound?}}
                     (symbol "clojure.core" "intern")
                     {:val (make-intern-fn heap-atom) :meta {:name 'intern}}
                     (symbol "clojure.core" "find-ns")
                     {:val (make-find-ns-fn ctx) :meta {:name 'find-ns :doc #?(:clj (:doc (meta #'clojure.core/find-ns)) :cljs "Returns the namespace named by the symbol or nil if it doesn't exist.")}}
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
                     {:val ns-vars-fn :meta {:name 'ns-publics :doc #?(:clj (:doc (meta #'clojure.core/ns-publics)) :cljs "Returns a map of the public intern mappings for the namespace.")}}
                     (symbol "clojure.core" "ns-interns")
                     {:val ns-vars-fn :meta {:name 'ns-interns}}
                     (symbol "clojure.core" "*clojure-version*")
                     {:val #?(:clj {:major (:major *clojure-version*)
                                    :minor (:minor *clojure-version*)
                                    :incremental (:incremental *clojure-version*)
                                    :qualifier "SCI"}
                              :cljs {:major 0 :minor 0 :incremental 0 :qualifier "SCI"})
                      :meta {:name '*clojure-version*}
                      :dynamic? true}
                     (symbol "clojure.core" "clojure-version")
                     {:val (fn [] #?(:clj (clojure.core/str (:major *clojure-version*) "."
                                                            (:minor *clojure-version*) "."
                                                            (:incremental *clojure-version*) "-SCI")
                                     :cljs "0.0.0-SCI"))
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
                     {:val (make-ns-unalias-fn ctx) :meta {:name 'ns-unalias :doc #?(:clj (:doc (meta #'clojure.core/ns-unalias)) :cljs (existing-doc (symbol "clojure.core" "ns-unalias")))}}
                     (symbol "clojure.core" "ns-unmap")
                     {:val (fn [ns-sym sym]
                             (let [ns-sym (if (instance? sci.lang.Namespace ns-sym) (:name ns-sym) ns-sym)
                                   qualified (symbol (str ns-sym) (str sym))]
                               (swap! heap-atom dissoc qualified)
                              ;; Also remove from imports, types, refers in ns-atom
                              ;; and track in :unmapped so syntax-quote resolver knows
                               (when-let [ns-atom (:ns-atom ctx)]
                                 (swap! ns-atom (fn [ns-table]
                                                  (-> ns-table
                                                      (update-in [ns-sym :imports] dissoc sym)
                                                      (update-in [ns-sym :types] dissoc sym)
                                                      (update-in [ns-sym :refers] dissoc sym)
                                                      (update-in [ns-sym :unmapped] (fnil conj #{}) sym)))))
                               nil))
                      :meta {:name 'ns-unmap :doc #?(:clj (:doc (meta #'clojure.core/ns-unmap)) :cljs "Removes the mappings for the symbol from the namespace.")}}
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
                      :meta {:name 'ns-imports :doc #?(:clj (:doc (meta #'clojure.core/ns-imports)) :cljs (existing-doc (symbol "clojure.core" "ns-imports")))}}
                     (symbol "clojure.core" "remove-ns")
                     {:val (make-remove-ns-fn ctx heap-atom) :meta {:name 'remove-ns :doc #?(:clj (:doc (meta #'clojure.core/remove-ns)) :cljs (existing-doc (symbol "clojure.core" "remove-ns")))}}
                     (symbol "clojure.core" "find-var")
                     {:val (make-find-var-fn ctx heap-atom) :meta {:name 'find-var :doc #?(:clj (:doc (meta #'clojure.core/find-var)) :cljs (existing-doc (symbol "clojure.core" "find-var")))}}
                     (symbol "clojure.core" "refer")
                     {:val (make-refer-fn ctx heap-atom) :meta {:name 'refer :doc #?(:clj (:doc (meta #'clojure.core/refer)) :cljs (existing-doc (symbol "clojure.core" "refer")))}}
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
                      :meta {:name 'require :doc #?(:clj (:doc (meta #'clojure.core/require)) :cljs (existing-doc (symbol "clojure.core" "require")))}}
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
                     (symbol "clojure.repl" "dir")
                     {:val (fn [sci-dir-nsname]
                             (let [heap @heap-atom
                                   ns-str (str sci-dir-nsname)
                                   matching (sort (keep (fn [[k _]]
                                                          (let [ks (str k)]
                                                            (when (and (qualified-symbol? k)
                                                                       (= ns-str (clojure.core/namespace k)))
                                                              (symbol (clojure.core/name k)))))
                                                        heap))]
                               (when (empty? matching)
                                 (throw (ex-info (str "No namespace '" ns-str "' found")
                                                 {:type :sci/error})))
                               (list 'do
                                     (cons 'do (map (fn [s] (list 'println (list 'quote s))) matching))
                                     nil)))
                      :meta {:macro true :name 'dir
                             :doc "Prints a sorted directory of public vars in a namespace"}
                      :macro? true}
                     (symbol "clojure.repl" "apropos")
                     {:val (fn [str-or-pattern]
                             (let [re (re-pattern (str str-or-pattern))
                                   heap @heap-atom]
                               (sort (keep (fn [[k _]]
                                             (when (and (qualified-symbol? k)
                                                        (re-find re (str k)))
                                               k))
                                           heap))))
                      :meta {:name 'apropos
                             :doc "Given a regular expression or stringable thing, return a seq of all public definitions in all currently-loaded namespaces that match the str_or_pattern."}}
                     (symbol "clojure.repl" "dir-fn")
                     {:val (fn [ns-sym]
                             (let [heap @heap-atom
                                   ns-str (str ns-sym)]
                               (sort (keep (fn [[k _]]
                                             (when (and (qualified-symbol? k)
                                                        (= ns-str (clojure.core/namespace k)))
                                               (symbol (clojure.core/name k))))
                                           heap))))
                      :meta {:name 'dir-fn
                             :doc "Returns a sorted seq of symbols naming public vars in a namespace"}}
                     (symbol "clojure.repl" "source-fn")
                     {:val (fn [_] nil) :meta {:name 'source-fn}}
                     ;; clojure.walk/macroexpand-all — uses SCI's macroexpand
                     (symbol "clojure.walk" "macroexpand-all")
                     {:val (fn sci-macroexpand-all [form]
                             (let [me1-fn (:val (get @heap-atom (symbol "clojure.core" "macroexpand-1")))]
                               (clojure.walk/prewalk
                                (fn [x]
                                  (if (seq? x)
                                    (loop [f x]
                                      (let [expanded (me1-fn f)]
                                        (if (= expanded f) f (recur expanded))))
                                    x))
                                form)))
                      :meta {:name 'macroexpand-all
                             :doc "Recursively performs all possible macroexpansions in form."}}
                     (symbol "clojure.core" "load-string")
                     {:val (make-load-string-fn ctx heap-atom) :meta {:name 'load-string}}
                     (symbol "clojure.core" "read-string")
                     {:val (let [sci-tag-reader (fn [tag]
                                                ;; Look up SCI record constructor for tagged literal like #foo.A{...}
                                                  (let [tag-str (str tag)
                                                        idx #?(:clj (.lastIndexOf ^String tag-str ".")
                                                               :cljs (.lastIndexOf tag-str "."))]
                                                    (when (> idx 0)
                                                      (let [ns-str (subs tag-str 0 idx)
                                                            type-str (subs tag-str (inc idx))
                                                            map-ctor-sym (symbol ns-str (str "map->" type-str))
                                                            entry (get @heap-atom map-ctor-sym)]
                                                        (when entry (:val entry))))))]
                             (fn sci-read-string
                               ([s]
                                (let [suppress? #?(:clj *suppress-read* :cljs nil)
                                      re-val    #?(:clj (or *read-eval* @read-eval) :cljs @read-eval)
                                      default-fn #?(:clj *default-data-reader-fn* :cljs nil)
                                      resolver  #?(:clj *reader-resolver* :cljs nil)
                                      opts (cond-> (assoc (make-reader-opts) :location? (constantly false))
                                             suppress? (assoc :suppress-read true)
                                             re-val    (assoc :read-eval clojure.core/eval)
                                             true (assoc :readers
                                                         #?(:clj (fn [tag]
                                                                   (or (get clojure.core/default-data-readers tag)
                                                                       (sci-tag-reader tag)
                                                                       (when default-fn (fn [val] (default-fn tag val)))))
                                                            :cljs (fn [tag]
                                                                    (cond
                                                                      (= 'js tag)
                                                                      (fn [v]
                                                                        (if (map? v)
                                                                          (apply list 'js-obj
                                                                                 (mapcat (fn [[k val]]
                                                                                           [(if (keyword? k) (name k) (str k)) val])
                                                                                         v))
                                                                          (apply list 'array (seq v))))
                                                                      (= 'queue tag)
                                                                      (fn [v] (into cljs.core/PersistentQueue.EMPTY v))
                                                                      :else (sci-tag-reader tag)))))
                                             resolver  (assoc :auto-resolve
                                                              #?(:clj (fn [alias]
                                                                        (if (= alias :current)
                                                                          (.currentNS ^clojure.lang.LispReader$Resolver resolver)
                                                                          (.resolveAlias ^clojure.lang.LispReader$Resolver resolver alias)))
                                                                 :cljs nil)))]
                                  (edamame/parse-string s opts)))
                               ([opts s]
                                (let [eof-val   (:eof opts ::none)
                                      suppress? #?(:clj *suppress-read* :cljs nil)
                                      re-val    #?(:clj (or *read-eval* @read-eval) :cljs @read-eval)
                                      default-fn #?(:clj *default-data-reader-fn* :cljs nil)
                                      resolver  #?(:clj *reader-resolver* :cljs nil)
                                      reader-opts (cond-> (merge (assoc (make-reader-opts) :location? (constantly false))
                                                                 (dissoc opts :eof))
                                                    suppress? (assoc :suppress-read true)
                                                    re-val    (assoc :read-eval clojure.core/eval)
                                                    true (assoc :readers
                                                                #?(:clj (fn [tag]
                                                                          (or (get clojure.core/default-data-readers tag)
                                                                              (sci-tag-reader tag)
                                                                              (when default-fn (fn [val] (default-fn tag val)))))
                                                                   :cljs nil))
                                                    resolver  (assoc :auto-resolve
                                                                     #?(:clj (fn [alias]
                                                                               (if (= alias :current)
                                                                                 (.currentNS ^clojure.lang.LispReader$Resolver resolver)
                                                                                 (.resolveAlias ^clojure.lang.LispReader$Resolver resolver alias)))
                                                                        :cljs nil)))
                                      result (try
                                               (edamame/parse-string s reader-opts)
                                               (catch #?(:clj Exception :cljs :default) e
                                                 (if (and (not= eof-val ::none)
                                                          (re-find #"EOF" (str (ex-message e))))
                                                   eof-val
                                                   (throw e))))]
                                  (if (and (nil? result)
                                           (not= eof-val ::none)
                                           (clojure.string/blank? s))
                                    eof-val
                                    result)))))
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
                    ;; empty — return nil for SCI deftypes (not records), like Clojure
                    (symbol "clojure.core" "empty")
                    {:val (fn [coll]
                            (let [m (clojure.core/meta coll)]
                              (if (and m (:type m) (instance? sci.lang.Type (:type m))
                                       (not (:sci.impl/record m)))
                                nil  ;; deftype instances have no empty collection
                                (clojure.core/empty coll))))
                     :meta {:name 'empty}}
                    ;; hash — dispatch to hashCode override for SCI deftypes
                    (symbol "clojure.core" "hash")
                    {:val (fn [x]
                            (if-let [type-obj (when-let [m (clojure.core/meta x)]
                                                (when (instance? sci.lang.Type (:type m))
                                                  (:type m)))]
                              (if-let [hash-fn (get (type-methods type-obj) 'hashCode)]
                                (hash-fn x)
                                (clojure.core/hash x))
                              (clojure.core/hash x)))
                     :meta {:name 'hash}}
                    ;; = — records of different types must not be equal
                    (symbol "clojure.core" "=")
                    {:val (fn sci-equals
                            ([] true)
                            ([x] true)
                            ([x y]
                             (let [xm (clojure.core/meta x)
                                   ym (clojure.core/meta y)]
                               (if (or (:sci.impl/record xm) (:sci.impl/record ym))
                                 ;; At least one is a record — types must match
                                 (and (= (:type xm) (:type ym))
                                      (clojure.core/= x y))
                                 (clojure.core/= x y))))
                            ([x y & more]
                             (if (sci-equals x y)
                               (if (next more)
                                 (recur y (first more) (next more))
                                 (sci-equals y (first more)))
                               false)))
                     :meta {:name '=}}
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
                    ;; str override is now in sci.vm.host (default-heap) so it survives freeze/thaw
                    #?@(:clj
                        [;; aset — coerce values for primitive arrays
                         (symbol "clojure.core" "aset")
                         {:val (fn
                                 ([array idx val]
                                  (let [comp-type (.getComponentType (class array))]
                                    (if (and comp-type (.isPrimitive ^Class comp-type))
                                      (do (java.lang.reflect.Array/set
                                           array idx
                                           (condp = comp-type
                                             Integer/TYPE (int val)
                                             Long/TYPE (long val)
                                             Double/TYPE (double val)
                                             Float/TYPE (float val)
                                             Short/TYPE (short val)
                                             Byte/TYPE (byte val)
                                             Boolean/TYPE (boolean val)
                                             Character/TYPE (char val)
                                             val))
                                          val)
                                      (do (clojure.core/aset ^"[Ljava.lang.Object;" array idx val)
                                          val))))
                                 ([array idx idx2 & idxv]
                                  (apply (fn [a i v] (clojure.core/aset a i v))
                                         (clojure.core/aget array idx) idx2 idxv)))
                          :meta {:name 'aset}}])
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
                     :meta {:name 'with-meta :doc #?(:clj (:doc (meta #'clojure.core/with-meta)) :cljs (existing-doc (symbol "clojure.core" "with-meta")))}}
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
                     :meta {:name 'vary-meta :doc #?(:clj (:doc (meta #'clojure.core/vary-meta)) :cljs (existing-doc (symbol "clojure.core" "vary-meta")))}}
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
                     :meta {:name 'meta :doc #?(:clj (:doc (meta #'clojure.core/meta)) :cljs (existing-doc (symbol "clojure.core" "meta")))}}
                    ;; dissoc — handle SCI records: removing basis fields downgrades to plain map
                    (symbol "clojure.core" "dissoc")
                    (let [dissoc1 (fn [m k]
                                    (let [md (clojure.core/meta m)
                                          result (clojure.core/dissoc m k)]
                                      (if (and md (:sci.impl/record md))
                                        (let [type-obj (:type md)
                                              basis-fields (when (instance? sci.lang.Type type-obj)
                                                             (set (map keyword (.-fields ^sci.lang.Type type-obj))))]
                                          (if (and basis-fields (contains? basis-fields k))
                                            (with-meta result (dissoc md :type :sci.impl/record))
                                            result))
                                        result)))]
                      {:val (fn
                              ([m] m)
                              ([m k] (dissoc1 m k))
                              ([m k & ks] (reduce dissoc1 (dissoc1 m k) ks)))
                       :meta {:name 'dissoc}})
                    ;; pr-str — handle SCI records and vars, with recursive collection traversal
                    (symbol "clojure.core" "pr-str")
                    {:val (let [get-custom-pm (fn [type-obj]
                                                #?(:clj
                                                   (when (instance? sci.lang.Type type-obj)
                                                     (let [pm-entry (get @heap-atom (symbol "clojure.core" "print-method"))
                                                           pm (:val pm-entry)]
                                                       (when (instance? clojure.lang.MultiFn pm)
                                                         (let [method-table (.getMethodTable ^clojure.lang.MultiFn pm)]
                                                           (get method-table type-obj)))))
                                                   :cljs
                                                   (when (instance? sci.lang.Type type-obj)
                                                     (or
                                                      ;; Inline protocol implementation (deftype/defrecord/reify)
                                                      (let [methods (type-methods type-obj)]
                                                        (or (get methods '-pr-writer)
                                                            (get methods (symbol "-pr-writer"))))
                                                      ;; Extended via extend-protocol/extend-type
                                                      (let [ipw-entry (get @heap-atom (symbol "clojure.core" "IPrintWithWriter"))]
                                                        (when (and ipw-entry (= :sci/protocol (:type (:val ipw-entry))))
                                                          (let [impls @(:impls (:val ipw-entry))
                                                                impl (get impls type-obj)]
                                                            (or (get impl '-pr-writer)
                                                                (get impl (symbol "-pr-writer"))))))))))]
                            (fn sci-pr [& args]
                              (letfn [(meta-prefix [x s]
                                        (if (and *print-meta*
                                                 (instance? clojure.lang.IMeta x)
                                                 (seq (clojure.core/meta x))
                                                 (not (:sci.impl/record (clojure.core/meta x)))
                                                 (not (instance? sci.lang.Type (:type (clojure.core/meta x)))))
                                          (str "^" (pr1 (clojure.core/meta x)) " " s)
                                          s))
                                      (pr1 [x]
                                        (let [m (clojure.core/meta x)
                                              type-obj (when m (:type m))
                                              custom-pm-fn (get-custom-pm type-obj)]
                                          (cond
                                            ;; Custom print-method/IPrintWithWriter for this SCI type
                                            custom-pm-fn
                                            #?(:clj
                                               (let [sw (java.io.StringWriter.)]
                                                 (custom-pm-fn x sw)
                                                 (str sw))
                                               :cljs
                                               (let [sb (volatile! "")
                                                     writer (reify
                                                              IWriter
                                                              (-write [_ s] (vswap! sb str s))
                                                              (-flush [_]))]
                                                 (custom-pm-fn x writer nil)
                                                 @sb))
                                            ;; SCI record — print as #ns.Name{...}
                                            (and m (:sci.impl/record m))
                                            (let [type-name (when (instance? sci.lang.Type type-obj)
                                                              (type-name type-obj))]
                                              (str "#" type-name "{" (clojure.string/join ", " (map (fn [[k v]] (str (pr1 k) " " (pr1 v))) (sort-by key x))) "}"))
                                            ;; SCI deftype (non-record) — print as #object[ns.Name]
                                            (instance? sci.lang.Type type-obj)
                                            (str "#object[" (type-name type-obj) "]")
                                            ;; SCI Var — print as #'ns/name
                                            (instance? sci.lang.Var x) (str "#'" (or (:sci.impl/var-sym (.-meta-map ^sci.lang.Var x)) (.-sym ^sci.lang.Var x)))
                                            ;; Collections — recursive traversal to catch SCI types inside
                                            (vector? x) (meta-prefix x (str "[" (clojure.string/join " " (map pr1 x)) "]"))
                                            (set? x) (meta-prefix x (str "#{" (clojure.string/join " " (map pr1 (sort x))) "}"))
                                            (map? x) (meta-prefix x (str "{" (clojure.string/join ", " (map (fn [[k v]] (str (pr1 k) " " (pr1 v))) x)) "}"))
                                            (seq? x) (meta-prefix x (str "(" (clojure.string/join " " (map pr1 x)) ")"))
                                            :else (clojure.core/pr-str x))))]
                                (clojure.string/join " " (map pr1 args)))))
                     :meta {:name 'pr-str}}
                    ;; pr — print using SCI-aware formatting to *out*
                    (symbol "clojure.core" "pr")
                    {:val (fn [& args]
                            (let [pr-str-fn (:val (get @heap-atom (symbol "clojure.core" "pr-str")))
                                  s (apply pr-str-fn args)]
                              #?(:clj (.write ^java.io.Writer *out* ^String s)
                                 :cljs (if-let [w @out] (-write w s) (if-let [pf @print-fn] (pf s) (when *print-fn* (*print-fn* s)))))))
                     :meta {:name 'pr :doc #?(:clj (:doc (meta #'clojure.core/pr)) :cljs (existing-doc (symbol "clojure.core" "pr")))}}
                    ;; prn — pr followed by newline
                    (symbol "clojure.core" "prn")
                    {:val (fn [& args]
                            (let [pr-fn (:val (get @heap-atom (symbol "clojure.core" "pr")))]
                              (apply pr-fn args)
                              #?(:clj (do (.write ^java.io.Writer *out* "\n")
                                          (when *flush-on-newline* (.flush ^java.io.Writer *out*)))
                                 :cljs (if-let [w @out] (-write w "\n") (if-let [pf @print-fn] (pf "\n") (when *print-fn* (*print-fn* "\n")))))))
                     :meta {:name 'prn :doc #?(:clj (:doc (meta #'clojure.core/prn)) :cljs (existing-doc (symbol "clojure.core" "prn")))}}
                    ;; print — like pr but uses print-str (human-readable)
                    (symbol "clojure.core" "print")
                    {:val (fn [& args]
                            (let [print-str-fn (:val (get @heap-atom (symbol "clojure.core" "print-str")))
                                  s (apply print-str-fn args)]
                              #?(:clj (.write ^java.io.Writer *out* ^String s)
                                 :cljs (if-let [w @out] (-write w s) (if-let [pf @print-fn] (pf s) (when *print-fn* (*print-fn* s)))))))
                     :meta {:name 'print :doc #?(:clj (:doc (meta #'clojure.core/print)) :cljs (existing-doc (symbol "clojure.core" "print")))}}
                    ;; println — print followed by newline
                    (symbol "clojure.core" "println")
                    {:val (fn [& args]
                            (let [print-fn* (:val (get @heap-atom (symbol "clojure.core" "print")))]
                              (apply print-fn* args)
                              #?(:clj (do (.write ^java.io.Writer *out* "\n")
                                          (when *flush-on-newline* (.flush ^java.io.Writer *out*)))
                                 :cljs (if-let [w @out] (-write w "\n") (if-let [pf @print-fn] (pf "\n") (when *print-fn* (*print-fn* "\n")))))))
                     :meta {:name 'println :doc #?(:clj (:doc (meta #'clojure.core/println)) :cljs (existing-doc (symbol "clojure.core" "println")))}}
                    ;; print-str — like pr-str for print-str
                    (symbol "clojure.core" "print-str")
                    {:val (fn [& args]
                            (clojure.string/join " "
                                                 (map (fn [x]
                                                        (let [m (clojure.core/meta x)]
                                                          (cond
                                                            (:sci.impl/record m)
                                                            (let [type-obj (:type m)
                                                                  type-name (when (instance? sci.lang.Type type-obj)
                                                                              (type-name type-obj))]
                                                              (str "#" type-name (into (sorted-map) (map (fn [[k v]] [k v]) x))))
                                                            (instance? sci.lang.Var x)
                                                            (let [v ^sci.lang.Var x]
                                                              (str "#'" (or (:sci.impl/var-sym (.-meta-map v)) (.-sym v))))
                                                            :else (clojure.core/print-str x))))
                                                      args)))
                     :meta {:name 'print-str}}
                    ;; class? — true for SCI types too
                    (symbol "clojure.core" "class?")
                    {:val (fn [x]
                            (or #?(:clj (clojure.core/class? x) :cljs (fn? x))
                                (instance? sci.lang.Type x)))
                     :meta {:name 'class?}}
                    ;; extends? — check SCI protocol impls for SCI types
                    (symbol "clojure.core" "extends?")
                    {:val (fn [protocol atype]
                            (if (and (map? protocol) (= :sci/protocol (:type protocol)))
                              ;; SCI protocol — check impls atom
                              (contains? @(:impls protocol) atype)
                              ;; Real protocol — atype must be a Class
                              #?(:clj (if (clojure.core/class? atype)
                                        (clojure.core/extends? protocol atype)
                                        false)
                                 :cljs false)))
                     :meta {:name 'extends? :doc #?(:clj (:doc (meta #'clojure.core/extends?)) :cljs (existing-doc (symbol "clojure.core" "extends?")))}})
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
              (:deftype-fn ctx) (assoc :deftype-fn (:deftype-fn ctx))
              (:reify-fn ctx) (assoc :reify-fn (:reify-fn ctx))
              true (as-> m' m'
                     (let [f (or (:file ctx) #?(:clj @@(clojure.core/resolve 'sci.core/file) :cljs @file))]
                       (if f (assoc m' :current-file f) m')))
                ;; Add atom-vars mapping for binding mechanism
              true (assoc :atom-vars
                          #?(:clj (let [resolve-atom (fn [s] (some-> (clojure.core/find-var s) deref))]
                                    {'clojure.core/*out*                 (resolve-atom 'sci.core/out)
                                     'clojure.core/*in*                  (resolve-atom 'sci.core/in)
                                     'clojure.core/*err*                 (resolve-atom 'sci.core/err)
                                     'clojure.core/*print-length*        (resolve-atom 'sci.core/print-length)
                                     'clojure.core/*print-namespace-maps* (resolve-atom 'sci.core/print-namespace-maps)})
                             :cljs {})))]
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
         sci-ns-val #?(:clj (some-> (clojure.core/find-var 'sci.core/ns) deref deref)
                       :cljs @ns)
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
         eof #?(:clj (Object.) :cljs (js-obj))]
     (loop [result nil]
       (let [current-ns @current-ns-atom
             ;; Get current namespace aliases for ::alias/keyword resolution
             ns-atom (or (:ns-atom ctx) (atom {}))
             ns-info (get @ns-atom current-ns)
             aliases (:aliases ns-info)
             base-opts (make-reader-opts current-ns aliases (:heap-atom ctx) ns-atom)
             ;; Compose user :readers with built-in :readers so both work
             reader-extra (if-let [user-readers (:readers reader-extra)]
                            (let [builtin-readers (:readers base-opts)]
                              (assoc reader-extra :readers
                                     (if (map? user-readers)
                                       (fn [tag]
                                         (or (get user-readers tag)
                                             (when (fn? builtin-readers) (builtin-readers tag))))
                                       user-readers)))
                            reader-extra)
             read-opts (merge base-opts reader-extra {:eof eof})
             form (edamame/parse-next reader read-opts)]
         (if (identical? form eof)
           (if (and (map? result) (= :suspend (:status result)))
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

#?(:clj
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
           (sci.lang/->Var (quote ~clj-var) val# merged-meta# (boolean (:dynamic m#))))))))

(defn copy-var*
  "Copy a Clojure var into an SCI namespace (runtime version, takes a var)."
  ([clj-var sci-ns] (copy-var* clj-var sci-ns nil))
  ([clj-var sci-ns opts]
   (let [m (meta clj-var)
         val (deref clj-var)
         merged-meta (merge m opts)]
     (sci.lang/->Var (.-sym clj-var) val merged-meta (boolean (:dynamic m))))))

#?(:clj
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
            publics#))))))

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

#?(:clj
   (def ^:private sci-var->clj-var
     "Mapping from SCI atom vars to their corresponding Clojure dynamic vars."
     {'sci.core/out       #'*out*
      'sci.core/in        #'*in*
      'sci.core/err       #'*err*
      'sci.core/print-length #'*print-length*
      'sci.core/print-namespace-maps #'*print-namespace-maps*}))

#?(:clj
   (defmacro binding
     "Dynamic binding form for SCI vars.
      Supports both real Clojure vars and SCI dynamic vars (atoms)."
     [bindings & body]
     (let [pairs (partition 2 bindings)]
       (if (:ns &env)
         ;; CLJS: simple atom save/restore (no thread bindings)
         (let [sym-pairs (mapv (fn [[target val-expr]]
                                 [(gensym "old") target val-expr])
                               pairs)]
           `(let [~@(mapcat (fn [[old-sym target _]] [old-sym `(deref ~target)]) sym-pairs)]
              ~@(mapv (fn [[_ target val-expr]] `(reset! ~target ~val-expr)) sym-pairs)
              (try
                (do ~@body)
                (finally
                  ~@(mapv (fn [[old-sym target _]] `(reset! ~target ~old-sym)) sym-pairs)))))
         ;; CLJ
         (let [;; Check at compile time if the binding targets are vars
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
                        ~@(mapv (fn [[old-sym target _]] `(reset! ~target ~old-sym)) sym-pairs))))))))))))

#?(:clj
   (defmacro with-bindings
     "Execute body with SCI var bindings. Keys must be dynamic vars (atoms from new-dynamic-var)."
     [binding-map & body]
     (let [check-expr (if (:ns &env)
                        `(or (instance? cljs.core/Atom ~'k#) (instance? sci.lang.DynamicVar ~'k#))
                        `(or (instance? clojure.lang.Atom ~'k#) (instance? sci.lang.DynamicVar ~'k#)))]
       `(let [~'bmap# ~binding-map]
          (doseq [[~'k# _#] ~'bmap#]
            (when-not ~check-expr
              (throw (ex-info (str "Cannot bind non-dynamic var: " ~'k#)
                              {:type :bind-non-dynamic}))))
          (let [~'saved# (into {} (map (fn [[v# _#]] [v# @v#]) ~'bmap#))]
            (try
              (doseq [[v# val#] ~'bmap#]
                (reset! v# val#))
              ~@body
              (finally
                (doseq [[v# old#] ~'saved#]
                  (reset! v# old#)))))))))

#?(:clj
   (defmacro with-redefs
     "Temporarily redefine vars."
     [bindings & body]
     (if (:ns &env)
       ;; CLJS: atom save/restore for SCI vars
       (let [pairs (partition 2 bindings)
             sym-pairs (mapv (fn [[target val-expr]]
                               [(gensym "old") target val-expr])
                             pairs)]
         `(let [~@(mapcat (fn [[old-sym target _]] [old-sym `(deref ~target)]) sym-pairs)]
            ~@(mapv (fn [[_ target val-expr]] `(reset! ~target ~val-expr)) sym-pairs)
            (try
              (do ~@body)
              (finally
                ~@(mapv (fn [[old-sym target _]] `(reset! ~target ~old-sym)) sym-pairs)))))
       `(clojure.core/with-redefs ~bindings ~@body))))

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
;; IO wrappers
;; ============================================================

#?(:cljs
   (defn with-out-str-fn
     "Execute f and capture all print output to a string."
     [f]
     (let [sb (volatile! "")
           old-print-fn *print-fn*
           old-print-err-fn *print-err-fn*
           old-out @out
           writer (reify
                    IWriter
                    (-write [_ s] (vswap! sb str s))
                    (-flush [_]))]
       (reset! out writer)
       (set! *print-fn* (fn [x] (vswap! sb str x)))
       (set! *print-err-fn* (fn [x] (vswap! sb str x)))
       (try
         (f)
         (finally
           (set! *print-fn* old-print-fn)
           (set! *print-err-fn* old-print-err-fn)
           (reset! out old-out)))
       @sb)))

#?(:clj
   (defmacro with-out-str [& body]
     (if (:ns &env)
       `(sci.core/with-out-str-fn (fn [] ~@body))
       `(let [sw# (java.io.StringWriter.)
              old-out# @out]
          (reset! out sw#)
          (try
            (clojure.core/binding [~'*out* sw#]
              ~@body)
            (finally
              (reset! out old-out#)))
          (str sw#)))))

#?(:clj
   (defmacro with-in-str [s & body]
     `(let [sr# (java.io.StringReader. ~s)
            old-in# @in]
        (reset! in sr#)
        (try
          (binding [*in* (clojure.java.io/reader sr#)]
            ~@body)
          (finally
            (reset! in old-in#))))))

#?(:clj
   (defmacro future [& body]
     `(clojure.core/future ~@body)))

#?(:clj
   (defmacro pmap [f & colls]
     `(clojure.core/pmap ~f ~@colls)))

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
  "Serialize a suspended or running machine to an EDN string."
  [machine]
  (vm-freeze/freeze machine))

(defn thaw
  "Deserialize an EDN string back into a live machine."
  [edn-str]
  (vm-freeze/thaw edn-str))

;; ============================================================
;; Single-step execution API
;; ============================================================

(defn prepare
  "Parse code and create a machine ready for stepping, without executing it.
   Returns a machine map with :status :running.
   opts are the same as eval-string (context options or an initialized context)."
  ([s] (prepare s nil))
  ([s opts]
   (let [ctx (if (and opts (:heap opts))
               opts
               (init (or opts {})))
         reader-extra (cond-> {}
                        (:features ctx) (assoc :features (:features ctx))
                        (:readers ctx) (assoc :readers (:readers ctx)))
         current-ns-atom (or (:current-ns-atom ctx) (atom 'user))
         current-ns @current-ns-atom
         ns-atom (or (:ns-atom ctx) (atom {}))
         ns-info (get @ns-atom current-ns)
         aliases (:aliases ns-info)
         reader (edamame/reader s)
         eof #?(:clj (Object.) :cljs (js-obj))
         read-opts (merge (make-reader-opts current-ns aliases (:heap-atom ctx) ns-atom)
                          reader-extra {:eof eof})
         forms (loop [acc []]
                 (let [form (edamame/parse-next reader read-opts)]
                   (if (identical? form eof)
                     acc
                     (recur (conj acc form)))))]
     (make-machine-from-ctx ctx forms))))

(defn step
  "Execute a single VM operation on a machine.
   Returns the updated machine. Only steps if status is :running;
   otherwise returns the machine unchanged.

   The returned machine's :status will be one of:
     :running  — more work to do, call step again
     :done     — computation finished, result in (:result machine)
     :suspend  — code called (suspend!), data in (:suspend-data machine)"
  [machine]
  (if (= :running (:status machine))
    (step/safe-step machine)
    machine))

(defn prepare-resume
  "Prepare a suspended machine for stepping again.
   Like resume, but returns the :running machine instead of running it to completion."
  ([machine] (prepare-resume machine nil))
  ([machine value]
   (machine/resume machine value)))

(defn inspect
  "Return a summary map describing a machine's current state.
   Useful for logging, debugging, or building scheduling decisions
   during stepped execution."
  [machine]
  (let [frame (machine/peek-frame machine)]
    {:status      (:status machine)
     :op          (:op frame)
     :expr        (:expr frame)
     :result      (:result machine)
     :stack-depth (count (:stack machine))
     :current-ns  (:current-ns machine)
     :env         (:env machine)
     :suspend-data (:suspend-data machine)}))
