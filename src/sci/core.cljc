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

;; ============================================================
;; Reader
;; ============================================================

(def ^:private special-forms-sq
  #{'if 'do 'let 'fn 'def 'quote 'var 'loop 'recur
    'try 'catch 'finally 'throw 'new 'set! 'monitor-enter
    'monitor-exit '& 'binding})

(defn- sq-resolve-class
  "Try to resolve sym as a Java class; returns fully-qualified symbol or nil."
  [sym]
  #?(:clj (let [resolved (clojure.core/resolve sym)]
             (when (instance? Class resolved)
               (symbol (.getName ^Class resolved))))
     :cljs nil))

(defn- make-syntax-quote-resolver
  "Returns a :resolve-symbol fn for edamame syntax-quote.
   heap-atom may be nil (for contexts without a live heap)."
  [current-ns heap-atom]
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
         ;; Host Clojure var (clojure.core etc.)
         (let [resolved #?(:clj (clojure.core/resolve sym) :cljs nil)]
           (when resolved
             (let [m (meta resolved)]
               (symbol (str (:ns m)) (str (:name m))))))
         ;; Default: qualify with current ns
         (symbol (str current-ns) sym-name))))))

(defn- make-reader-opts
  "Create edamame reader options, optionally with a current namespace for ::keyword resolution."
  ([] (make-reader-opts 'user nil nil))
  ([current-ns] (make-reader-opts current-ns nil nil))
  ([current-ns ns-aliases] (make-reader-opts current-ns ns-aliases nil))
  ([current-ns ns-aliases heap-atom]
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
    :syntax-quote {:resolve-symbol (make-syntax-quote-resolver current-ns heap-atom)}
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
                features load-fn readers deny allow file]} opts
        heap (host/default-heap)
        ns-table (host/default-ns-table)
        ;; Override satisfies? to handle SCI protocols
        heap (assoc heap (symbol "clojure.core" "satisfies?")
                    {:val (fn sci-satisfies? [protocol x]
                            (if (and (map? protocol) (= :sci/protocol (:type protocol)))
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
                              ;; Fall back to clojure.core/satisfies? for real protocols
                              (clojure.core/satisfies? protocol x)))
                     :meta {:name 'satisfies?}
                     :dynamic? false})
        ;; Install user bindings into heap as user/sym vars
        heap (reduce-kv
              (fn [h sym val]
                (let [sym-name (if (symbol? sym) (name sym) (str sym))
                      qualified (symbol "user" sym-name)
                      ;; Unwrap sci.lang.Var (from copy-var) to get actual value + meta
                      sci-var? (instance? sci.lang.Var val)
                      actual-val (if sci-var? @val val)
                      vm (meta val)
                      is-macro? (or (:macro vm) (:sci/macro vm))
                      is-dynamic? (or (boolean (:dynamic? val))
                                      (boolean (:dynamic vm)))]
                  (assoc h qualified (cond-> {:val actual-val
                                              :meta (or vm {})
                                              :macro? (boolean is-macro?)
                                              :dynamic? is-dynamic?}
                                       is-macro? (assoc :host-macro? true)))))
              heap
              (or bindings {}))
        ;; Install custom namespaces
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
                                                   :dynamic? is-dynamic?}
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
     :current-ns-atom (atom 'user)
     :classes (or classes {})
     :features (or features #{:clj})
     :load-fn load-fn
     :readers readers
     :ns-aliases ns-aliases
     :deny deny
     :allow allow
     :file file}))

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
    (let [m2 (machine/make-machine {:heap        @heap-atom
                                    :ns-table    (:ns-table ctx)
                                    :permissions {:allow (:allow ctx)
                                                  :deny  (:deny ctx)}})
          m2 (assoc m2 :heap-atom heap-atom)
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
        (let [result (atom nil)]
          (swap! heap-atom
                 (fn [h]
                   (let [entry   (get h sym)
                         old-val (:val entry)
                         new-val (apply f old-val args)]
                     (reset! result new-val)
                     (assoc h sym (assoc entry :val new-val)))))
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
           (let [method       (symbol (subs n 1))
                 [_ obj & args] form]
             (list* '. obj method args))

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
                 (if (var? mv)
                   (apply mf form {} (rest form))
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

(defn- make-ns-map-fn [heap-atom]
  (fn [ns-sym]
    (let [heap   @heap-atom
          ns-str (str ns-sym)]
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
                 {} heap))))

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

(defn- make-find-ns-fn [ctx]
  (fn [sym]
    (let [ns-data (if-let [a (:ns-atom ctx)] @a (:ns-table ctx))
          ns-info (get ns-data sym)]
      (when ns-info
        (let [ns-meta (dissoc ns-info :aliases :refers :imports)]
          (if (seq ns-meta) (with-meta sym ns-meta) sym))))))

(defn- make-the-ns-fn [ctx]
  (fn [sym]
    (let [ns-data (if-let [a (:ns-atom ctx)] @a (:ns-table ctx))
          ns-info (get ns-data sym)]
      (if ns-info
        (let [ns-meta (dissoc ns-info :aliases :refers :imports)]
          (if (seq ns-meta) (with-meta sym ns-meta) sym))
        (throw (ex-info (str "No namespace: " sym " found") {:type :sci/error}))))))

(defn- make-create-ns-fn [ctx]
  (fn [sym]
    (let [sym (if (string? sym) (symbol sym) sym)]
      (when-let [a (:ns-atom ctx)]
        (swap! a (fn [ns-table]
                   (if (get ns-table sym)
                     ns-table
                     (assoc ns-table sym {:aliases {} :refers {} :imports {}})))))
      sym)))

(defn- make-all-ns-fn [ctx]
  (fn []
    (let [ns-data (if-let [a (:ns-atom ctx)] @a (:ns-table ctx))]
      (keys ns-data))))

(defn- make-load-string-fn [ctx heap-atom]
  (fn sci-load-string [s]
    (let [forms (read-all s)
          expr  (if (= 1 (count forms)) (first forms) (cons 'do forms))
          m2    (-> (machine/make-machine {:heap        @heap-atom
                                           :ns-table    (:ns-table ctx)
                                           :permissions {:allow (:allow ctx)
                                                         :deny  (:deny ctx)}})
                    (assoc :heap-atom heap-atom)
                    (machine/push-frame {:op :eval :expr expr}))]
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
  (fn [alias-sym ns-sym]
    (when-let [a (:ns-atom ctx)]
      (let [current-ns (if-let [cna (:current-ns-atom ctx)] @cna 'user)]
        (swap! a update-in [current-ns :aliases] assoc alias-sym ns-sym)))
    nil))

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

(defn- make-refer-fn [heap-atom]
  (fn sci-refer
    ([ns-sym] (sci-refer ns-sym :only nil))
    ([ns-sym & filters]
     (let [opts         (apply hash-map filters)
           only-syms    (:only opts)
           exclude-syms (set (:exclude opts))
           heap         @heap-atom
           ns-str       (str ns-sym)
           entries      (filter (fn [[k _]] (= ns-str (namespace k))) heap)
           current-ns   'user]
       (doseq [[k entry] entries]
         (let [sym-name (symbol (name k))]
           (when (and (or (nil? only-syms) (contains? (set only-syms) sym-name))
                      (not (contains? exclude-syms sym-name)))
             (swap! heap-atom assoc (symbol (str current-ns) (str sym-name)) entry))))
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
        entry
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
  (fn [name-sym fields & specs]
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
  (fn [name-sym fields & specs]
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
                                    dyn @step/current-dynamic-bindings]
                                (if (and dyn (contains? dyn sym))
                                  (get dyn sym)
                                  (let [entry (get @heap-atom sym)]
                                    (if entry (:val entry) (.-val ^sci.lang.Var v)))))
                              (var-get v)))
                     :meta {:name 'var-get}}
                    (symbol "clojure.core" "thread-bound?")
                    {:val (fn sci-thread-bound? [& vars]
                            (every? (fn [v]
                                      (if (instance? sci.lang.Var v)
                                        (let [sym (var-qualified-sym v)
                                              dyn @step/current-dynamic-bindings]
                                          (and dyn (contains? dyn sym)))
                                        (clojure.core/thread-bound? v)))
                                    vars))
                     :meta {:name 'thread-bound?}}
                    (symbol "clojure.core" "var-set")
                    {:val (fn sci-var-set [v val]
                            (if (instance? sci.lang.Var v)
                              (let [sym (var-qualified-sym v)
                                    dyn @step/current-dynamic-bindings]
                                (if (and dyn (contains? dyn sym))
                                  ;; Update dynamic binding
                                  (do (swap! step/current-dynamic-bindings assoc sym val)
                                      val)
                                  ;; Update heap
                                  (let [entry (assoc (get @heap-atom sym) :val val)]
                                    (swap! heap-atom assoc sym entry)
                                    val)))
                              (var-set v val)))
                     :meta {:name 'var-set}}
                    (symbol "clojure.core" "with-redefs-fn")
                    {:val (make-with-redefs-fn heap-atom) :meta {:name 'with-redefs-fn}}
                    (symbol "clojure.core" "alter-var-root")
                    {:val (make-alter-var-root-fn heap-atom) :meta {:name 'alter-var-root}}
                    (symbol "clojure.core" "meta")
                    {:val (fn sci-meta [obj]
                            (let [m (meta obj)]
                              (cond
                                (:sci/closure m)
                                (let [cleaned (dissoc m :sci/closure :type :name :ns :arities :env)]
                                  (when (seq cleaned) cleaned))
                                (:sci.impl/var-sym m) (dissoc m :sci.impl/var-sym)
                                :else m)))
                     :meta {:name 'meta}}
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
                    {:val eval-fn :meta {:name 'eval}}
                    (symbol "clojure.core" "macroexpand-1")
                    {:val (make-macroexpand-1-fn heap-atom) :meta {:name 'macroexpand-1}}
                    (symbol "clojure.core" "macroexpand")
                    {:val (fn sci-macroexpand [form]
                            (let [me1-fn (:val (get @heap-atom (symbol "clojure.core" "macroexpand-1")))]
                              (loop [f form]
                                (let [expanded (me1-fn f)]
                                  (if (= expanded f) f (recur expanded))))))
                     :meta {:name 'macroexpand}}
                    (symbol "clojure.core" "bound?")
                    {:val (fn [& vars]
                            (every? (fn [v]
                                      (if (instance? sci.lang.Var v)
                                        (let [sym   (var-qualified-sym v)
                                              entry (get @heap-atom sym)
                                              dyn   @step/current-dynamic-bindings]
                                          (or (:bound? entry)
                                              (and dyn (contains? dyn sym))
                                              (some? (.-val ^sci.lang.Var v))))
                                        (clojure.core/bound? v)))
                                    vars))
                     :meta {:name 'bound?}}
                    (symbol "clojure.core" "intern")
                    {:val (make-intern-fn heap-atom) :meta {:name 'intern}}
                    (symbol "clojure.core" "find-ns")
                    {:val (make-find-ns-fn ctx) :meta {:name 'find-ns}}
                    (symbol "clojure.core" "create-ns")
                    {:val (make-create-ns-fn ctx) :meta {:name 'create-ns}}
                    (symbol "clojure.core" "the-ns")
                    {:val (make-the-ns-fn ctx) :meta {:name 'the-ns}}
                    (symbol "clojure.core" "ns-name")
                    {:val (fn [ns-sym]
                            (cond
                              (symbol? ns-sym) ns-sym
                              (string? ns-sym) (symbol ns-sym)
                              :else (clojure.core/ns-name ns-sym)))
                     :meta {:name 'ns-name}}
                    (symbol "clojure.core" "all-ns")
                    {:val (make-all-ns-fn ctx) :meta {:name 'all-ns}}
                    (symbol "clojure.core" "ns-publics")
                    {:val ns-vars-fn :meta {:name 'ns-publics}}
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
                    {:val (make-ns-map-fn heap-atom) :meta {:name 'ns-map}}
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
                    {:val (make-ns-unalias-fn ctx) :meta {:name 'ns-unalias}}
                    (symbol "clojure.core" "ns-unmap")
                    {:val (fn [ns-sym sym]
                            (let [qualified (symbol (str ns-sym) (str sym))]
                              (swap! heap-atom dissoc qualified)
                              nil))
                     :meta {:name 'ns-unmap}}
                    (symbol "clojure.core" "ns-imports")
                    {:val (fn [ns-sym]
                            {}) ;; TODO: track imports properly
                     :meta {:name 'ns-imports}}
                    (symbol "clojure.core" "remove-ns")
                    {:val (make-remove-ns-fn ctx heap-atom) :meta {:name 'remove-ns}}
                    (symbol "clojure.core" "find-var")
                    {:val (make-find-var-fn ctx heap-atom) :meta {:name 'find-var}}
                    (symbol "clojure.core" "refer")
                    {:val (make-refer-fn heap-atom) :meta {:name 'refer}}
                    (symbol "clojure.core" "ns-aliases")
                    {:val (fn [ns-sym] (or (:aliases (get (:ns-table ctx) ns-sym)) {}))
                     :meta {:name 'ns-aliases}}
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
                             (let [default-fn (or (when *suppress-read*
                                                    (fn [tag val] (tagged-literal tag val)))
                                                  (when-let [f *default-data-reader-fn*]
                                                    (fn [tag val] (f tag val))))
                                   opts (cond-> (assoc (make-reader-opts)
                                                       :location? (constantly false))
                                          default-fn (assoc :default default-fn))]
                               (edamame/parse-string s opts)))
                            ([opts s]
                             (let [eof-val (:eof opts ::none)
                                   ;; Pick up dynamic vars from thread bindings
                                   default-fn (or (when *suppress-read*
                                                    (fn [tag val] (tagged-literal tag val)))
                                                  (when-let [f *default-data-reader-fn*]
                                                    (fn [tag val] (f tag val))))
                                   reader-opts (cond-> (merge (assoc (make-reader-opts)
                                                                     :location? (constantly false))
                                                              (dissoc opts :eof))
                                                 default-fn (assoc :default default-fn))
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
                     :meta {:name 'read-string}}}
        ns-atom (or (:ns-atom ctx) (atom (:ns-table ctx)))
        ;; Override ns-aliases to read from ns-atom
        heap (assoc (merge @heap-atom extra-heap)
                    (symbol "clojure.core" "ns-aliases")
                    {:val (fn [ns-sym] (or (:aliases (get @ns-atom ns-sym)) {}))
                     :meta {:name 'ns-aliases}}
                    (symbol "clojure.core" "defrecord")
                    {:val (make-defrecord-fn ctx)
                     :meta {:macro true :name 'defrecord}
                     :macro? true}
                    (symbol "clojure.core" "deftype")
                    {:val (make-deftype-fn ctx)
                     :meta {:macro true :name 'deftype}
                     :macro? true}
                    ;; instance? — check SCI types too
                    (symbol "clojure.core" "instance?")
                    {:val (fn [cls obj]
                            (if (instance? sci.lang.Type cls)
                              ;; SCI type — check :type metadata
                              (= cls (:type (clojure.core/meta obj)))
                              ;; Host class
                              (clojure.core/instance? cls obj)))
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
                    ;; class? — true for SCI types too
                    (symbol "clojure.core" "class?")
                    {:val (fn [x]
                            (or (clojure.core/class? x)
                                (instance? sci.lang.Type x)))
                     :meta {:name 'class?}})
        m (machine/make-machine
           {:heap heap
            :ns-table @ns-atom
            :permissions {:allow (:allow ctx)
                          :deny (:deny ctx)}})]
    (let [expr (if (= 1 (count forms))
                 (first forms)
                 (cons 'do forms))
          current-ns-atom (or (:current-ns-atom ctx) (atom 'user))
          m (cond-> (assoc m :heap-atom heap-atom :ns-atom ns-atom
                             :current-ns-atom current-ns-atom
                             :current-ns @current-ns-atom)
                (:load-fn ctx) (assoc :load-fn (:load-fn ctx))
                (:ns-aliases ctx) (assoc :ns-aliases (:ns-aliases ctx))
                true (as-> m' m'
                      (let [f (or (:file ctx) @(clojure.core/resolve 'sci.core/file))]
                        (if f (assoc m' :current-file f) m'))))]
      (reset! heap-atom heap)
      (machine/push-frame m {:op :eval :expr expr}))))

(defn eval-string
  "Evaluate a string of Clojure code."
  ([s] (eval-string s nil))
  ([s opts]
   (let [ctx (if (and opts (:heap opts))
               opts  ;; already initialized
               (init (or opts {})))
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
             read-opts (merge (make-reader-opts current-ns aliases (:heap-atom ctx)) reader-extra {:eof eof})
             form (edamame/parse-next reader read-opts)]
         (if (identical? form eof)
           (if (and (map? result) (contains? #{:suspend :effect} (:status result)))
             result  ;; Return suspended machine as-is
             result)
           (let [machine (make-machine-from-ctx ctx [form])
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
  "Create a source reader from a string."
  [s]
  (reader s))

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
  "Create a new dynamic SCI var."
  ([name] (new-dynamic-var name nil nil))
  ([name init-val] (new-dynamic-var name init-val nil))
  ([name init-val opts]
   (atom init-val)))

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
  "Execute body with SCI var bindings."
  [binding-map & body]
  `(do ~@body))

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
  `(clojure.core/with-out-str ~@body))

(defmacro with-in-str [s & body]
  `(clojure.core/with-in-str ~s ~@body))

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
    (->> st
         (filter :line) ;; only entries with source locations
         (mapv (fn [{:keys [ns name line column file]}]
                 (let [ns-str (str (or ns "user"))
                       name-str (if name (str ns-str "/" name) (str ns-str))
                       file-str (or file "NO_SOURCE_PATH")]
                   (format "%-18s - %s:%s:%s" name-str file-str line column)))))))

;; ============================================================
;; set! for dynamic vars
;; ============================================================

(defn set!
  "Set a dynamic var's value."
  [v val]
  (if (instance? #?(:clj clojure.lang.Atom :cljs Atom) v)
    (reset! v val)
    val))

;; resolve is defined at the bottom of the file

;; ============================================================
;; EOF sentinel
;; ============================================================

(def eof ::eof)

(defn parse-next+string
  "Parse the next form from a reader, returning [form string]."
  [ctx rdr]
  (let [col-before (edamame/get-column-number rdr)
        form (parse-next ctx rdr)
        col-after (edamame/get-column-number rdr)]
    ;; Return [form source-string]
    ;; Note: exact source string reconstruction is limited
    [form (pr-str form)]))

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
