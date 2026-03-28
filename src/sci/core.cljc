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

(defn- make-reader-opts
  "Create edamame reader options, optionally with a current namespace for ::keyword resolution."
  ([] (make-reader-opts 'user))
  ([current-ns]
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
    :syntax-quote {:resolve-symbol
                    (fn [sym]
                      (if (or (namespace sym)
                              (contains? #{'if 'do 'let 'fn 'def 'quote 'var 'loop 'recur
                                           'try 'catch 'finally 'throw 'new 'set! 'monitor-enter
                                           'monitor-exit '& 'binding} sym)
                              ;; Don't qualify special symbols
                              (.contains (str sym) "."))
                        sym
                        ;; Check if it resolves in clojure.core
                        (let [core-var (clojure.core/resolve sym)]
                          (if core-var
                            (let [m (meta core-var)]
                              (symbol (str (:ns m)) (str (:name m))))
                            ;; Qualify with current namespace
                            (symbol (str current-ns) (str sym))))))}
    :var true
    :deref true
    :regex true
    :auto-resolve {:current (or current-ns 'user)}}))

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
                      qualified (symbol "user" sym-name)]
                  (assoc h qualified {:val val
                                      :meta {}
                                      :dynamic? true})))
              heap
              (or bindings {}))
        ;; Install custom namespaces
        heap (reduce-kv
              (fn [h ns-sym ns-map]
                (reduce-kv
                 (fn [h2 sym val]
                   (let [sym-name (if (symbol? sym) (name sym) (str sym))
                         qualified (symbol (str ns-sym) sym-name)]
                     (assoc h2 qualified {:val val
                                          :meta {}
                                          :dynamic? false})))
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

(defn- make-machine-from-ctx
  "Create a fresh machine from a context and a list of forms."
  [ctx forms]
  (let [heap-atom (or (:heap-atom ctx) (atom (:heap ctx)))
        ;; Inject VM-aware functions that need heap access
        resolve-fn (fn sci-resolve
                     ([sym] (sci-resolve 'user sym))
                     ([ns-sym sym]
                      (let [heap @heap-atom
                            ;; Handle already-qualified symbols
                            [qualified core-q]
                            (if (qualified-symbol? sym)
                              [sym nil]
                              [(symbol (str ns-sym) (str sym))
                               (symbol "clojure.core" (str sym))])
                            entry (or (get heap qualified) (when core-q (get heap core-q)))]
                        (when entry
                          (let [found-key (if (get heap qualified) qualified core-q)]
                            (sci.lang/->Var (symbol (name found-key))
                                           (:val entry)
                                           (assoc (:meta entry)
                                                  :name (symbol (name found-key))
                                                  :ns (symbol (namespace found-key))
                                                  :sci.impl/var-sym found-key)
                                           (:dynamic? entry)))))))
        eval-fn (fn sci-eval [form]
                  (let [m2 (machine/make-machine {:heap @heap-atom
                                                   :ns-table (:ns-table ctx)
                                                   :permissions {:allow (:allow ctx)
                                                                  :deny (:deny ctx)}})
                        m2 (assoc m2 :heap-atom heap-atom)
                        m2 (machine/push-frame m2 {:op :eval :expr form})]
                    (step/run m2)))
        extra-heap {(symbol "clojure.core" "symbol")
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
                    {:val (fn sci-with-redefs-fn [binding-map func]
                            (let [sci-bindings (filter (fn [[v _]] (instance? sci.lang.Var v)) binding-map)
                                  clj-bindings (remove (fn [[v _]] (instance? sci.lang.Var v)) binding-map)
                                  ;; Save old values for SCI vars
                                  old-vals (into {} (map (fn [[v _]]
                                                           (let [sym (var-qualified-sym v)]
                                                             [sym (:val (get @heap-atom sym))]))
                                                         sci-bindings))]
                              ;; Set new values
                              (doseq [[v new-val] sci-bindings]
                                (let [sym (var-qualified-sym v)
                                      entry (assoc (get @heap-atom sym) :val new-val)]
                                  (swap! heap-atom assoc sym entry)))
                              (try
                                (if (seq clj-bindings)
                                  (with-redefs-fn (into {} clj-bindings) func)
                                  (func))
                                (finally
                                  ;; Restore old values
                                  (doseq [[sym old-val] old-vals]
                                    (let [entry (assoc (get @heap-atom sym) :val old-val)]
                                      (swap! heap-atom assoc sym entry)))))))
                     :meta {:name 'with-redefs-fn}}
                    (symbol "clojure.core" "alter-var-root")
                    {:val (fn sci-alter-var-root [v f & args]
                            (if (instance? sci.lang.Var v)
                              (let [sym (var-qualified-sym v)
                                    result (atom nil)]
                                ;; Atomic read-modify-write in single swap!
                                (swap! heap-atom
                                       (fn [h]
                                         (let [entry (get h sym)
                                               old-val (:val entry)
                                               new-val (apply f old-val args)]
                                           (reset! result new-val)
                                           (assoc h sym (assoc entry :val new-val)))))
                                @result)
                              (apply clojure.core/alter-var-root v f args)))
                     :meta {:name 'alter-var-root}}
                    (symbol "clojure.core" "meta")
                    {:val (fn sci-meta [obj]
                            (let [m (meta obj)]
                              (cond
                                (:sci/closure m)
                                (let [cleaned (dissoc m :sci/closure :type :name :ns :arities :env)]
                                  (when (seq cleaned) cleaned))
                                ;; Strip internal SCI keys from var/other metadata
                                (:sci.impl/var-sym m)
                                (dissoc m :sci.impl/var-sym)
                                :else m)))
                     :meta {:name 'meta}}
                    (symbol "clojure.core" "alter-meta!")
                    {:val (fn sci-alter-meta! [ref f & args]
                            (if (instance? sci.lang.Var ref)
                              (let [qualified (var-qualified-sym ref)
                                    old-meta (.-meta-map ^sci.lang.Var ref)
                                    new-meta (apply f old-meta args)
                                    entry (get @heap-atom qualified)]
                                (swap! heap-atom assoc qualified (assoc entry :meta new-meta))
                                new-meta)
                              (apply clojure.core/alter-meta! ref f args)))
                     :meta {:name 'alter-meta!}}
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
                    {:val (fn sci-macroexpand-1
                            ([form]
                             (if-not (and (seq? form) (symbol? (first form)))
                               form
                               (let [head (first form)
                                     n (name head)]
                                 (cond
                                   ;; .method sugar → (. obj method args...)
                                   (and #?(:clj (.startsWith ^String n ".")
                                           :cljs (= "." (subs n 0 1)))
                                        (not= n "..")
                                        (> (count n) 1))
                                   (let [method (symbol (subs n 1))
                                         [_ obj & args] form]
                                     (list* '. obj method args))

                                   ;; Constructor. sugar → (new ClassName args...)
                                   (and #?(:clj (.endsWith ^String n ".")
                                           :cljs (= "." (subs n (dec (count n)))))
                                        (not= n "..")
                                        (> (count n) 1))
                                   (let [class-name (symbol (subs n 0 (dec (count n))))]
                                     (list* 'new class-name (rest form)))

                                   ;; Macro expansion
                                   :else
                                   (let [heap @heap-atom
                                         sym-ns (clojure.core/namespace head)
                                         candidates (if sym-ns
                                                      [(symbol sym-ns n)]
                                                      [(symbol "user" n)
                                                       (symbol "clojure.core" n)])
                                         macro-entry (some #(let [e (get heap %)]
                                                              (when (:macro? e) e))
                                                           candidates)]
                                     (if macro-entry
                                       (let [mv (:val macro-entry)
                                             mf (if (var? mv) @mv mv)]
                                         (if (var? mv)
                                           (apply mf form {} (rest form))
                                           (apply mf (rest form))))
                                       form))))))
                            ([env form]
                             ;; If the head symbol is in the env, don't expand
                             (if (and (seq? form) (symbol? (first form))
                                      (contains? env (first form)))
                               form
                               (sci-macroexpand-1 form))))
                     :meta {:name 'macroexpand-1}}
                    (symbol "clojure.core" "macroexpand")
                    {:val (fn sci-macroexpand [form]
                            (let [me1-fn (:val (get @heap-atom (symbol "clojure.core" "macroexpand-1")))]
                              (loop [f form]
                                (let [expanded (me1-fn f)]
                                  (if (= expanded f)
                                    f
                                    (recur expanded))))))
                     :meta {:name 'macroexpand}}
                    (symbol "clojure.core" "bound?")
                    {:val (fn [& vars]
                            (every? (fn [v]
                                      (if (instance? sci.lang.Var v)
                                        (let [sym (var-qualified-sym v)
                                              entry (get @heap-atom sym)
                                              dyn @step/current-dynamic-bindings]
                                          (or (:bound? entry)
                                              ;; Check if currently dynamically bound
                                              (and dyn (contains? dyn sym))
                                              ;; Fallback: check val directly
                                              (some? (.-val ^sci.lang.Var v))))
                                        (clojure.core/bound? v)))
                                    vars))
                     :meta {:name 'bound?}}
                    (symbol "clojure.core" "intern")
                    {:val (fn
                            ([ns-sym name-sym]
                             (let [qualified (symbol (str ns-sym) (str name-sym))
                                   existing (get @heap-atom qualified)
                                   name-meta (meta name-sym)
                                   entry (if existing
                                           (update existing :meta merge name-meta)
                                           {:val nil :meta (or name-meta {}) :dynamic? false :bound? false})]
                               (swap! heap-atom assoc qualified entry)
                               (sci.lang/->Var (symbol (str name-sym)) (:val entry)
                                               (assoc (:meta entry) :name name-sym :ns ns-sym
                                                      :sci.impl/var-sym qualified)
                                               (:dynamic? entry))))
                            ([ns-sym name-sym val]
                             (let [qualified (symbol (str ns-sym) (str name-sym))
                                   existing (get @heap-atom qualified)
                                   name-meta (meta name-sym)
                                   entry (if existing
                                           (-> existing (assoc :val val) (update :meta merge name-meta))
                                           {:val val :meta (or name-meta {}) :dynamic? false})]
                               (swap! heap-atom assoc qualified entry)
                               (sci.lang/->Var (symbol (str name-sym)) val
                                               (assoc (:meta entry) :name name-sym :ns ns-sym
                                                      :sci.impl/var-sym qualified)
                                               (:dynamic? entry)))))
                     :meta {:name 'intern}}
                    (symbol "clojure.core" "find-ns")
                    {:val (fn [sym]
                            (let [ns-data (if-let [a (:ns-atom ctx)] @a (:ns-table ctx))
                                  ns-info (get ns-data sym)]
                              (when ns-info
                                ;; Return symbol with namespace metadata
                                (let [ns-meta (dissoc ns-info :aliases :refers :imports)]
                                  (if (seq ns-meta)
                                    (with-meta sym ns-meta)
                                    sym)))))
                     :meta {:name 'find-ns}}
                    (symbol "clojure.core" "create-ns")
                    {:val (fn [sym]
                            ;; Create namespace if it doesn't exist
                            (let [sym (if (string? sym) (symbol sym) sym)]
                              (when-let [a (:ns-atom ctx)]
                                (swap! a (fn [ns-table]
                                           (if (get ns-table sym)
                                             ns-table
                                             (assoc ns-table sym {:aliases {} :refers {} :imports {}})))))
                              sym))
                     :meta {:name 'create-ns}}
                    (symbol "clojure.core" "the-ns")
                    {:val (fn [sym]
                            (let [ns-data (if-let [a (:ns-atom ctx)] @a (:ns-table ctx))
                                  ns-info (get ns-data sym)]
                              (if ns-info
                                (let [ns-meta (dissoc ns-info :aliases :refers :imports)]
                                  (if (seq ns-meta)
                                    (with-meta sym ns-meta)
                                    sym))
                                (throw (ex-info (str "No namespace: " sym " found")
                                                {:type :sci/error})))))
                     :meta {:name 'the-ns}}
                    (symbol "clojure.core" "ns-name")
                    {:val (fn [ns-sym]
                            (cond
                              (symbol? ns-sym) ns-sym
                              (string? ns-sym) (symbol ns-sym)
                              :else (clojure.core/ns-name ns-sym)))
                     :meta {:name 'ns-name}}
                    (symbol "clojure.core" "all-ns")
                    {:val (fn [] (let [ns-data (if-let [a (:ns-atom ctx)] @a (:ns-table ctx))]
                                   (keys ns-data)))
                     :meta {:name 'all-ns}}
                    (symbol "clojure.core" "ns-publics")
                    {:val (fn [ns-sym]
                            (let [heap @heap-atom
                                  ns-str (str ns-sym)]
                              (reduce-kv (fn [m k v]
                                           (if (= ns-str (namespace k))
                                             (let [var-meta (merge {:name (symbol (name k))
                                                                    :ns (symbol (namespace k))}
                                                                   (:meta v)
                                                                   {:sci.impl/var-sym k})]
                                               (assoc m (symbol (name k))
                                                      (sci.lang/->Var (symbol (name k)) (:val v) var-meta (:dynamic? v))))
                                             m))
                                         {} heap)))
                     :meta {:name 'ns-publics}}
                    (symbol "clojure.core" "ns-interns")
                    {:val (fn [ns-sym]
                            ;; In SCI, ns-interns is the same as ns-publics
                            (let [heap @heap-atom
                                  ns-str (str ns-sym)]
                              (reduce-kv (fn [m k v]
                                           (if (= ns-str (namespace k))
                                             (let [var-meta (merge {:name (symbol (name k))
                                                                    :ns (symbol (namespace k))}
                                                                   (:meta v)
                                                                   {:sci.impl/var-sym k})]
                                               (assoc m (symbol (name k))
                                                      (sci.lang/->Var (symbol (name k)) (:val v) var-meta (:dynamic? v))))
                                             m))
                                         {} heap)))
                     :meta {:name 'ns-interns}}
                    (symbol "clojure.core" "*clojure-version*")
                    {:val {:major (:major *clojure-version*)
                           :minor (:minor *clojure-version*)
                           :incremental (:incremental *clojure-version*)
                           :qualifier "SCI"}
                     :meta {:name '*clojure-version*}
                     :dynamic? true}
                    (symbol "clojure.core" "clojure-version")
                    {:val (fn [] (str (:major *clojure-version*) "."
                                      (:minor *clojure-version*) "."
                                      (:incremental *clojure-version*) "-SCI"))
                     :meta {:name 'clojure-version}}
                    (symbol "clojure.core" "ns-map")
                    {:val (fn [ns-sym]
                            (let [heap @heap-atom
                                  ns-str (str ns-sym)]
                              ;; Include both ns-specific and clojure.core vars
                              (reduce-kv (fn [m k v]
                                           (let [k-ns (namespace k)]
                                             (if (or (= ns-str k-ns)
                                                     (= "clojure.core" k-ns))
                                               (let [var-meta (merge {:name (symbol (name k))
                                                                      :ns (symbol (namespace k))}
                                                                     (:meta v)
                                                                     {:sci.impl/var-sym k})]
                                                 (assoc m (symbol (name k))
                                                        (sci.lang/->Var (symbol (name k)) (:val v) var-meta (:dynamic? v))))
                                               m)))
                                         {} heap)))
                     :meta {:name 'ns-map}}
                    (symbol "clojure.core" "ns-refers")
                    {:val (fn [ns-sym]
                            ;; Returns all referred vars (clojure.core + explicit refers)
                            (let [heap @heap-atom
                                  ns-str (str ns-sym)]
                              (reduce-kv (fn [m k v]
                                           (let [k-ns (namespace k)
                                                 k-name (name k)]
                                             ;; Include clojure.core vars and vars from
                                             ;; other namespaces that were referred into this ns
                                             (if (and (not= ns-str k-ns)
                                                      (or (= "clojure.core" k-ns)
                                                          ;; Check if this var appears in this ns too
                                                          ;; (from explicit refer)
                                                          (get heap (symbol ns-str k-name))))
                                               (let [var-meta (merge {:name (symbol k-name)
                                                                      :ns (symbol k-ns)}
                                                                     (:meta v)
                                                                     {:sci.impl/var-sym k})]
                                                 (assoc m (symbol k-name)
                                                        (sci.lang/->Var (symbol k-name) (:val v)
                                                                        var-meta (:dynamic? v))))
                                               m)))
                                         {} heap)))
                     :meta {:name 'ns-refers}}
                    ;; Override with-in-str to use VM binding (not host push-thread-bindings)
                    (symbol "clojure.core" "with-in-str")
                    {:val (fn sci-with-in-str [s & body]
                            (list 'let ['s__in (list 'new 'clojure.lang.LineNumberingPushbackReader
                                                     (list 'new 'java.io.StringReader s))]
                                  (list* 'binding ['*in* 's__in] body)))
                     :meta {:macro true :name 'with-in-str}
                     :macro? true}
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
                    {:val (fn [ns-sym]
                            ;; Remove namespace from ns-atom and its vars from heap
                            (when-let [a (:ns-atom ctx)]
                              (swap! a dissoc ns-sym))
                            (let [ns-str (str ns-sym)]
                              (swap! heap-atom (fn [h]
                                                 (reduce-kv (fn [acc k v]
                                                              (if (= ns-str (namespace k))
                                                                acc
                                                                (assoc acc k v)))
                                                            {} h))))
                            nil)
                     :meta {:name 'remove-ns}}
                    (symbol "clojure.core" "find-var")
                    {:val (fn [sym]
                            (when-not (qualified-symbol? sym)
                              (throw (ex-info (str "Not a qualified symbol: " sym)
                                              {:type :sci/error})))
                            ;; Check if namespace exists
                            (let [ns-sym (symbol (namespace sym))
                                  ns-data (if-let [a (:ns-atom ctx)] @a (:ns-table ctx))]
                              (when-not (get ns-data ns-sym)
                                (throw (ex-info (str "No such namespace: " ns-sym)
                                                {:type :sci/error})))
                              (let [entry (get @heap-atom sym)]
                                (when entry
                                  (sci.lang/->Var (symbol (name sym)) (:val entry)
                                                  (assoc (:meta entry) :sci.impl/var-sym sym)
                                                  (:dynamic? entry))))))
                     :meta {:name 'find-var}}
                    (symbol "clojure.core" "refer")
                    {:val (fn sci-refer
                            ([ns-sym] (sci-refer ns-sym :only nil))
                            ([ns-sym & filters]
                             (let [opts (apply hash-map filters)
                                   only-syms (:only opts)
                                   exclude-syms (set (:exclude opts))
                                   heap @heap-atom
                                   ns-str (str ns-sym)
                                   entries (filter (fn [[k _]] (= ns-str (namespace k))) heap)
                                   current-ns 'user] ;; TODO: track current-ns
                               (doseq [[k entry] entries]
                                 (let [sym-name (symbol (name k))]
                                   (when (and (or (nil? only-syms) (contains? (set only-syms) sym-name))
                                              (not (contains? exclude-syms sym-name)))
                                     (let [target (symbol (str current-ns) (str sym-name))]
                                       (swap! heap-atom assoc target entry)))))
                               nil)))
                     :meta {:name 'refer}}
                    (symbol "clojure.core" "ns-aliases")
                    {:val (fn [ns-sym]
                            (let [ns-data (get (:ns-table ctx) ns-sym)]
                              (or (:aliases ns-data) {})))
                     :meta {:name 'ns-aliases}}
                    ;; defonce — override host macro that uses .hasRoot
                    (symbol "clojure.core" "defonce")
                    {:val (fn sci-defonce [name expr]
                            (list 'do
                                  (list 'when-not (list 'resolve (list 'quote name))
                                        (list 'def name expr))
                                  (list 'var name)))
                     :meta {:macro true :name 'defonce}
                     :macro? true}
                    ;; doc — override host macro that uses host resolve
                    (symbol "clojure.repl" "doc")
                    {:val (fn sci-doc [sym-name]
                            ;; Look up at expansion time (we have heap-atom closure)
                            (let [heap @heap-atom
                                  sym-str (str sym-name)
                                  ;; Try to find as a var
                                  candidates (if (qualified-symbol? sym-name)
                                               [sym-name]
                                               [(symbol "user" sym-str)
                                                (symbol "clojure.core" sym-str)])
                                  entry (some #(get heap %) candidates)
                                  ;; Only show doc for entries with meaningful metadata
                                  ;; (not bare bindings which have empty meta)
                                  has-doc-meta? (and entry
                                                     (let [m (:meta entry)]
                                                       (or (:doc m) (:arglists m) (:name m)
                                                           (:macro m))))
                                  ns-data (when-let [na (:ns-atom ctx)]
                                            (get @na sym-name))]
                              (cond
                                has-doc-meta?
                                (list (list 'var 'clojure.repl/print-doc)
                                      (list 'meta (list 'resolve (list 'quote sym-name))))
                                ns-data
                                (list (list 'var 'clojure.repl/print-doc)
                                      (list 'quote {:name sym-name :doc (:doc ns-data)}))
                                :else nil)))
                     :meta {:macro true :name 'doc :doc "Prints documentation for a var or special form given its name,\n   or for a spec if given a keyword"}
                     :macro? true}
                    ;; find-doc — override host version that uses host ns-publics
                    (symbol "clojure.repl" "find-doc")
                    {:val (fn sci-find-doc [re-string-or-pattern]
                            (let [re (re-pattern re-string-or-pattern)
                                  heap @heap-atom
                                  matches (->> heap
                                               (filter (fn [[_ entry]]
                                                         (let [m (:meta entry)]
                                                           (and m (or (when-let [d (:doc m)]
                                                                        (re-find re d))
                                                                      (re-find re (str (:name m))))))))
                                               (sort-by first))]
                              (doseq [[qualified-sym entry] matches]
                                ;; Format name as ns/name without using ns-name
                                (let [m (merge (dissoc (:meta entry) :ns)
                                               {:name qualified-sym})]
                                  (#'clojure.repl/print-doc m)))
                              ;; Also check namespace docs
                              (when-let [ns-data @(or (:ns-atom ctx) (atom {}))]
                                (doseq [[ns-sym ns-info] (sort-by first ns-data)]
                                  (when-let [doc-str (:doc ns-info)]
                                    (when (re-find re doc-str)
                                      (#'clojure.repl/print-doc
                                       {:name ns-sym :doc doc-str})))))))
                     :meta {:name 'find-doc :doc "Prints documentation for any var whose documentation or name\n contains a match for re-string-or-pattern"}}
                    ;; source-fn — SCI doesn't have source for user or host fns
                    (symbol "clojure.repl" "source-fn")
                    {:val (fn [sym] nil)
                     :meta {:name 'source-fn}}
                    (symbol "clojure.core" "load-string")
                    {:val (fn sci-load-string [s]
                            (let [forms (read-all s)
                                  m2 (machine/make-machine
                                      {:heap @heap-atom
                                       :ns-table (:ns-table ctx)
                                       :permissions {:allow (:allow ctx)
                                                     :deny (:deny ctx)}})
                                  expr (if (= 1 (count forms))
                                         (first forms)
                                         (cons 'do forms))
                                  m2 (-> m2
                                         (assoc :heap-atom heap-atom)
                                         (machine/push-frame {:op :eval :expr expr}))]
                              (step/run m2)))
                     :meta {:name 'load-string}}
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
                     :meta {:name 'ns-aliases}})
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
             read-opts (merge (make-reader-opts current-ns) reader-extra {:eof eof})
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
  ;; Return an atom wrapping position + string for sequential reads
  (atom {:source s :pos 0}))

(defn source-reader
  "Create a source reader from a string."
  [s]
  (reader s))

(defn parse-next
  "Parse the next form from a reader."
  [ctx rdr]
  (let [state @rdr
        remaining (subs (:source state) (:pos state))]
    (if (empty? (clojure.string/trim remaining))
      ::eof
      (let [form (edamame/parse-string remaining
                                        {:all true
                                         :read-cond :allow
                                         :features #{:clj}
                                         :fn true
                                         :quote true
                                         :var true
                                         :deref true
                                         :regex true})]
        ;; Advance position (approximate — find end of first form)
        (swap! rdr assoc :pos (count (:source state)))
        form))))

(defn get-line-number [rdr]
  1)

(defn get-column-number [rdr]
  1)

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
            val# (deref v#)]
        (with-meta (if (:macro m#)
                     val#
                     (fn [& args#] (apply val# args#)))
          (merge m# ~opts-expr))))))

(defn copy-var*
  "Copy a Clojure var into an SCI namespace (runtime version, takes a var)."
  ([clj-var sci-ns] (copy-var* clj-var sci-ns nil))
  ([clj-var sci-ns opts]
   (let [m (meta clj-var)
         val (deref clj-var)]
     (with-meta (if (:macro m)
                  val
                  (fn [& args] (apply val args)))
       (merge m opts)))))

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
  "Parse the next form from a reader, returning both the form and the string."
  [ctx rdr]
  (let [form (parse-next ctx rdr)]
    {:val form
     :string (pr-str form)}))

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
