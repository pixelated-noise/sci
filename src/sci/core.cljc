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
  ([s] (read-all s 'user))
  ([s current-ns]
   (edamame/parse-string-all s (make-reader-opts current-ns))))

;; ============================================================
;; Context / init
;; ============================================================

(defn init
  "Create an SCI context (the machine's initial state)."
  [opts]
  (let [{:keys [bindings namespaces classes aliases imports
                features load-fn readers deny allow]} opts
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
     :ns-table ns-table
     :classes (or classes {})
     :features (or features #{:clj})
     :load-fn load-fn
     :readers readers
     :deny deny
     :allow allow}))

(defn fork
  "Create a fork of a context — an independent copy."
  [ctx]
  (update ctx :heap #(or % {})))

;; ============================================================
;; Evaluation
;; ============================================================

(defn- make-machine-from-ctx
  "Create a fresh machine from a context and a list of forms."
  [ctx forms]
  (let [heap-atom (atom (:heap ctx))
        ;; Inject VM-aware functions that need heap access
        resolve-fn (fn sci-resolve
                     ([sym] (sci-resolve 'user sym))
                     ([ns-sym sym]
                      (let [heap @heap-atom
                            qualified (symbol (str ns-sym) (str sym))
                            core-q (symbol "clojure.core" (str sym))
                            entry (or (get heap qualified) (get heap core-q))]
                        (when entry
                          (sci.lang/->Var (or (when (get heap qualified) qualified) core-q)
                                         (:val entry)
                                         (merge (:meta entry) {:name sym :ns (symbol (str ns-sym))})
                                         (:dynamic? entry))))))
        eval-fn (fn sci-eval [form]
                  (let [m2 (machine/make-machine {:heap @heap-atom
                                                   :ns-table (:ns-table ctx)
                                                   :permissions {:allow (:allow ctx)
                                                                  :deny (:deny ctx)}})
                        m2 (assoc m2 :heap-atom heap-atom)
                        m2 (machine/push-frame m2 {:op :eval :expr form})]
                    (step/run m2)))
        extra-heap {(symbol "clojure.core" "var?")
                    {:val (fn sci-var? [x]
                            (or (var? x) (instance? sci.lang.Var x)))
                     :meta {:name 'var?}}
                    (symbol "clojure.core" "var-get")
                    {:val (fn sci-var-get [v]
                            (if (instance? sci.lang.Var v)
                              ;; Get latest value from heap-atom
                              (let [sym (.-sym ^sci.lang.Var v)
                                    entry (get @heap-atom sym)]
                                (if entry (:val entry) (.-val ^sci.lang.Var v)))
                              (var-get v)))
                     :meta {:name 'var-get}}
                    (symbol "clojure.core" "thread-bound?")
                    {:val (fn sci-thread-bound? [& vars]
                            ;; For SCI vars, check if they have dynamic bindings in the VM
                            ;; This is a best-effort since we don't have the machine context
                            (every? (fn [v]
                                      (if (instance? sci.lang.Var v)
                                        ;; SCI vars are considered bound if they have a value
                                        (some? (.-val ^sci.lang.Var v))
                                        (clojure.core/thread-bound? v)))
                                    vars))
                     :meta {:name 'thread-bound?}}
                    (symbol "clojure.core" "var-set")
                    {:val (fn sci-var-set [v val]
                            (if (instance? sci.lang.Var v)
                              (let [sym (.-sym ^sci.lang.Var v)
                                    entry (assoc (get @heap-atom sym) :val val)]
                                (swap! heap-atom assoc sym entry)
                                val)
                              (var-set v val)))
                     :meta {:name 'var-set}}
                    (symbol "clojure.core" "with-redefs-fn")
                    {:val (fn sci-with-redefs-fn [binding-map func]
                            (let [sci-bindings (filter (fn [[v _]] (instance? sci.lang.Var v)) binding-map)
                                  clj-bindings (remove (fn [[v _]] (instance? sci.lang.Var v)) binding-map)
                                  ;; Save old values for SCI vars
                                  old-vals (into {} (map (fn [[v _]]
                                                           (let [sym (.-sym ^sci.lang.Var v)]
                                                             [sym (:val (get @heap-atom sym))]))
                                                         sci-bindings))]
                              ;; Set new values
                              (doseq [[v new-val] sci-bindings]
                                (let [sym (.-sym ^sci.lang.Var v)
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
                              (let [sym (.-sym ^sci.lang.Var v)
                                    old-val (.-val ^sci.lang.Var v)
                                    new-val (apply f old-val args)
                                    entry {:val new-val
                                           :meta (.-meta-map ^sci.lang.Var v)
                                           :dynamic? (.-dynamic? ^sci.lang.Var v)}]
                                (swap! heap-atom assoc sym entry)
                                new-val)
                              (apply clojure.core/alter-var-root v f args)))
                     :meta {:name 'alter-var-root}}
                    (symbol "clojure.core" "alter-meta!")
                    {:val (fn sci-alter-meta! [ref f & args]
                            (if (instance? sci.lang.Var ref)
                              (let [sym (.-sym ^sci.lang.Var ref)
                                    old-meta (.-meta-map ^sci.lang.Var ref)
                                    new-meta (apply f old-meta args)
                                    entry (get @heap-atom sym)]
                                (swap! heap-atom assoc sym (assoc entry :meta new-meta))
                                new-meta)
                              (apply clojure.core/alter-meta! ref f args)))
                     :meta {:name 'alter-meta!}}
                    (symbol "clojure.core" "reset-meta!")
                    {:val (fn sci-reset-meta! [ref m]
                            (if (instance? sci.lang.Var ref)
                              (let [sym (.-sym ^sci.lang.Var ref)
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
                             (if (and (seq? form) (symbol? (first form)))
                               (let [head (first form)
                                     heap @heap-atom
                                     sym-name (name head)
                                     sym-ns (clojure.core/namespace head)
                                     candidates (if sym-ns
                                                  [(symbol sym-ns sym-name)]
                                                  [(symbol "user" sym-name)
                                                   (symbol "clojure.core" sym-name)])
                                     macro-entry (some #(let [e (get heap %)]
                                                          (when (:macro? e) e))
                                                       candidates)]
                                 (if macro-entry
                                   (let [mv (:val macro-entry)
                                         mf (if (var? mv) @mv mv)]
                                     (if (var? mv)
                                       (apply mf form {} (rest form))
                                       (apply mf (rest form))))
                                   form))
                               form))
                            ([env form]
                             (sci-macroexpand-1 form)))
                     :meta {:name 'macroexpand-1}}
                    (symbol "clojure.core" "bound?")
                    {:val (fn [& vars]
                            (every? (fn [v]
                                      (if (instance? sci.lang.Var v)
                                        (let [sym (.-sym ^sci.lang.Var v)
                                              entry (get @heap-atom sym)]
                                          (if entry
                                            (:bound? entry true)
                                            (some? (.-val ^sci.lang.Var v))))
                                        (clojure.core/bound? v)))
                                    vars))
                     :meta {:name 'bound?}}
                    (symbol "clojure.core" "intern")
                    {:val (fn
                            ([ns-sym name-sym]
                             (let [qualified (symbol (str ns-sym) (str name-sym))
                                   entry {:val nil :meta {} :dynamic? false}]
                               (swap! heap-atom assoc qualified entry)
                               (sci.lang/->Var qualified nil {:name name-sym :ns ns-sym} false)))
                            ([ns-sym name-sym val]
                             (let [qualified (symbol (str ns-sym) (str name-sym))
                                   entry {:val val :meta {} :dynamic? false}]
                               (swap! heap-atom assoc qualified entry)
                               (sci.lang/->Var qualified val {:name name-sym :ns ns-sym} false))))
                     :meta {:name 'intern}}
                    (symbol "clojure.core" "find-ns")
                    {:val (fn [sym] (when (get (:ns-table ctx) sym) sym))
                     :meta {:name 'find-ns}}
                    (symbol "clojure.core" "create-ns")
                    {:val (fn [sym] sym)
                     :meta {:name 'create-ns}}
                    (symbol "clojure.core" "the-ns")
                    {:val (fn [sym]
                            (or (when (get (:ns-table ctx) sym) sym)
                                (throw (ex-info (str "No namespace: " sym " found")
                                               {:type :sci/error}))))
                     :meta {:name 'the-ns}}
                    (symbol "clojure.core" "ns-name")
                    {:val (fn [ns-sym] (if (symbol? ns-sym) ns-sym (clojure.core/ns-name ns-sym)))
                     :meta {:name 'ns-name}}
                    (symbol "clojure.core" "all-ns")
                    {:val (fn [] (keys (:ns-table ctx)))
                     :meta {:name 'all-ns}}
                    (symbol "clojure.core" "ns-publics")
                    {:val (fn [ns-sym]
                            (let [heap @heap-atom
                                  ns-str (str ns-sym)]
                              (reduce-kv (fn [m k v]
                                           (if (= ns-str (namespace k))
                                             (assoc m (symbol (name k))
                                                    (sci.lang/->Var k (:val v) (:meta v) (:dynamic? v)))
                                             m))
                                         {} heap)))
                     :meta {:name 'ns-publics}}
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
                              (reduce-kv (fn [m k v]
                                           (if (= ns-str (namespace k))
                                             (assoc m (symbol (name k))
                                                    (sci.lang/->Var k (:val v) (:meta v) (:dynamic? v)))
                                             m))
                                         {} heap)))
                     :meta {:name 'ns-map}}
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
                    (symbol "clojure.core" "find-var")
                    {:val (fn [sym]
                            (when-not (qualified-symbol? sym)
                              (throw (ex-info "Symbol must be namespace-qualified"
                                              {:type :sci/error})))
                            (let [entry (get @heap-atom sym)]
                              (when entry
                                (sci.lang/->Var sym (:val entry) (:meta entry) (:dynamic? entry)))))
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
        ns-atom (atom (:ns-table ctx))
        ;; Override ns-aliases to read from ns-atom
        heap (assoc (merge (:heap ctx) extra-heap)
                    (symbol "clojure.core" "ns-aliases")
                    {:val (fn [ns-sym] (or (:aliases (get @ns-atom ns-sym)) {}))
                     :meta {:name 'ns-aliases}})
        m (machine/make-machine
           {:heap heap
            :ns-table (:ns-table ctx)
            :permissions {:allow (:allow ctx)
                          :deny (:deny ctx)}})]
    (let [expr (if (= 1 (count forms))
                 (first forms)
                 (cons 'do forms))
          m (assoc m :heap-atom heap-atom :ns-atom ns-atom)]
      (reset! heap-atom heap)
      (machine/push-frame m {:op :eval :expr expr}))))

(defn eval-string
  "Evaluate a string of Clojure code."
  ([s] (eval-string s nil))
  ([s opts]
   (let [ctx (if (and opts (:heap opts))
               opts  ;; already initialized
               (init (or opts {})))
         ;; Read all forms at once (syntax-quote resolved at read time)
         ;; For now, use a single read pass. Per-form reading with ns tracking
         ;; would be needed for full syntax-quote ns support across ns changes.
         forms (read-all s)
         machine (make-machine-from-ctx ctx forms)]
     (step/run machine))))

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
  ctx)

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
  (merge ctx opts))

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
    (var? v) (let [m (meta v)] (symbol (str (:ns m)) (str (:name m))))
    :else nil))

(defn eval-string+
  "Like eval-string but returns a map with :val and :ns."
  ([ctx s] (eval-string+ ctx s nil))
  ([ctx s opts]
   (let [use-ctx (if-let [ns-val (:ns opts)]
                   ctx ;; TODO: switch namespace
                   ctx)
         result (eval-string s use-ctx)]
     {:val result
      :ns (or (:ns opts) 'user)})))

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
