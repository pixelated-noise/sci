(ns sci.vm.step
  "The step function — heart of the VM. Each step processes one frame."
  (:require [sci.vm.machine :as m]
            [sci.vm.host :as host]
            [sci.lang]
            [clojure.string]
            [edamame.core :as edamame]))

(declare match-arity bind-params run check-permission form-location do-extend)

;; Thread-local dynamic bindings for closures called from host code (e.g. via map).
;; Using a dynamic var ensures each thread (future/test) has isolated bindings.
(def ^:dynamic current-dynamic-bindings nil)

;; Thread-local: most recent form location seen in step-eval (line/column map or nil).
;; Updated before each form is processed so the exception handler can report the correct
;; call-site location even when the exception is thrown inside the same step.
(def ^:dynamic *current-form-loc* nil)

;; ============================================================
;; Helpers
;; ============================================================

(defn- cond->*
  "Like cond-> but evaluates the threading form."
  [m pred f & args]
  (if pred (apply f m args) m))

;; ============================================================
;; Special forms set
;; ============================================================

(def special-forms
  '#{if do let* fn* def quote var loop* recur try
     throw set! new . defmacro case* import*
     ns in-ns require letfn* binding
     defmulti defmethod remove-method prefer-method
     defprotocol extend extend-type extend-protocol
     deftype* reify* monitor-enter monitor-exit
     suspend!})

;; ============================================================
;; Form classification
;; ============================================================

(defn classify-form [form]
  (cond
    (nil? form)     :literal
    (number? form)  :literal
    (string? form)  :literal
    (keyword? form) :literal
    #?@(:clj  [(instance? Boolean form) :literal]
        :cljs [(boolean? form) :literal])
    #?@(:clj  [(char? form) :literal])
    (symbol? form)  :symbol
    (vector? form)  :vector
    #?@(:clj [(record? form) :literal])
    (map? form)     :map
    (set? form)     :set
    (seq? form)
    (let [head (first form)]
      (cond
        (and (symbol? head)
             (or (contains? special-forms head)
                 ;; Handle qualified special forms like clojure.core/import*
                 (contains? special-forms (symbol (name head))))) :special
        ;; .method instance calls
        (and (symbol? head)
             (let [n (name head)]
               (and #?(:clj (.startsWith ^String n ".")
                       :cljs (= "." (subs n 0 1)))
                    (not= n "..")
                    (> (count n) 1)))) :dot-call
        ;; ClassName. constructor call (but not .. which is a macro)
        (and (symbol? head)
             (let [n (name head)]
               (and #?(:clj (.endsWith ^String n ".")
                       :cljs (= "." (subs n (dec (count n)))))
                    (not= n "..")))) :new-call
        :else :invoke))
    :else :literal))

;; ============================================================
;; Symbol resolution
;; ============================================================

#?(:clj
   (def ^:private class-prefixes
     ["java.lang." "java.math." "java.util." "java.io." "java.net."
      "java.util.concurrent." "java.util.regex." "clojure.lang."])

   :cljs nil)

#?(:clj
   (defn- try-resolve-class
     "Try to resolve a class name string. Returns the Class or nil."
     [class-name]
     (try
       (Class/forName class-name)
       (catch ClassNotFoundException _
         (loop [prefixes class-prefixes]
           (when (seq prefixes)
             (or (try (Class/forName (str (first prefixes) class-name))
                      (catch ClassNotFoundException _ nil))
                 (recur (rest prefixes)))))))))

#?(:clj
   (defn- check-class-access
     "Check if a class is allowed by the :classes sandbox config.
      Throws if not allowed."
     [machine class-name klass]
     (let [classes (:classes machine)]
       (when (some? classes)
         (let [allowed (or (= :all classes)
                           (= :all (:allow classes))
                           (contains? classes (symbol class-name))
                           (contains? classes klass)
                           (and (map? classes)
                                (or (contains? classes (symbol class-name))
                                    (contains? classes klass))))]
           (when-not allowed
             (throw (ex-info (str class-name " is not allowed!")
                             {:type :sci/error}))))))))

#?(:clj
   (defn- resolve-static-member
     "Resolve ClassName/member — returns the static field value or a wrapper fn for static methods.
      Also handles Clojure 1.12 ClassName/.method and ClassName/new."
     [klass member-name]
     (cond
       ;; Clojure 1.12: ClassName/.method — returns instance method as fn
       (.startsWith ^String member-name ".")
       (let [method-name (subs member-name 1)]
         (fn [target & args]
           (clojure.lang.Reflector/invokeInstanceMethod
            target method-name (to-array args))))

       ;; Clojure 1.12: ClassName/new — returns constructor as fn
       (= "new" member-name)
       (fn [& args]
         (clojure.lang.Reflector/invokeConstructor klass (to-array args)))

       :else
       ;; Try static field first
       (try
         (clojure.lang.Reflector/getStaticField klass member-name)
         (catch Exception _
           ;; Try as zero-arg static method call (Clojure semantics:
           ;; Class/method resolves as a zero-arg call, not a fn reference)
           (try
             (clojure.lang.Reflector/invokeStaticMethod
              klass member-name (to-array []))
             (catch Exception e
               ;; Check if ANY static method with this name exists — if so, wrap as fn
               ;; Otherwise, throw (the member truly doesn't exist)
               (let [methods (.getMethods ^Class klass)]
                 (if (some #(and (java.lang.reflect.Modifier/isStatic (.getModifiers ^java.lang.reflect.Method %))
                                 (= member-name (.getName ^java.lang.reflect.Method %)))
                           methods)
                   ;; Method exists but needs args — return wrapper fn
                   (fn [& args]
                     (clojure.lang.Reflector/invokeStaticMethod
                      klass member-name (to-array args)))
                   ;; No such static member at all
                   (throw e))))))))))

(defn resolve-symbol [machine sym]
  (let [env (:env machine)]
    (if (contains? env sym)
      (get env sym)
      (let [sym-name (name sym)]
        ;; Special handling for *ns*
        (if (= sym-name "*ns*")
          (let [ns-sym (:current-ns machine)
                ns-info (get-in machine [:ns ns-sym])
                ns-meta (dissoc ns-info :aliases :refers :imports :types :refer-clojure-excludes)]
            (if (seq ns-meta)
              (with-meta ns-sym ns-meta)
              ns-sym))
          (let [sym-ns (namespace sym)
                ;; Use heap-atom for latest state (handles intern, defmacro etc.)
                heap (if-let [a (:heap-atom machine)] @a (:heap machine))]
            (if sym-ns
          ;; Qualified symbol
              (let [ns-table (:ns machine)
                    current-ns (:current-ns machine)
                    current-ns-data (get ns-table current-ns)
                    resolved-ns (or (get (:aliases current-ns-data) (symbol sym-ns))
                                ;; Global ns-aliases
                                    (get (:ns-aliases machine) (symbol sym-ns))
                                    (symbol sym-ns))
                ;; Follow ns-aliases transitively
                    resolved-ns (or (get (:ns-aliases machine) resolved-ns)
                                    resolved-ns)
                    qualified (symbol (str resolved-ns) sym-name)
                    dyn (:dynamic-bindings machine)]
                (if (and dyn (contains? dyn qualified))
                  (get dyn qualified)
                  (if (contains? heap qualified)
                    (let [entry (get heap qualified)
                          v (:val entry)
                      ;; DynamicVar (from new-dynamic-var) wraps an atom for thread-local storage;
                      ;; deref it to get the current value. Plain atoms are returned as-is.
                          v (if (instance? sci.lang.DynamicVar v) @v v)]
                      (if (and (not (:bound? entry true))
                               (nil? v))
                        (sci.lang/->Unbound qualified)
                        v))
              ;; Check SCI types in the resolved namespace
                    (if-let [type-obj (get-in machine [:ns resolved-ns :types (symbol sym-name)])]
                      type-obj
                ;; Try as Java static field/method
                      #?(:clj
                         (if-let [klass (try-resolve-class sym-ns)]
                           (resolve-static-member klass sym-name)
                           (throw (ex-info (str "Unable to resolve symbol: " sym)
                                           {:type :sci/error :sym sym :phase "analysis"})))
                         :cljs
                         (throw (ex-info (str "Unable to resolve symbol: " sym)
                                         {:type :sci/error :sym sym :phase "analysis"})))))))
          ;; Unqualified
              (let [ns-sym (:current-ns machine)
                    qualified (symbol (str ns-sym) sym-name)
                    core-q (symbol "clojure.core" sym-name)
                    dyn (:dynamic-bindings machine)
                ;; Check :refer-clojure :exclude
                    excludes (get-in machine [:ns ns-sym :refer-clojure-excludes])
                    core-excluded? (and excludes (contains? excludes (symbol sym-name)))]
            ;; Use if-let chain instead of or — or treats false/nil as "not found"
                (if (and dyn (contains? dyn qualified)) (get dyn qualified)
                    (if (and (not core-excluded?) dyn (contains? dyn core-q)) (get dyn core-q)
                        (if (contains? heap qualified)
                          (let [entry (get heap qualified)
                                v (:val entry)
                        ;; DynamicVar (from new-dynamic-var) wraps an atom for thread-local storage;
                        ;; deref it to get the current value. Plain atoms are returned as-is.
                                v (if (instance? sci.lang.DynamicVar v) @v v)]
                            (if (and (not (:bound? entry true))
                                     (nil? v))
                              (sci.lang/->Unbound qualified)
                              v))
                          (if (and (not core-excluded?) (contains? heap core-q)) (:val (get heap core-q))
                    ;; Check types in namespace
                              (if-let [type-obj (get-in machine [:ns ns-sym :types (symbol sym-name)])]
                                type-obj
                                #?(:clj (or (try-resolve-class sym-name)
                                            (throw (ex-info (str "Unable to resolve symbol: " sym)
                                                            {:type :sci/error :sym sym :phase "analysis"})))
                                   :cljs (throw (ex-info (str "Unable to resolve symbol: " sym)
                                                         {:type :sci/error :sym sym :phase "analysis"}))))))))))))))))

;; ============================================================
;; Literals, symbols, collections
;; ============================================================

(defn step-eval-literal [machine frame]
  (m/push-value machine (:expr frame)))

(defn- meta-needs-eval?
  "Check if any values in a metadata map need evaluation (are non-literal forms
   or have metadata that needs evaluation)."
  [meta-map]
  (and meta-map
       (some (fn [[_ v]]
               (or (and (seq? v) (not (nil? v)))
                   (meta-needs-eval? (meta v))))
             meta-map)))

(defn step-eval-symbol [machine frame]
  (let [sym (:expr frame)
        _ (when (and (not (qualified-symbol? sym))
                     (contains? special-forms sym)
                     (not (contains? (:env machine) sym)))
            (throw (ex-info (str "Unable to resolve symbol: " sym " in this context")
                            {:type :sci/error :sym sym :phase "analysis"})))
        ;; Check if symbol resolves to a macro — can't use macro as value
        _ (when-not (contains? (:env machine) sym)
            (let [sym-name (name sym)
                  heap (if-let [a (:heap-atom machine)] @a (:heap machine))
                  ns-sym (:current-ns machine)
                  candidates [(symbol (str ns-sym) sym-name)
                              (symbol "clojure.core" sym-name)]
                  entry (some #(get heap %) candidates)]
              (when (:macro? entry)
                (throw (ex-info (str "Can't take value of a macro: " sym)
                                {:type :sci/error})))))]
    (m/push-value machine (resolve-symbol machine sym))))

(defn step-eval-vector [machine frame]
  (let [exprs (:expr frame)
        form-meta (meta (:expr frame))]
    (if (empty? exprs)
      (if (meta-needs-eval? form-meta)
        (-> machine
            (m/replace-frame {:op :apply-meta :value []})
            (m/push-frame {:op :eval :expr (into {} form-meta)}))
        (m/push-value machine (if form-meta (with-meta [] form-meta) [])))
      (-> machine
          (m/replace-frame {:op :eval-coll :coll-type :vector
                            :pending (subvec exprs 1) :done []
                            :form-meta form-meta})
          (m/push-frame {:op :eval :expr (nth exprs 0)})))))

(defn step-eval-map [machine frame]
  (let [exprs (:expr frame)
        form-meta (meta (:expr frame))
        flat (reduce-kv (fn [acc k v] (conj acc k v)) [] exprs)]
    (if (empty? flat)
      (if (meta-needs-eval? form-meta)
        (-> machine
            (m/replace-frame {:op :apply-meta :value {}})
            (m/push-frame {:op :eval :expr (into {} form-meta)}))
        (m/push-value machine (if form-meta (with-meta {} form-meta) {})))
      (-> machine
          (m/replace-frame {:op :eval-coll :coll-type :map
                            :pending (vec (rest flat)) :done []
                            :form-meta form-meta})
          (m/push-frame {:op :eval :expr (first flat)})))))

(defn step-eval-set [machine frame]
  (let [exprs (vec (:expr frame))
        form-meta (meta (:expr frame))]
    (if (empty? exprs)
      (if (meta-needs-eval? form-meta)
        (-> machine
            (m/replace-frame {:op :apply-meta :value #{}})
            (m/push-frame {:op :eval :expr (into {} form-meta)}))
        (m/push-value machine (if form-meta (with-meta #{} form-meta) #{})))
      (-> machine
          (m/replace-frame {:op :eval-coll :coll-type :set
                            :pending (vec (rest exprs)) :done []
                            :form-meta form-meta})
          (m/push-frame {:op :eval :expr (first exprs)})))))

(defn step-eval-coll [machine frame]
  (let [done (conj (:done frame) (:result machine))
        pending (:pending frame)]
    (if (empty? pending)
      (let [raw (case (:coll-type frame)
                  :vector (vec done)
                  :set    (let [s (set done)]
                            (when (not= (count s) (count done))
                              (throw (ex-info (str "Duplicate key: "
                                                   (pr-str (first (filter #(> (count (filter #{%} done)) 1) done))))
                                              {:type :sci/error})))
                            s)
                  :map    (let [ks (take-nth 2 done)]
                            (when (not= (count (set ks)) (count ks))
                              (throw (ex-info (str "Duplicate key: "
                                                   (pr-str (first (filter #(> (count (filter #{%} ks)) 1) ks))))
                                              {:type :sci/error})))
                            (apply array-map done)))
            fm (:form-meta frame)]
        (if (and fm (meta-needs-eval? fm))
          ;; Metadata has unevaluated forms — evaluate it first
          (-> machine
              (m/replace-frame {:op :apply-meta :value raw})
              (m/push-frame {:op :eval :expr (into {} fm)}))
          ;; Apply metadata as-is
          (let [val (if fm (with-meta raw fm) raw)]
            (m/push-value machine val))))
      (-> machine
          (m/replace-frame (assoc frame :done done :pending (vec (rest pending))))
          (m/push-frame {:op :eval :expr (first pending)})))))

(defn step-apply-meta [machine frame]
  (let [val (:value frame)
        evaled-meta (:result machine)]
    (if (and (fn? val) (:sci/closure (clojure.core/meta val)))
      ;; SCI closure: store user meta in :user-meta key (keeps internal closure info intact)
      (m/push-value machine (with-meta val (assoc (clojure.core/meta val) :user-meta evaled-meta)))
      ;; Other values: merge normally
      (let [new-meta (if (clojure.core/meta val)
                       (merge (clojure.core/meta val) evaled-meta)
                       evaled-meta)]
        (m/push-value machine (with-meta val new-meta))))))

;; ============================================================
;; if
;; ============================================================

(defn step-eval-if [machine frame]
  (let [form (:expr frame)
        argc (dec (count form))
        [_ test then else] form]
    (when (< argc 2)
      (throw (ex-info "Too few arguments to if" {:type :sci/error})))
    (when (> argc 3)
      (throw (ex-info "Too many arguments to if" {:type :sci/error})))
    (-> machine
        (m/replace-frame {:op :if :then then :else else})
        (m/push-frame {:op :eval :expr test}))))

(defn step-if [machine frame]
  (if (:result machine)
    (m/replace-frame machine {:op :eval :expr (:then frame)})
    (if (contains? frame :else)
      (m/replace-frame machine {:op :eval :expr (:else frame)})
      (m/push-value machine nil))))

;; ============================================================
;; do
;; ============================================================

(defn step-eval-do [machine frame]
  (let [body (vec (rest (:expr frame)))]
    (if (empty? body)
      (m/push-value machine nil)
      (-> machine
          (m/replace-frame {:op :do :remaining (subvec body 1)})
          (m/push-frame {:op :eval :expr (nth body 0)})))))

(defn step-do [machine frame]
  (let [remaining (:remaining frame)]
    (if (empty? remaining)
      (m/pop-frame machine)
      (-> machine
          (assoc :top-loc nil) ;; reset for fresh location tracking per form
          (m/replace-frame (assoc frame :remaining (subvec remaining 1)))
          (m/push-frame {:op :eval :expr (nth remaining 0)})))))

;; ============================================================
;; let*
;; ============================================================

(defn step-eval-let [machine frame]
  (let [[_ bindings & body] (:expr frame)
        binding-pairs (vec (partition 2 bindings))]
    (-> machine
        (m/replace-frame {:op :let
                          :bindings binding-pairs
                          :body (vec body)
                          :saved-env (:env machine)
                          :bind-idx 0}))))

(defn step-let [machine frame]
  (let [idx (:bind-idx frame)
        bindings (:bindings frame)]
    (if (nil? idx)
      ;; :bind-result phase — binding value just evaluated
      (let [sym (:bind-sym frame)
            val (:result machine)]
        (-> machine
            (update :env assoc sym val)
            (m/replace-frame (assoc frame :bind-idx (:next-idx frame)
                                    :bind-sym nil
                                    :next-idx nil))))
      (if (>= idx (count bindings))
        ;; All bindings done — evaluate body
        (let [body (:body frame)]
          (if (empty? body)
            (-> machine
                (assoc :env (:saved-env frame))
                (m/push-value nil))
            (-> machine
                (m/replace-frame {:op :do-restore-env
                                  :body body
                                  :saved-env (:saved-env frame)})
                (m/push-frame {:op :eval :expr (first body)}))))
        ;; Evaluate next binding value
        (let [[sym expr] (nth bindings idx)]
          (-> machine
              (m/replace-frame (assoc frame :bind-idx nil
                                      :bind-sym sym
                                      :next-idx (inc idx)))
              (m/push-frame {:op :eval :expr expr})))))))

;; do-restore-env: like do but restores env when done
(defn step-do-restore-env [machine frame]
  (let [body (:body frame)
        remaining (vec (rest body))]
    (if (empty? remaining)
      ;; Last expression done — restore env
      (-> machine
          (assoc :env (:saved-env frame))
          (m/pop-frame))
      ;; More body expressions
      (-> machine
          (m/replace-frame (assoc frame :body remaining))
          (m/push-frame {:op :eval :expr (first remaining)})))))

;; ============================================================
;; Tail position analysis for recur
;; ============================================================

(defn- check-recur-in-body
  "Check that recur only appears in tail position within a body.
   `tail?` indicates whether the current form is in tail position.
   `expected-argc` is the expected number of recur args (param count), or nil.
   Throws if recur is found in non-tail position or with wrong arity."
  ([form tail?] (check-recur-in-body form tail? nil))
  ([form tail? expected-argc]
   (cond
    ;; Check inside vectors — not tail position
     (vector? form) (doseq [e form] (check-recur-in-body e false))
    ;; Check inside maps — not tail position
     (map? form) (doseq [[k v] form]
                   (check-recur-in-body k false)
                   (check-recur-in-body v false))
    ;; Check inside sets — not tail position
     (set? form) (doseq [e form] (check-recur-in-body e false))
     (not (seq? form)) nil
     (empty? form) nil
     :else
     (let [raw-head (first form)
          ;; Strip namespace from head (e.g. clojure.core/let → let)
           head (if (and (symbol? raw-head) (namespace raw-head))
                  (symbol (name raw-head))
                  raw-head)]
       (cond
        ;; (recur ...) — check if we're in tail position and arity matches
         (= 'recur head)
         (do (when (= expected-argc :in-try)
               (throw (ex-info "Cannot recur across try"
                               {:type :sci/error})))
             (when-not tail?
               (throw (ex-info "Can only recur from tail position"
                               {:type :sci/error})))
             (when (and (number? expected-argc) (not= expected-argc (count (rest form))))
               (throw (ex-info (str "Mismatched argument count to recur, expected: "
                                    expected-argc " args, got: " (count (rest form)))
                               {:type :sci/error}))))

        ;; (if test then else) — test is not tail, branches inherit tail?
         (= 'if head)
         (let [[_ test then else] form]
           (check-recur-in-body test false)
           (check-recur-in-body then tail? expected-argc)
           (when else (check-recur-in-body else tail? expected-argc)))

        ;; (do expr...) — only last expr is tail
         (= 'do head)
         (let [exprs (rest form)]
           (when (seq exprs)
             (doseq [e (butlast exprs)]
               (check-recur-in-body e false))
             (check-recur-in-body (last exprs) tail? expected-argc)))

        ;; (let* [bindings...] body...) or (let ...) — only last body expr is tail
         (contains? '#{let* let letfn*} head)
         (let [[_ bindings & body] form]
           (doseq [[_ init] (partition 2 bindings)]
             (check-recur-in-body init false))
           (when (seq body)
             (doseq [e (butlast body)]
               (check-recur-in-body e false))
             (check-recur-in-body (last body) tail? expected-argc)))

        ;; (loop* [bindings...] body...) — body is a new recur target
         (= 'loop* head) nil

        ;; (fn* ...) / (fn ...) / (letfn* ...) — new recur context, don't descend
         (contains? '#{fn* fn letfn* letfn reify*} head) nil

        ;; (defn name [params] body) — new recur context, but check body
         (contains? '#{defn defn-} head)
         (let [args (rest form)
              ;; Skip name, docstring?, attr-map?
               args (if (symbol? (first args)) (rest args) args)
               args (if (string? (first args)) (rest args) args)
               args (if (map? (first args)) (rest args) args)]
           (when (vector? (first args))
            ;; Single arity: [params] body...
             (let [params (first args)
                   body (rest args)
                   argc (count (remove #{'&} params))]
               (when (seq body)
                 (doseq [e (butlast body)]
                   (check-recur-in-body e false))
                 (check-recur-in-body (last body) true argc)))))

        ;; (try ...) — recur not allowed across try
         (= 'try head)
         (doseq [expr (rest form)]
           (if (and (seq? expr) (contains? #{'catch 'finally} (first expr)))
             (doseq [e (rest expr)]
               (check-recur-in-body e false :in-try))
             (check-recur-in-body expr false :in-try)))

        ;; (case* ...) / (case ...) — result exprs inherit tail position
         (contains? '#{case* case} head)
         (let [[_ expr _ _ default case-map] form]
           (check-recur-in-body expr false)
           (check-recur-in-body default tail? expected-argc)
           (when (map? case-map)
             (doseq [[_ [_ result-expr]] case-map]
               (check-recur-in-body result-expr tail? expected-argc))))

        ;; (def ...) — init expr is not tail
         (= 'def head)
         (when (> (count form) 2)
           (check-recur-in-body (last form) false))

        ;; (binding [...] body...) — only last body is tail
         (= 'binding head)
         (let [[_ _ & body] form]
           (when (seq body)
             (doseq [e (butlast body)]
               (check-recur-in-body e false))
             (check-recur-in-body (last body) tail? expected-argc)))

        ;; Macros that pass tail position to their last arg
         (contains? '#{or and when when-not when-first} head)
         (let [args (rest form)]
           (when (seq args)
             (doseq [e (butlast args)]
               (check-recur-in-body e false))
             (check-recur-in-body (last args) tail? expected-argc)))

        ;; if-let/when-let/if-some/when-some — [binding] then else
         (contains? '#{if-let when-let if-some when-some} head)
         (let [[_ bindings & body] form]
           (when (vector? bindings)
             (doseq [e bindings] (check-recur-in-body e false)))
           (doseq [e body] (check-recur-in-body e tail? expected-argc)))

        ;; Any other list form — args are not tail
         :else
         (doseq [arg (rest form)]
           (check-recur-in-body arg false)))))))

(defn- check-recur-tail-position
  "Check that recur is only used in tail position within fn/loop arities."
  [arities]
  (doseq [{:keys [params body]} arities]
    (when (seq body)
      (let [argc (count (remove #{'&} params))]
        (doseq [e (butlast body)]
          (check-recur-in-body e false))
        (check-recur-in-body (last body) true argc)))))

;; ============================================================
;; ^:const inlining — substitute const var references in fn bodies
;; ============================================================

(defn- inline-const-syms
  "Walk a form, replacing unqualified symbols that resolve to :const? vars with
   their current values (wrapped in quote). Tracks local bindings introduced by
   let*, loop*, fn*, destructuring etc. so they are NOT substituted."
  [form heap current-ns locals]
  (cond
    (symbol? form)
    (if (or (namespace form) (contains? locals form) (= '& form))
      form
      (let [qualified (symbol (str current-ns) (name form))
            entry (or (get heap qualified) (get heap (symbol "clojure.core" (name form))))]
        (if (:const? entry)
          (list 'quote (:val entry))
          form)))

    (seq? form)
    (case (first form)
      quote  form
      ;; fn* introduces new local scope — don't inline across fn boundary
      fn*    form
      ;; let*/loop*: walk binding values with outer locals, bodies with extended locals
      (let* loop*)
      (let [[head bindings & body] form
            pairs (partition 2 bindings)
            walked-pairs (mapcat (fn [[sym val]]
                                   [sym (inline-const-syms val heap current-ns locals)])
                                 pairs)
            new-locals (into locals (map (fn [[sym _]] sym) pairs))
            rebuilt (apply list head (vec walked-pairs)
                           (map #(inline-const-syms % heap current-ns new-locals) body))]
        (if (meta form) (with-meta rebuilt (meta form)) rebuilt))
      ;; Default: walk all sub-forms, preserving source location metadata
      (let [rebuilt (apply list (map #(inline-const-syms % heap current-ns locals) form))]
        (if (meta form) (with-meta rebuilt (meta form)) rebuilt)))

    (vector? form)
    (mapv #(inline-const-syms % heap current-ns locals) form)

    (map? form)
    (into {} (map (fn [[k v]] [(inline-const-syms k heap current-ns locals)
                               (inline-const-syms v heap current-ns locals)])
                  form))

    (set? form)
    (into #{} (map #(inline-const-syms % heap current-ns locals) form))

    :else form))

;; ============================================================
;; fn* parsing (needed by static analysis and fn* step handler)
;; ============================================================

(defn parse-fn-form [form]
  (let [args (rest form)
        [fname args] (if (symbol? (first args))
                       [(first args) (rest args)]
                       [nil args])
        ;; Skip optional docstring
        [docstring args] (if (string? (first args))
                           [(first args) (rest args)]
                           [nil args])
        ;; Skip optional attr-map
        [attr-map args] (if (and (map? (first args))
                                 (not (vector? (first args))))
                          [(first args) (rest args)]
                          [nil args])
        arities (if (vector? (first args))
                  [{:params (vec (first args)) :body (vec (rest args))}]
                  (mapv (fn [arity-form]
                          {:params (vec (first arity-form))
                           :body (vec (rest arity-form))})
                        args))]
    {:name fname :arities arities :docstring docstring :attr-map attr-map}))

;; Forward declarations for static analysis helpers (defined after macroexpand-form)
(declare extract-param-hints analyze-form macroexpand-all)

;; ============================================================
;; fn*
;; ============================================================

(defn make-callable-closure
  "Create a closure that is both an IFn (so host code like `map` can call it)
   and carries closure metadata for the VM."
  [closure-map machine]
  (let [fn-name (let [n (:name closure-map)
                      ns-sym (:ns closure-map)]
                  (when n
                    (if ns-sym
                      (symbol (str ns-sym) (str n))
                      n)))
        f (fn callable-closure [& args]
            ;; Create a mini-machine and run the closure
            (let [arity (match-arity (:arities closure-map) (count args) fn-name)
                  bindings (bind-params (:params arity) args)
                  fn-env (merge (:env closure-map)
                                bindings
                                (when-let [fname (:name closure-map)]
                                  {fname callable-closure}))
                  ;; Use heap-atom for latest heap state (handles forward references)
                  heap-atom (:heap-atom machine)
                  latest-heap (if heap-atom @heap-atom (:heap machine))
                  mini-m (-> (m/make-machine {:heap latest-heap
                                              :ns-table (:ns machine)
                                              :permissions (:permissions machine)})
                             (assoc :env fn-env
                                    :current-ns (:current-ns machine)
                                    :current-fn-name (:name closure-map)
                                    :heap-atom heap-atom
                                    :dynamic-bindings current-dynamic-bindings))]
              ;; Push fn-body frame with recur-target so recur works
              (let [body (:body arity)
                    m (-> mini-m
                          (m/push-frame {:op :fn-body
                                         :body body
                                         :saved-env fn-env
                                         :recur-target true
                                         :params (:params arity)
                                         :loop-body body
                                         :closure closure-map}))]
                ;; step-fn-body will push the eval frame for (first body)
                (run m))))]
    (with-meta f (assoc closure-map :sci/closure true))))

(defn- validate-fn-arities
  "Check multi-arity fn validity."
  [arities]
  (let [variadic-arities (filter (fn [{:keys [params]}]
                                   (some #{'&} params))
                                 arities)
        fixed-arities (remove (fn [{:keys [params]}]
                                (some #{'&} params))
                              arities)]
    (when (> (count variadic-arities) 1)
      (throw (ex-info "Can't have more than 1 variadic overload"
                      {:type :sci/error})))
    (when (and (seq variadic-arities) (seq fixed-arities))
      (let [variadic-fixed (count (take-while #(not= '& %) (:params (first variadic-arities))))
            max-fixed (apply max (map #(count (:params %)) fixed-arities))]
        (when (> max-fixed variadic-fixed)
          (throw (ex-info "Can't have fixed arity function with more params than variadic function"
                          {:type :sci/error})))))))

(defn step-eval-fn [machine frame]
  (let [parsed (parse-fn-form (:expr frame))
        ;; Validate multi-arity fn rules
        _ (when (> (count (:arities parsed)) 1)
            (validate-fn-arities (:arities parsed)))
        ;; Check recur tail position only for user-written fn* forms
        _ (when (:line (meta (:expr frame)))
            (check-recur-tail-position (:arities parsed)))
        ;; Analyze fn bodies for undefined symbols / macro values / denied symbols.
        ;; Only for user-written fn* forms (those with source :line from the reader).
        _ (when (:line (meta (:expr frame)))
            (let [base-env (cond-> (into {} (map (fn [[k _]] [k nil]) (:env machine)))
                             (:name parsed) (assoc (:name parsed) nil))]
              (doseq [{:keys [params body]} (:arities parsed)
                      :let [fn-env (into base-env (extract-param-hints params))]]
                (doseq [bf body]
                  (analyze-form machine fn-env bf)))))
        fn-meta (meta (:expr frame))
        ;; Inline ^:const var references in fn bodies (Clojure semantics: const vars are
        ;; substituted at compile time so redefinition of the var doesn't affect the fn).
        heap (if-let [a (:heap-atom machine)] @a (:heap machine))
        current-ns (:current-ns machine)
        ;; Build env-locals as ordered map: fn name first, then outer env locals.
        ;; Order matters because macroexpand-all passes this as &env to macros,
        ;; and Clojure preserves insertion order in &env (fn name, params, lets).
        env-locals (cond-> (into {} (map (fn [[k _]] [k nil]) (:env machine)))
                     (:name parsed) (as-> m (into {(:name parsed) nil} m)))
        arities (mapv (fn [{:keys [params body] :as arity}]
                        (let [;; param-map: ordered map used for macroexpand-all (&env)
                              param-map (reduce (fn [m p] (assoc m p nil))
                                                env-locals
                                                (remove #{'&} params))
                              ;; param-syms: set used for inline-const-syms (order irrelevant)
                              param-syms (into #{} (keys param-map))]
                          (assoc arity :body
                                 (mapv (fn [bf]
                                         ;; 1. Inline ^:const vars
                                         (let [inlined (inline-const-syms bf heap current-ns param-syms)]
                                           ;; 2. Expand macros at definition time (Clojure compile-time semantics)
                                           (macroexpand-all machine inlined param-map)))
                                       body))))
                      (:arities parsed))
        closure-map {:type :closure
                     :name (:name parsed)
                     :ns (:current-ns machine)
                     :arities arities
                     :env (:env machine)
                     :line (:line fn-meta)
                     :column (:column fn-meta)
                     :file (:current-file machine)}
        callable (make-callable-closure closure-map machine)
        ;; Check for user metadata on the fn form (e.g. ^{:foo 1} (fn []))
        form-meta (meta (:expr frame))
        user-meta (when form-meta
                    (dissoc form-meta :line :column :end-line :end-column))]
    (if (meta-needs-eval? user-meta)
      ;; Metadata needs evaluation — push eval frame
      (-> machine
          (m/replace-frame {:op :apply-meta :value callable})
          (m/push-frame {:op :eval :expr (into {} user-meta)}))
      ;; Store user metadata in :user-meta key so meta/with-meta overrides can expose it
      (if (seq user-meta)
        (m/push-value machine (with-meta callable (assoc (clojure.core/meta callable) :user-meta user-meta)))
        (m/push-value machine callable)))))

;; ============================================================
;; Function application
;; ============================================================

(defn step-eval-invoke [machine frame]
  (let [form (:expr frame)
        f-expr (first form)
        arg-exprs (vec (rest form))
        loc (form-location form)
        ;; Capture depth BEFORE pushing call-site frame (used to trim on fn return)
        pre-call-depth (count (:callstack machine))
        ;; Push callstack entry for this call site
        machine (if loc
                  (update machine :callstack conj
                          {:ns (:current-ns machine)
                           :name (:current-fn-name machine)
                           :line (:line loc)
                           :column (:column loc)
                           :file (:current-file machine)})
                  machine)]
    (-> machine
        (m/replace-frame {:op :eval-args
                          :pending arg-exprs
                          :done []
                          :phase :eval-f
                          :callstack-depth (count (:callstack machine))
                          :pre-call-depth pre-call-depth})
        (m/push-frame {:op :eval :expr f-expr}))))

(defn step-eval-args [machine frame]
  (case (:phase frame)
    :eval-f
    (let [f (:result machine)
          pending (:pending frame)]
      (if (empty? pending)
        (cond
          (:dot? frame)
          #?(:clj
             (let [method-str (str (:method-name frame))]
               (if (instance? Class f)
                 ;; Static access — try static field/method first, fall back to instance method on Class object
                 (if (:field? frame)
                   (m/push-value machine
                                 (try (clojure.lang.Reflector/getStaticField ^Class f method-str)
                                      (catch Exception _
                                        (clojure.lang.Reflector/invokeNoArgInstanceMember f method-str false))))
                   (m/push-value machine
                                 (try
                                   (clojure.lang.Reflector/getStaticField ^Class f method-str)
                                   (catch Exception _
                                     (try (clojure.lang.Reflector/invokeStaticMethod ^Class f method-str (to-array []))
                                          (catch Exception _
                                            (clojure.lang.Reflector/invokeNoArgInstanceMember f method-str false)))))))
                 ;; Instance access
                 (if (:field? frame)
                   (if (:type (clojure.core/meta f))
                     ;; SCI type instance — field access via keyword
                     (let [field-name (if (.startsWith ^String method-str "-")
                                        (subs method-str 1)
                                        method-str)]
                       (m/push-value machine (get f (keyword field-name))))
                     ;; For .-field syntax, try field access first, fall back to method
                     (m/push-value machine
                                   (try (clojure.lang.Reflector/getInstanceField f method-str)
                                        (catch Exception _
                                          (clojure.lang.Reflector/invokeNoArgInstanceMember f method-str false)))))
                   ;; Special methods for sci.lang.Var
                   (if (and (instance? sci.lang.Var f)
                            (contains? #{"hasRoot" "isBound" "isDynamic" "get"} method-str))
                     (m/push-value machine
                                   (case method-str
                                     "hasRoot" (some? (.-val ^sci.lang.Var f))
                                     "isBound" (some? (.-val ^sci.lang.Var f))
                                     "isDynamic" (boolean (.-dynamic? ^sci.lang.Var f))
                                     "get" (.-val ^sci.lang.Var f)))
                     (m/push-value machine
                                   (clojure.lang.Reflector/invokeNoArgInstanceMember f method-str false))))))
             :cljs
             (throw (ex-info "Interop not supported in CLJS" {})))
          (:new? frame)
          (if (instance? sci.lang.Type f)
            ;; SCI type constructor
            (let [type-obj f
                  fields (.-fields ^sci.lang.Type type-obj)
                  field-kws (mapv keyword fields)
                  is-record? (:record? (.-opts ^sci.lang.Type type-obj))
                  instance (with-meta (zipmap field-kws [])
                             (merge {:type type-obj}
                                    (when is-record? {:sci.impl/record true})))]
              (m/push-value machine instance))
            #?(:clj
               (m/push-value machine
                             (clojure.lang.Reflector/invokeConstructor
                              ^Class f (to-array [])))
               :cljs
               (throw (ex-info "new not supported in CLJS" {}))))
          :else
          (m/replace-frame machine {:op :apply :f f :args []
                                    :pre-call-depth (:pre-call-depth frame)}))
        (-> machine
            (m/replace-frame (assoc frame :f f :phase :eval-arg
                                    :pending (subvec pending 1)))
            (m/push-frame {:op :eval :expr (nth pending 0)}))))

    :eval-arg
    (let [done (conj (:done frame) (:result machine))
          pending (:pending frame)]
      (if (empty? pending)
        (cond
          (:dot? frame)
          (let [obj (:f frame)
                method-str (str (:method-name frame))
                args done]
            #?(:clj
               (if (instance? Class obj)
                 ;; Static method call
                 ;; Special case: PersistentHashMap.create with a single-element seq
                 ;; containing a map is the Clojure 1.10 kwargs destructuring form.
                 ;; In Clojure 1.11 this became seq-to-map-for-destructuring, which
                 ;; allows a single map to be passed as kwargs. Replicate that here.
                 (if (and (= ^Class obj clojure.lang.PersistentHashMap)
                          (= "create" method-str)
                          (= 1 (count args))
                          (sequential? (first args))
                          (= 1 (count (first args)))
                          (map? (first (first args))))
                   (m/push-value machine (first (first args)))
                   (m/push-value machine
                                 (clojure.lang.Reflector/invokeStaticMethod ^Class obj method-str (to-array args))))
                 ;; Instance method call — fall back to field access if method not found
                 (m/push-value machine
                               (try (clojure.lang.Reflector/invokeInstanceMethod obj method-str (to-array args))
                                    (catch IllegalArgumentException _
                                      (if (empty? args)
                                        (clojure.lang.Reflector/invokeNoArgInstanceMember obj method-str false)
                                        (throw (ex-info (str "No matching method " method-str
                                                             " found taking " (count args)
                                                             " args for class " (class obj))
                                                        {:type :sci/error})))))))
               :cljs
               (throw (ex-info "Interop not supported in CLJS" {}))))
          (:new? frame)
          (let [f (:f frame)]
            (if (instance? sci.lang.Type f)
              ;; SCI type constructor with args
              (let [fields (.-fields ^sci.lang.Type f)
                    field-kws (mapv keyword fields)
                    is-record? (:record? (.-opts ^sci.lang.Type f))
                    instance (with-meta (zipmap field-kws done)
                               (merge {:type f}
                                      (when is-record? {:sci.impl/record true})))]
                (m/push-value machine instance))
              #?(:clj
                 (m/push-value machine
                               (clojure.lang.Reflector/invokeConstructor
                                ^Class f (to-array done)))
                 :cljs
                 (throw (ex-info "new not supported in CLJS" {})))))
          (:defmethod? frame)
          ;; f = multimethod, done = [dispatch-val method-fn]
          (let [mm (:f frame)
                [dispatch-val method-fn] done]
            ;; Check class access if dispatch-val is a Java class
            #?(:clj (when (class? dispatch-val)
                      (check-class-access machine (.getName ^Class dispatch-val) dispatch-val)))
            #?(:clj
               (if (instance? clojure.lang.MultiFn mm)
                 (.addMethod ^clojure.lang.MultiFn mm dispatch-val method-fn)
                 (swap! (:methods (meta mm)) assoc dispatch-val method-fn))
               :cljs
               (swap! (:methods (meta mm)) assoc dispatch-val method-fn))
            (m/push-value machine mm))
          (:remove-method? frame)
          (let [mm (:f frame)
                [dispatch-val] done]
            #?(:clj
               (if (instance? clojure.lang.MultiFn mm)
                 (.removeMethod ^clojure.lang.MultiFn mm dispatch-val)
                 (swap! (:methods (meta mm)) dissoc dispatch-val))
               :cljs
               (swap! (:methods (meta mm)) dissoc dispatch-val))
            (m/push-value machine mm))
          (:prefer-method? frame)
          (let [mm (:f frame)
                [preferred other] done
                prefer-atom (:prefer-table (meta mm))]
            (swap! prefer-atom assoc preferred other)
            (m/push-value machine mm))
          (:extend? frame)
          ;; f = type, done = [protocol impl-map]
          (let [target-type (:f frame)
                [protocol impl-map] done]
            (do-extend protocol target-type impl-map)
            (m/push-value machine nil))
          :else
          (m/replace-frame machine {:op :apply :f (:f frame) :args done
                                    :pre-call-depth (:pre-call-depth frame)}))
        (-> machine
            (m/replace-frame (assoc frame :done done
                                    :pending (subvec pending 1)))
            (m/push-frame {:op :eval :expr (nth pending 0)}))))))

(defn match-arity
  ([arities argc] (match-arity arities argc nil false))
  ([arities argc fn-name] (match-arity arities argc fn-name false))
  ([arities argc fn-name disable-arity-checks?]
   (or
    ;; Prefer exact match over variadic
    (first (filter (fn [{:keys [params]}]
                     (let [params-vec (vec params)
                           amp-pos (reduce-kv (fn [_ i v] (if (= '& v) (reduced i) nil))
                                              nil params-vec)]
                       (and (nil? amp-pos) (= argc (count params)))))
                   arities))
    ;; Fall back to variadic match
    (first (filter (fn [{:keys [params]}]
                     (let [params-vec (vec params)
                           amp-pos (reduce-kv (fn [_ i v] (if (= '& v) (reduced i) nil))
                                              nil params-vec)]
                       (and amp-pos (>= argc amp-pos))))
                   arities))
    (if fn-name
      (throw (ex-info (if disable-arity-checks?
                        (str "Cannot call " (name fn-name) " with " argc " arguments")
                        (str "Wrong number of args (" argc ") passed to: " fn-name))
                      {:type :sci/error}))
      (let [arity-counts (map (fn [{:keys [params]}]
                                (let [pv (vec params)
                                      amp (reduce-kv (fn [_ i v] (if (= '& v) (reduced i) nil)) nil pv)]
                                  (if amp amp (count params))))
                              arities)]
        (throw (ex-info (str "Wrong number of args (" argc ") passed to: function of arity "
                             (clojure.string/join ", " arity-counts))
                        {:type :sci/error})))))))

(defn bind-params [params args]
  (let [params-vec (vec params)
        amp-pos (reduce-kv (fn [_ i v] (if (= '& v) (reduced i) nil))
                           nil params-vec)]
    (if (nil? amp-pos)
      (zipmap params args)
      (let [fixed-params (subvec params-vec 0 amp-pos)
            rest-param (nth params-vec (inc amp-pos))
            fixed-args (take amp-pos args)
            rest-args (drop amp-pos args)
            ;; Clojure 1.11 kwargs map support: if rest-param is a map destructuring form
            ;; and the rest args are a single map, use the map directly as kwargs.
            rest-val (if (and (map? rest-param)
                              (= 1 (count rest-args))
                              (map? (first rest-args)))
                       (first rest-args)
                       (seq rest-args))]
        (-> (zipmap fixed-params fixed-args)
            (assoc rest-param rest-val))))))

(defn step-apply [machine frame]
  (let [f (:f frame)
        args (:args frame)]
    (cond
      ;; SCI Var — deref and re-apply with the var's value
      (instance? sci.lang.Var f)
      (m/replace-frame machine {:op :apply :f (.-val ^sci.lang.Var f) :args args
                                :pre-call-depth (:pre-call-depth frame)})

      ;; SCI closure wrapped as IFn — unwrap and use VM stack path
      (and (fn? f) (:sci/closure (meta f)))
      (let [closure-map (-> (meta f) (dissoc :sci/closure) (assoc :sci/self f))]
        (m/replace-frame machine {:op :apply :f closure-map :args args
                                  :pre-call-depth (:pre-call-depth frame)}))

      ;; Host function
      (fn? f)
      (m/push-value machine (apply f args))

      ;; Host fn ref (for serialization)
      (and (map? f) (= :host-fn (:type f)))
      (m/push-value machine (apply (:fn f) args))

      ;; Closure
      (and (map? f) (= :closure (:type f)))
      (let [;; Qualify the name for error messages
            qualified-name (when-let [n (:name f)]
                             (if (qualified-symbol? n) n
                                 (let [ns-sym (or (:ns f) (:current-ns machine))]
                                   (symbol (str ns-sym) (str n)))))
            disable-arity-checks? (get-in machine [:permissions :disable-arity-checks])
            arity (match-arity (:arities f) (count args) qualified-name disable-arity-checks?)
            bindings (bind-params (:params arity) args)
            fn-env (merge (:env f)
                          ;; Self-reference comes before params to match Clojure's &env order.
                          ;; Only for (fn name [x] ...) style, not (defn name [x] ...) which
                          ;; uses :sci/def-named to suppress this.
                          ;; Use :sci/self (the IFn wrapper) if available so self-reference
                          ;; returns the same object as the caller sees.
                          (when (and (:name f) (not (:sci/def-named f)))
                            {(:name f) (or (:sci/self f) f)})
                          bindings)
            ;; Use pre-call-depth (before call-site frame was pushed) as the saved depth.
            ;; This ensures the call-site frame AND entry frame are removed on successful return.
            pre-call-depth (or (:pre-call-depth frame) (count (:callstack machine)))
            ;; Push function entry frame (definition location) if the fn has a name and location
            machine (if (and (:name f) (:line f))
                      (update machine :callstack conj
                              {:ns (or (:ns f) (:current-ns machine))
                               :name (:name f)
                               :line (:line f)
                               :column (:column f)
                               :file (:file f)})
                      machine)]
        (-> machine
            (m/replace-frame {:op :fn-body
                              :body (:body arity)
                              :loop-body (:body arity)
                              :saved-env (:env machine)
                              :saved-fn-name (:current-fn-name machine)
                              :saved-callstack-depth pre-call-depth
                              :recur-target true
                              :params (:params arity)
                              :closure f})
            (assoc :env fn-env
                   :current-fn-name (:name f))))

      ;; Keyword as function
      (keyword? f)
      (m/push-value machine (get (first args) f (second args)))

      ;; Map as function (but not closure/host-fn maps)
      (and (map? f) (not (:type f)))
      (m/push-value machine (get f (first args) (second args)))

      ;; Set as function
      (set? f)
      (m/push-value machine (get f (first args)))

      ;; Vector as function
      (vector? f)
      (m/push-value machine (nth f (first args)))

      ;; Symbol — used as function: looks up in map (like keyword)
      (symbol? f)
      (m/push-value machine (get (first args) f (second args)))

      ;; Java class as constructor
      #?@(:clj
          [(instance? Class f)
           (m/push-value machine
                         (clojure.lang.Reflector/invokeConstructor
                          ^Class f (to-array args)))])

      ;; Unbound var
      (instance? sci.lang.Unbound f)
      (throw (ex-info (str "unbound fn: #'" (.-sym ^sci.lang.Unbound f))
                      {:type :sci/error}))

      :else
      (throw (ex-info (str "Cannot call " (pr-str f) " as a function")
                      {:type :sci/error})))))

;; ============================================================
;; fn-body
;; ============================================================

(defn step-fn-body [machine frame]
  (let [body (:body frame)]
    (if (empty? body)
      (let [depth (:saved-callstack-depth frame)]
        (-> machine
            (assoc :env (:saved-env frame)
                   :current-fn-name (:saved-fn-name frame))
            (cond-> depth (update :callstack #(subvec (vec %) 0 (min depth (count %)))))
            (m/push-value nil)))
      (if (= 1 (count body))
        ;; Single expression — tail position
        (-> machine
            (m/replace-frame (assoc frame :body [] :phase :return))
            (m/push-frame {:op :eval :expr (first body)}))
        ;; Multiple — eval first, keep rest
        (-> machine
            (m/replace-frame (assoc frame :body (vec (rest body))))
            (m/push-frame {:op :eval :expr (first body)}))))))

(defn step-fn-body-return [machine frame]
  (let [depth (:saved-callstack-depth frame)]
    (-> machine
        (assoc :env (:saved-env frame)
               :current-fn-name (:saved-fn-name frame))
        ;; Trim callstack back to saved depth
        (cond-> depth (update :callstack #(subvec (vec %) 0 (min depth (count %)))))
        (m/pop-frame))))

;; ============================================================
;; def
;; ============================================================

(defn step-eval-def [machine frame]
  (let [[_ sym & init] (:expr frame)
        ;; Validate def arguments — allow qualified if namespace matches current
        _ (when (and (symbol? sym) (namespace sym)
                     (not= (symbol (namespace sym)) (:current-ns machine)))
            (throw (ex-info (str "Can't def a qualified name: " sym
                                 ". Def requires a simple symbol.")
                            {:type :sci/error})))
        ;; Strip namespace if it matches current ns
        sym (if (namespace sym) (symbol (name sym)) sym)
        _ (when (or (> (count init) 2)
                    (and (= 2 (count init)) (not (string? (first init)))))
            (throw (ex-info "Too many arguments to def"
                            {:type :sci/error})))
        ;; Handle (def name docstring init-expr)
        [doc-str init-expr meta-map]
        (cond
          (empty? init)       [nil nil (meta sym)]
          (and (= 2 (count init)) (string? (first init)))
          [(first init) (second init) (merge (meta sym) {:doc (first init)})]
          :else               [nil (first init) (meta sym)])
        ;; Add source location: use the outermost form's location (top-loc) which is the
        ;; macro call site when inside a macro expansion. For direct (def ...) forms,
        ;; top-loc equals the form's own location. Fall back to form's own metadata.
        form-meta (meta (:expr frame))
        effective-loc (or (:top-loc machine) form-meta)
        meta-map (cond-> (or meta-map {})
                   (:line effective-loc) (assoc :line (:line effective-loc)
                                                :column (:column effective-loc))
                   (:current-file machine) (assoc :file (:current-file machine)))
        ;; Analyze fn* init-expr bodies at definition time when the def form has source
        ;; location (user-written or from defn macro expansion). This catches undefined
        ;; symbols, macro references as values, and denied symbols.
        _ (when (and (:line form-meta)
                     (seq? init-expr)
                     (= 'fn* (first init-expr)))
            (let [fn-parsed (parse-fn-form init-expr)
                  base-env (cond-> (into {} (map (fn [[k _]] [k nil]) (:env machine)))
                             (:name fn-parsed) (assoc (:name fn-parsed) nil))]
              (doseq [{:keys [params body]} (:arities fn-parsed)
                      :let [fn-env (into base-env (extract-param-hints params))]]
                (doseq [bf body]
                  (analyze-form machine fn-env bf)))))]
    ;; If metadata contains unevaluated forms, evaluate the map first
    (if (meta-needs-eval? meta-map)
      (-> machine
          (m/replace-frame {:op :def-with-meta
                            :sym sym
                            :init init
                            :init-expr init-expr
                            :form-meta (meta (:expr frame))})
          (m/push-frame {:op :eval :expr (into {} meta-map)}))
      (if (and (nil? init-expr) (empty? init))
        (let [ns-sym (:current-ns machine)
              qualified (symbol (str ns-sym) (str sym))
              ;; Only create entry if var doesn't already exist (declare semantics)
              heap (if-let [a (:heap-atom machine)] @a (:heap machine))
              existing (get heap qualified)
              ;; Check if existing entry was referred from another namespace
              ;; (i.e. has :sci.impl/var-sym pointing to a different ns)
              referred-from (when existing
                              (let [vs (get-in existing [:meta :sci.impl/var-sym])]
                                (when (and vs (not= (str ns-sym) (namespace vs)))
                                  vs)))
              _ (when referred-from
                  (throw (ex-info (str ns-sym " already refers to: " referred-from
                                       ", being replaced by: " qualified)
                                  {:type :sci/error})))
              entry (if (and existing (:bound? existing))
                      ;; Var already bound — keep existing value, update meta
                      (assoc existing :meta meta-map)
                      ;; Var not yet bound or doesn't exist — declare it
                      {:val nil :meta meta-map :bound? false})]
          (when-let [a (:heap-atom machine)]
            (swap! a assoc qualified entry))
          (-> machine
              (assoc-in [:heap qualified] entry)
              (m/push-value (sci.lang/->Var (symbol (name qualified)) nil
                                            (assoc meta-map :sci.impl/var-sym qualified)
                                            (:dynamic meta-map)))))
      (let [;; Propagate :line from the def form to init-expr (for recur checking)
            init-expr (if (and (seq? init-expr)
                               (not (:line (meta init-expr)))
                               (:line (meta (:expr frame))))
                        (with-meta init-expr
                          (select-keys (meta (:expr frame)) [:line :column]))
                        init-expr)
            ;; Pre-declare the var as unbound so self-referential defs work
            ;; e.g. (def foo foo) — foo is resolvable as Unbound during init
            ns-sym (:current-ns machine)
            qualified (symbol (str ns-sym) (str sym))
            heap (if-let [a (:heap-atom machine)] @a (:heap machine))
            machine (if (contains? heap qualified)
                      machine ;; already exists, don't clobber
                      (let [entry {:val nil :meta meta-map :bound? false}]
                        (when-let [a (:heap-atom machine)]
                          (swap! a assoc qualified entry))
                        (assoc-in machine [:heap qualified] entry)))]
        (-> machine
            (m/replace-frame {:op :def :sym sym
                              :ns-sym ns-sym
                              :meta-map meta-map})
            (m/push-frame {:op :eval :expr init-expr})))))))

(defn step-def-with-meta
  "Continue def after metadata has been evaluated."
  [machine frame]
  (let [meta-map (:result machine)
        sym (:sym frame)
        init (:init frame)
        init-expr (:init-expr frame)]
    (if (and (nil? init-expr) (empty? init))
      ;; declare path
      (let [ns-sym (:current-ns machine)
            qualified (symbol (str ns-sym) (str sym))
            heap (if-let [a (:heap-atom machine)] @a (:heap machine))
            existing (get heap qualified)
            entry (if (and existing (:bound? existing))
                    (assoc existing :meta meta-map)
                    {:val nil :meta meta-map :bound? false})]
        (when-let [a (:heap-atom machine)]
          (swap! a assoc qualified entry))
        (-> machine
            (assoc-in [:heap qualified] entry)
            (m/push-value (sci.lang/->Var (symbol (name qualified)) nil
                                          (assoc meta-map :sci.impl/var-sym qualified)
                                          (:dynamic meta-map)))))
      ;; def with init — push eval frame for the init expression
      (let [form-meta (:form-meta frame)
            init-expr (if (and (seq? init-expr)
                               (not (:line (meta init-expr)))
                               (:line form-meta))
                        (with-meta init-expr (select-keys form-meta [:line :column]))
                        init-expr)]
        (-> machine
            (m/replace-frame {:op :def :sym sym
                              :ns-sym (:current-ns machine)
                              :meta-map meta-map})
            (m/push-frame {:op :eval :expr init-expr}))))))

(defn step-def [machine frame]
  (let [sym (:sym frame)
        ns-sym (:ns-sym frame)
        qualified (symbol (str ns-sym) (str sym))
        val (:result machine)
        ;; If the value is a closure (IFn with :sci/closure meta), update its name.
        ;; Use :sci/def-named true to mark that this name came from def (not fn-name form),
        ;; so it won't be added to &env for recursion (matching Clojure behavior).
        val (if (and (fn? val) (:sci/closure (meta val)) (nil? (:name (meta val))))
              (vary-meta val assoc :name sym :ns ns-sym :sci/def-named true)
              val)
        meta-map (:meta-map frame)
        ;; Preserve :arglists/:doc from existing entry — deftype* constructors set these
        ;; before the host deftype macro expansion re-defs ->TypeName
        heap-for-meta (if-let [a (:heap-atom machine)] @a (:heap machine))
        existing-meta (:meta (get heap-for-meta qualified))
        meta-map (if existing-meta
                   (merge (select-keys existing-meta [:arglists :doc]) meta-map)
                   meta-map)
        entry {:val val :meta meta-map :dynamic? (:dynamic meta-map) :bound? true
               :const? (boolean (:const meta-map))
               :user-defined? true}]
    ;; Update both the immutable heap and the shared atom
    (when-let [a (:heap-atom machine)]
      (swap! a assoc qualified entry))
    (-> machine
        (assoc-in [:heap qualified] entry)
        (m/push-value (sci.lang/->Var (symbol (name qualified)) val
                                      (assoc meta-map :sci.impl/var-sym qualified)
                                      (:dynamic meta-map))))))

;; ============================================================
;; quote
;; ============================================================

(defn step-eval-quote [machine frame]
  (m/push-value machine (second (:expr frame))))

;; ============================================================
;; loop* / recur
;; ============================================================

(defn step-eval-loop [machine frame]
  (let [[_ bindings & body] (:expr frame)
        binding-pairs (vec (partition 2 bindings))
        body-vec (vec body)]
    ;; Check recur tail position only for user-written loop* forms
    (when (:line (meta (:expr frame)))
      (check-recur-tail-position [{:params (mapv first binding-pairs) :body body-vec}]))
    (m/replace-frame machine {:op :loop-init
                              :bindings binding-pairs
                              :body body-vec
                              :saved-env (:env machine)
                              :bind-idx 0})))

(defn step-loop-init [machine frame]
  (let [idx (:bind-idx frame)
        bindings (:bindings frame)]
    (if (nil? idx)
      ;; bind-result phase
      (let [sym (:bind-sym frame)
            val (:result machine)]
        (-> machine
            (update :env assoc sym val)
            (m/replace-frame (assoc frame :bind-idx (:next-idx frame)
                                    :bind-sym nil :next-idx nil))))
      (if (>= idx (count bindings))
        ;; All bound — start body
        (let [body (:body frame)
              params (mapv first bindings)]
          (if (empty? body)
            (-> machine
                (assoc :env (:saved-env frame))
                (m/push-value nil))
            (-> machine
                (m/replace-frame {:op :fn-body
                                  :body body
                                  :saved-env (:saved-env frame)
                                  :recur-target true
                                  :params params
                                  :loop? true
                                  :loop-body body
                                  :closure nil})
                (m/push-frame {:op :eval :expr (first body)}))))
        ;; Eval next binding
        (let [[sym expr] (nth bindings idx)]
          (-> machine
              (m/replace-frame (assoc frame :bind-idx nil
                                      :bind-sym sym
                                      :next-idx (inc idx)))
              (m/push-frame {:op :eval :expr expr})))))))

(defn step-eval-recur [machine frame]
  (let [args (vec (rest (:expr frame)))]
    (if (empty? args)
      (m/replace-frame machine {:op :recur :args []})
      (-> machine
          (m/replace-frame {:op :eval-recur-args
                            :pending (subvec args 1)
                            :done []})
          (m/push-frame {:op :eval :expr (nth args 0)})))))

(defn step-eval-recur-args [machine frame]
  (let [done (conj (:done frame) (:result machine))
        pending (:pending frame)]
    (if (empty? pending)
      (m/replace-frame machine {:op :recur :args done})
      (-> machine
          (m/replace-frame (assoc frame :done done
                                  :pending (subvec pending 1)))
          (m/push-frame {:op :eval :expr (nth pending 0)})))))

(defn step-recur [machine frame]
  (let [stack (:stack machine)]
    (loop [i (- (count stack) 2)]
      (if (neg? i)
        (throw (ex-info "Can only recur from tail position" {:type :sci/error}))
        (let [target (nth stack i)]
          (if (:recur-target target)
            (let [params (:params target)
                  new-args (:args frame)
                  bindings (zipmap (remove #{'&} params) new-args)
                  new-stack (subvec (vec stack) 0 (inc i))
                  body (or (:loop-body target) (:body target))]
              (-> machine
                  (assoc :stack new-stack)
                  (update :env merge bindings)
                  (m/replace-frame (assoc target :body (vec body)))
                  (m/push-frame {:op :eval :expr (first body)})))
            (recur (dec i))))))))

;; ============================================================
;; try / catch / throw
;; ============================================================

(defn step-eval-try [machine frame]
  (let [form (:expr frame)
        clauses (rest form)
        body (vec (remove #(and (seq? %)
                                (or (and (= 'catch (first %)) (>= (count %) 3))
                                    (= 'finally (first %)))) clauses))
        catches (vec (filter #(and (seq? %) (= 'catch (first %)) (>= (count %) 3)) clauses))
        finally-form (first (filter #(and (seq? %) (= 'finally (first %))) clauses))]
    ;; Validate catch class names at compile time
    #?(:clj (doseq [c catches]
              (let [[_ class-sym] c]
                (when (and (symbol? class-sym)
                           (not (try-resolve-class (str class-sym))))
                  (throw (ex-info (str "Unable to resolve classname: " class-sym)
                                  {:type :sci/error}))))))
    (let [m (m/replace-frame machine {:op :try
                                      :catches catches
                                      :finally finally-form
                                      :body body
                                      :phase :body})]
      (if (seq body)
        (m/push-frame m {:op :eval :expr (first body)})
        m))))

(defn step-try [machine frame]
  (case (:phase frame)
    :body
    (let [body (vec (rest (:body frame)))]
      (if (empty? body)
        (if (:finally frame)
          (-> machine
              (m/replace-frame (assoc frame :phase :finally
                                      :body-result (:result machine)))
              (m/push-frame {:op :eval :expr (cons 'do (rest (:finally frame)))}))
          (m/pop-frame machine))
        (-> machine
            (m/replace-frame (assoc frame :body body))
            (m/push-frame {:op :eval :expr (first body)}))))

    :finally
    (-> machine
        (assoc :result (:body-result frame))
        (m/pop-frame))

    :catch-body
    (if (:finally frame)
      (-> machine
          (m/replace-frame (assoc frame :phase :finally
                                  :body-result (:result machine)))
          (m/push-frame {:op :eval :expr (cons 'do (rest (:finally frame)))}))
      (m/pop-frame machine))))

;; ============================================================
;; var special form
;; ============================================================

(defn step-eval-var [machine frame]
  (let [[_ sym] (:expr frame)
        ns-sym (:current-ns machine)
        heap (if-let [a (:heap-atom machine)] @a (:heap machine))
        ;; Check if sym is a type name (deftype/defrecord create no var)
        type-name (symbol (name sym))
        type-obj (get-in machine [:ns ns-sym :types type-name])]
    (if type-obj
      (throw (ex-info (str "Unable to resolve var: " sym " in this context")
                      {:type :sci/error}))
      (let [qualified (if (qualified-symbol? sym)
                        sym
                        (let [local-q (symbol (str ns-sym) (str sym))]
                          (if (contains? heap local-q)
                            local-q
                            (let [core-q (symbol "clojure.core" (str sym))]
                              (if (contains? heap core-q)
                                core-q
                                local-q)))))
            entry (get heap qualified)
            ;; For raw :bindings entries (:user-binding? true), don't inject :name/:ns
            ;; so that clojure.repl/doc produces no output for undocumented plain bindings.
            extra-meta (if (:user-binding? entry)
                         {:sci.impl/var-sym qualified
                          :file (or (:file (:meta entry)) (:current-file machine))}
                         {:name (symbol (name qualified))
                          :ns (symbol (namespace qualified))
                          :sci.impl/var-sym qualified
                          :file (or (:file (:meta entry)) (:current-file machine))})
            var-obj (sci.lang/->Var (symbol (name qualified))
                                    (:val entry)
                                    (merge (:meta entry) extra-meta)
                                    (:dynamic? entry))]
        (m/push-value machine var-obj)))))

;; ============================================================
;; Dynamic binding + set!
;; ============================================================

(defn- resolve-var-qualified [machine sym]
  (let [sym-name (name sym)
        sym-ns (namespace sym)]
    (if sym-ns
      ;; Qualified symbol: resolve the namespace alias and return fully qualified
      (let [ns-table (:ns machine)
            current-ns (:current-ns machine)
            current-ns-data (get ns-table current-ns)
            resolved-ns (or (get (:aliases current-ns-data) (symbol sym-ns))
                            (get (:ns-aliases machine) (symbol sym-ns))
                            (symbol sym-ns))
            resolved-ns (or (get (:ns-aliases machine) resolved-ns) resolved-ns)]
        (symbol (str resolved-ns) sym-name))
      ;; Unqualified symbol: check current-ns heap, fallback to clojure.core
      (let [local-q (symbol (str (:current-ns machine)) sym-name)]
        (if (contains? (:heap machine) local-q)
          local-q
          (symbol "clojure.core" sym-name))))))

(defn step-eval-binding [machine frame]
  (let [[_ bindings & body] (:expr frame)
        _ (when-not (vector? bindings)
            (throw (ex-info "binding requires a vector for its bindings"
                            {:type :sci/error})))
        _ (when (odd? (count bindings))
            (throw (ex-info "binding requires an even number of forms in binding vector"
                            {:type :sci/error})))
        pairs (vec (partition 2 bindings))]
    (-> machine
        (m/replace-frame {:op :binding-init
                          :pairs pairs
                          :body (vec body)
                          :saved-dynamic-bindings (:dynamic-bindings machine)
                          :bind-idx 0}))))

#?(:clj
   (defn- try-resolve-real-var
     "If sym resolves to a real Clojure dynamic var, return it. Otherwise nil.
      Also tries clojure.core/ prefix for user/ vars like user/*in* → clojure.core/*in*."
     [qualified]
     (try
       (or (let [v (clojure.core/resolve qualified)]
             (when (and (var? v) (.isDynamic ^clojure.lang.Var v))
               v))
           ;; Try clojure.core/ version for user namespace vars
           (when (and (namespace qualified)
                      (not= "clojure.core" (namespace qualified)))
             (let [core-sym (symbol "clojure.core" (name qualified))
                   v (clojure.core/resolve core-sym)]
               (when (and (var? v) (.isDynamic ^clojure.lang.Var v))
                 v))))
       (catch Exception _ nil))))

(defn step-binding-init [machine frame]
  (let [idx (:bind-idx frame)
        pairs (:pairs frame)]
    (if (nil? idx)
      (let [sym (:bind-sym frame)
            qualified (resolve-var-qualified machine sym)
            val (:result machine)]
        (-> machine
            (assoc-in [:dynamic-bindings qualified] val)
            (m/replace-frame (assoc frame :bind-idx (:next-idx frame)
                                    :bind-sym nil :next-idx nil))))
      (if (>= idx (count pairs))
        (let [body (:body frame)
              ;; Push real JVM thread bindings for vars like *print-length*
              thread-bindings
              #?(:clj (reduce-kv
                       (fn [acc qualified val]
                         (if-let [real-var (try-resolve-real-var qualified)]
                           (assoc acc real-var val)
                           acc))
                       {}
                       (:dynamic-bindings machine))
                 :cljs nil)
              has-thread-bindings? #?(:clj (seq thread-bindings) :cljs false)]
          (when has-thread-bindings?
            #?(:clj (clojure.core/push-thread-bindings thread-bindings)))
          (if (empty? body)
            (do (when has-thread-bindings?
                  #?(:clj (clojure.core/pop-thread-bindings)))
                (-> machine
                    (assoc :dynamic-bindings (:saved-dynamic-bindings frame))
                    (m/push-value nil)))
            (-> machine
                (m/replace-frame {:op :binding-body
                                  :body (vec body)
                                  :saved-dynamic-bindings (:saved-dynamic-bindings frame)
                                  :has-thread-bindings? has-thread-bindings?})
                (m/push-frame {:op :eval :expr (first body)}))))
        (let [[sym expr] (nth pairs idx)]
          (-> machine
              (m/replace-frame (assoc frame :bind-idx nil
                                      :bind-sym sym
                                      :next-idx (inc idx)))
              (m/push-frame {:op :eval :expr expr})))))))

(defn step-binding-body [machine frame]
  (let [body (vec (rest (:body frame)))]
    (if (empty? body)
      (do (when (:has-thread-bindings? frame)
            #?(:clj (clojure.core/pop-thread-bindings)))
          (-> machine
              (assoc :dynamic-bindings (:saved-dynamic-bindings frame))
              (m/pop-frame)))
      (-> machine
          (m/replace-frame (assoc frame :body body))
          (m/push-frame {:op :eval :expr (first body)})))))

(defn step-eval-set! [machine frame]
  (let [[_ target-sym val-expr] (:expr frame)]
    (-> machine
        (m/replace-frame {:op :set!-apply :target-sym target-sym})
        (m/push-frame {:op :eval :expr val-expr}))))

(defn step-set!-apply [machine frame]
  (let [sym (:target-sym frame)
        val (:result machine)
        qualified (resolve-var-qualified machine sym)]
    (if (and (:dynamic-bindings machine)
             (contains? (:dynamic-bindings machine) qualified))
      (-> machine
          (assoc-in [:dynamic-bindings qualified] val)
          (m/push-value val))
      ;; Check if this is a dynamic var — if so, set! is only allowed inside binding
      (let [heap (if-let [a (:heap-atom machine)] @a (:heap machine))
            entry (get heap qualified)]
        (if (and (:dynamic? entry) (:user-defined? entry))
          ;; User-defined dynamic var: set! outside binding is an error (Clojure semantics)
          (throw (ex-info (str "Can't set! root binding of dynamic var: " qualified)
                          {:type :sci/error}))
          ;; Non-dynamic var: update root binding in heap
          (let [new-entry (assoc entry :val val)]
            (when-let [a (:heap-atom machine)]
              (swap! a assoc qualified new-entry))
            (-> machine
                (assoc-in [:heap qualified] new-entry)
                (m/push-value val))))))))

;; ============================================================
;; new
;; ============================================================

(defn step-eval-new [machine frame]
  ;; (new ClassName args...)
  (let [[_ class-sym & arg-exprs] (:expr frame)]
    ;; Evaluate the class symbol first, then args
    (-> machine
        (m/replace-frame {:op :eval-args
                          :pending (vec arg-exprs)
                          :done []
                          :phase :eval-f
                          :new? true})
        (m/push-frame {:op :eval :expr class-sym}))))

;; ============================================================
;; . (dot) — Java interop
;; ============================================================

#?(:clj
   (defn step-eval-dot [machine frame]
     ;; (. obj method args...) or (. obj (method args...)) or (. obj -field)
     (let [form (:expr frame)
           [_ obj-expr method-or-call & args] form
           _ (when (nil? method-or-call)
               (throw (IllegalArgumentException.
                       "Malformed member expression, expecting (. target member ...)")))
           [method-name method-args]
           (if (seq? method-or-call)
             [(first method-or-call) (rest method-or-call)]
             [method-or-call args])
           method-str (name method-name) ;; use name to strip namespace (e.g. clojure.core/close → close)
           is-field? (.startsWith ^String method-str "-")]
       (-> machine
           (m/replace-frame {:op :eval-args
                             :pending (vec method-args)
                             :done []
                             :phase :eval-f
                             :dot? true
                             :method-name (if is-field?
                                            (symbol (subs method-str 1))
                                            (symbol method-str))
                             :field? is-field?})
           (m/push-frame {:op :eval :expr obj-expr}))))
   :cljs
   (defn step-eval-dot [machine frame]
     (throw (ex-info ". interop not implemented for ClojureScript" {}))))

;; ============================================================
;; import*
;; ============================================================

(defn- try-resolve-sci-type
  "Try to resolve a dotted class-name string as an SCI type from another namespace.
   E.g. 'bar.Foo' → looks up [:ns 'bar :types 'Foo]. Returns type-obj or nil."
  [machine class-name]
  #?(:clj
     (let [idx (.lastIndexOf ^String class-name ".")]
       (when (> idx 0)
         (let [ns-str (subs class-name 0 idx)
               type-str (subs class-name (inc idx))
               ;; Also try un-munged namespace (underscores → dashes)
               ns-str-unm (clojure.string/replace ns-str "_" "-")]
           (or (get-in machine [:ns (symbol ns-str) :types (symbol type-str)])
               (get-in machine [:ns (symbol ns-str-unm) :types (symbol type-str)])))))
     :cljs nil))

(defn step-eval-import [machine frame]
  ;; (import* "fully.qualified.ClassName")
  (let [[_ class-str] (:expr frame)]
    #?(:clj
       (let [klass (try (Class/forName class-str)
                        (catch ClassNotFoundException _ nil))
             sci-type (when-not klass (try-resolve-sci-type machine class-str))]
         (cond
           klass
           (let [short-name (symbol (.getSimpleName ^Class klass))
                 cur-ns (:current-ns machine)]
             (-> machine
                 (update :env assoc short-name klass)
                 (update-in [:ns cur-ns :imports] assoc short-name klass)
                 (m/push-value klass)))
           sci-type
           (let [idx (.lastIndexOf ^String class-str ".")
                 short-name (symbol (subs class-str (inc idx)))
                 cur-ns (:current-ns machine)]
             (-> machine
                 (update :env assoc short-name sci-type)
                 (update-in [:ns cur-ns :types] assoc short-name sci-type)
                 (update-in [:ns cur-ns :imports] assoc short-name sci-type)
                 (m/push-value sci-type)))
           :else
           (throw (ex-info (str "Unable to resolve classname: " class-str)
                           {:type :sci/error}))))
       :cljs
       (throw (ex-info "import not supported in ClojureScript" {})))))

;; ============================================================
;; Multimethods
;; ============================================================

(defn- make-multimethod
  "Create a multimethod: a callable fn that dispatches based on a dispatch-fn."
  [mm-name dispatch-fn]
  (let [methods-atom (atom {})
        prefer-table (atom {})
        mm (fn multimethod [& args]
             (let [dispatch-val (apply dispatch-fn args)
                   methods @methods-atom
                   method (or (get methods dispatch-val)
                              ;; Check hierarchy (isa?)
                              (first (filter some?
                                             (map (fn [[k v]]
                                                    (when (isa? dispatch-val k) v))
                                                  methods)))
                              (get methods :default))]
               (if method
                 (apply method args)
                 (throw (ex-info (str "No method in multimethod '" mm-name
                                      "' for dispatch value: " (pr-str dispatch-val))
                                 {:type :sci/error})))))]
    (with-meta mm {:type :sci/multimethod
                   :name mm-name
                   :methods methods-atom
                   :prefer-table prefer-table
                   :dispatch-fn dispatch-fn})))

(defn step-eval-defmulti [machine frame]
  ;; (defmulti name dispatch-fn)
  (let [[_ mm-name dispatch-fn-form] (:expr frame)]
    (-> machine
        (m/replace-frame {:op :defmulti-apply :mm-name mm-name})
        (m/push-frame {:op :eval :expr dispatch-fn-form}))))

(defn step-defmulti-apply [machine frame]
  (let [dispatch-fn (:result machine)
        mm-name (:mm-name frame)
        mm (make-multimethod mm-name dispatch-fn)
        ns-sym (:current-ns machine)
        qualified (symbol (str ns-sym) (str mm-name))
        entry {:val mm :meta {} :dynamic? false}]
    (when-let [a (:heap-atom machine)]
      (swap! a assoc qualified entry))
    (-> machine
        (assoc-in [:heap qualified] entry)
        (update :env assoc mm-name mm)
        (m/push-value mm))))

(defn step-eval-defmethod [machine frame]
  ;; (defmethod mm-name dispatch-val fn-form) or (defmethod mm-name dispatch-val [args] body)
  (let [form (:expr frame)
        [_ mm-ref dispatch-val & fn-parts] form
        ;; Build the fn form
        fn-form (if (vector? (first fn-parts))
                  ;; Single arity: (defmethod foo :bar [x] body)
                  (list* 'fn* fn-parts)
                  ;; Multi-arity: (defmethod foo :bar ([x] body1) ([x y] body2))
                  (list* 'fn* fn-parts))]
    ;; Evaluate the multimethod reference, dispatch-val, and the method fn
    (-> machine
        (m/replace-frame {:op :eval-args
                          :pending [dispatch-val fn-form]
                          :done []
                          :phase :eval-f
                          :defmethod? true})
        (m/push-frame {:op :eval :expr mm-ref}))))

(defn step-eval-remove-method [machine frame]
  (let [[_ mm-ref dispatch-val] (:expr frame)]
    (-> machine
        (m/replace-frame {:op :eval-args
                          :pending [(list 'quote dispatch-val)]
                          :done []
                          :phase :eval-f
                          :remove-method? true})
        (m/push-frame {:op :eval :expr mm-ref}))))

(defn step-eval-prefer-method [machine frame]
  (let [[_ mm-ref preferred other] (:expr frame)]
    (-> machine
        (m/replace-frame {:op :eval-args
                          :pending [(list 'quote preferred) (list 'quote other)]
                          :done []
                          :phase :eval-f
                          :prefer-method? true})
        (m/push-frame {:op :eval :expr mm-ref}))))

;; ============================================================
;; Protocols
;; ============================================================

(defn- make-protocol
  "Create a protocol record."
  [proto-name method-sigs ns-sym opts]
  {:type :sci/protocol
   :name proto-name
   :ns ns-sym
   :methods method-sigs
   :extend-via-metadata (:extend-via-metadata opts)
   :impls (atom {})}) ;; type -> {method-name -> fn}

(defn step-eval-defprotocol [machine frame]
  ;; (defprotocol Name :extend-via-metadata true (method1 [this]) (method2 [this x]))
  (let [[_ proto-name & method-defs] (:expr frame)
        ns-sym (:current-ns machine)
        ;; Parse options like :extend-via-metadata true
        [opts method-defs] (loop [opts {} remaining method-defs]
                             (if (keyword? (first remaining))
                               (recur (assoc opts (first remaining) (second remaining))
                                      (drop 2 remaining))
                               [opts remaining]))
        ;; Parse method signatures
        method-sigs (into {} (keep (fn [md]
                                     (when (seq? md)
                                       (let [mname (first md)
                                             arglists (rest md)
                                             ;; Filter out docstrings
                                             arglists (remove string? arglists)]
                                         [mname {:arglists (vec arglists)}])))
                                   method-defs))
        ;; Build :sigs map for protocol introspection
        sigs-map (reduce-kv (fn [acc mname {:keys [arglists]}]
                              (let [doc-str (some (fn [md]
                                                    (when (and (seq? md) (= mname (first md)))
                                                      ;; docstring can be second element or last element
                                                      (let [parts (rest md)]
                                                        (or (when (string? (last parts)) (last parts))
                                                            (when (string? (first parts)) (first parts))))))
                                                  method-defs)]
                                (assoc acc (keyword mname)
                                       {:name mname :arglists (apply list arglists) :doc doc-str})))
                            {} method-sigs)
        protocol (assoc (make-protocol proto-name method-sigs ns-sym opts)
                        :sigs sigs-map)
        qualified (symbol (str ns-sym) (str proto-name))
        ;; Create dispatch functions for each protocol method
        machine (reduce
                 (fn [m [mname {:keys [arglists]}]]
                   (let [extend-via-meta? (:extend-via-metadata protocol)
                         mname-qualified (symbol (str ns-sym) (str mname))
                         method-fn (fn protocol-dispatch [& args]
                                     (let [target (first args)
                                           ;; extend-via-metadata: check target's metadata first
                                           meta-fn (when extend-via-meta?
                                                     (when-let [m (clojure.core/meta target)]
                                                       (or (get m mname-qualified)
                                                           (get m (symbol (name mname))))))]
                                       (if meta-fn
                                         (apply meta-fn args)
                                     (let [;; For SCI type instances (maps with :type meta), use SCI type
                                           sci-type (when (map? target) (:type (clojure.core/meta target)))
                                           target-type (or sci-type (type target))
                                           impls @(:impls protocol)
                                           ;; Look up implementation: exact type, then IRecord, then interfaces, then Object
                                           impl (or (get impls target-type)
                                                    ;; SCI records: check IRecord/IPersistentMap before Object
                                                    (when (:sci.impl/record (clojure.core/meta target))
                                                      (or (get impls clojure.lang.IRecord)
                                                          (get impls clojure.lang.IPersistentMap)))
                                                    ;; Check interfaces (excluding Object — handled below)
                                                    (some (fn [[t impl]]
                                                            (when (and (class? t)
                                                                       (not= t Object)
                                                                       (instance? t target))
                                                              impl))
                                                          impls)
                                                    ;; Try nil
                                                    (when (nil? target) (get impls nil))
                                                    ;; Try Object/:default
                                                    (get impls Object)
                                                    (get impls :default))]
                                       (if-let [f (or (get impl mname)
                                                           (get impl (keyword mname))
                                                           (get impl (symbol mname)))]
                                         (apply f args)
                                         (throw (ex-info (str "No implementation of method: " mname
                                                              " of protocol: " proto-name
                                                              " found for: " (type target))
                                                         {:type :sci/error})))))))
                         mq (symbol (str ns-sym) (str mname))
                         method-arglists arglists
                         ;; Find docstring for this method (immediately after the method-name in the definition)
                         method-doc (some (fn [md]
                                            (when (and (seq? md) (= mname (first md)))
                                              (let [second-el (second md)]
                                                (when (string? second-el) second-el))))
                                          method-defs)
                         entry {:val method-fn
                                :meta {:protocol protocol
                                       :name mname
                                       :ns (symbol (str ns-sym))
                                       :arglists (vec method-arglists)
                                       :doc method-doc}
                                :dynamic? false}]
                     (when-let [a (:heap-atom m)]
                       (swap! a assoc mq entry))
                     (-> m
                         (assoc-in [:heap mq] entry)
                         (update :env assoc mname method-fn))))
                 machine
                 method-sigs)
        ;; Store the protocol itself
        proto-entry {:val protocol :meta {} :dynamic? false}]
    (when-let [a (:heap-atom machine)]
      (swap! a assoc qualified proto-entry))
    (-> machine
        (assoc-in [:heap qualified] proto-entry)
        (update :env assoc proto-name protocol)
        (m/push-value proto-name))))

(defn step-eval-extend [machine frame]
  ;; (extend Type Protocol {:method-name fn ...})
  (let [[_ type-expr proto-expr impl-map-expr] (:expr frame)]
    (-> machine
        (m/replace-frame {:op :eval-args
                          :pending [proto-expr impl-map-expr]
                          :done []
                          :phase :eval-f
                          :extend? true})
        (m/push-frame {:op :eval :expr type-expr}))))

(defn- do-extend
  "Register protocol implementations for a type."
  [protocol target-type impl-map]
  (swap! (:impls protocol) assoc target-type impl-map))

(defn step-eval-extend-type [machine frame]
  ;; (extend-type Type Protocol1 (method1 [this] ...) Protocol2 ...)
  (let [[_ type-sym & specs] (:expr frame)
        ;; Parse specs into protocol -> {method -> fn} pairs
        ;; Group specs by protocol
        groups (loop [specs specs groups []]
                 (if (empty? specs)
                   groups
                   (let [proto-sym (first specs)
                         methods (take-while seq? (rest specs))
                         remaining (drop-while seq? (rest specs))]
                     (recur remaining
                            (conj groups {:proto proto-sym :methods methods})))))
        ;; Build a do form that evaluates extend for each protocol
        extend-forms (mapv (fn [{:keys [proto methods]}]
                             (let [impl-map (into {}
                                                  (map (fn [method-form]
                                                         (let [mname (first method-form)
                                                               ;; Normalize to unqualified name
                                                               mname (symbol (name mname))
                                                               args-body (rest method-form)]
                                                           [(list 'quote mname)
                                                            (list* 'fn* args-body)]))
                                                       methods))]
                               (list 'extend type-sym proto impl-map)))
                           groups)
        do-form (cons 'do extend-forms)]
    (m/replace-frame machine {:op :eval :expr do-form})))

(defn step-eval-extend-protocol [machine frame]
  ;; (extend-protocol Protocol Type1 (method [this] ...) Type2 (method [this] ...) ...)
  (let [[_ proto-sym & specs] (:expr frame)
        ;; Group specs by type
        groups (loop [specs specs groups []]
                 (if (empty? specs)
                   groups
                   (let [type-sym (first specs)
                         methods (take-while seq? (rest specs))
                         remaining (drop-while seq? (rest specs))]
                     (recur remaining
                            (conj groups {:type type-sym :methods methods})))))
        ;; Build extend-type forms
        extend-forms (mapv (fn [{:keys [type methods]}]
                             (list* 'extend-type type proto-sym methods))
                           groups)
        do-form (cons 'do extend-forms)]
    (m/replace-frame machine {:op :eval :expr do-form})))

;; ============================================================
;; letfn*
;; ============================================================

(defn step-eval-letfn [machine frame]
  ;; (letfn* [name1 (fn* name1 [args] body) ...] body...)
  ;; Transform into: define each fn using def (so they go in heap for mutual recursion),
  ;; then evaluate body in a scope where the names are bound.
  (let [[_ bindings & body] (:expr frame)
        pairs (vec (partition 2 bindings))
        ;; Propagate source location to inner fn forms for recur checking
        loc-meta (select-keys (meta (:expr frame)) [:line :column])
        ;; Build a do form: (do (def name1 (fn* ...)) (def name2 (fn* ...)) ... body...)
        defs (mapv (fn [[fname fn-form]]
                     (let [fn-form (if (and (seq loc-meta) (not (meta fn-form)))
                                     (with-meta fn-form loc-meta)
                                     fn-form)]
                       (list 'def fname fn-form)))
                   pairs)
        ;; Wrap names in let bindings after defs so they're in local scope
        fn-names (mapv first pairs)
        let-bindings (vec (mapcat (fn [n] [n n]) fn-names))
        transformed (list* 'do (concat defs [(list* 'let* let-bindings body)]))]
    (m/replace-frame machine {:op :eval :expr transformed})))

;; ============================================================
;; defmacro
;; ============================================================

(defn step-eval-defmacro [machine frame]
  ;; (defmacro name [params] body) → defines a macro in the heap
  (let [form (:expr frame)
        [_ macro-name & rest-form] form
        ;; Parse like fn — then prepend &form and &env to each arity's params
        parsed (parse-fn-form (list* 'fn* rest-form))
        ;; Prepend &form &env to all arities so macros can use &form and &env
        ns-sym (:current-ns machine)
        arities-with-implicit (mapv (fn [arity]
                                      (update arity :params #(into ['&form '&env] %)))
                                    (:arities parsed))
        closure-map {:type :closure
                     :name macro-name
                     :ns ns-sym
                     :arities arities-with-implicit
                     :env (:env machine)}
        ;; Callable takes &form &env then the real args
        callable (make-callable-closure closure-map machine)
        qualified (symbol (str ns-sym) (str macro-name))
        macro-meta (merge {:macro true
                           :name macro-name
                           :ns ns-sym
                           ;; Arglists show the user-visible params (without &form &env)
                           :arglists (apply list (mapv :params (:arities parsed)))}
                          (when-let [ds (:docstring parsed)]
                            {:doc ds})
                          (:attr-map parsed))
        entry {:val callable :meta macro-meta :macro? true}]
    (when-let [a (:heap-atom machine)]
      (swap! a assoc qualified entry))
    (-> machine
        (assoc-in [:heap qualified] entry)
        (m/push-value (sci.lang/->Var (symbol (str macro-name)) callable
                                      (assoc macro-meta :sci.impl/var-sym qualified)
                                      false)))))

;; ============================================================
;; ns / in-ns / require
;; ============================================================

(defn- sync-ns-atom!
  "Sync the machine's :ns map to the :ns-atom if present."
  [machine]
  (when-let [a (:ns-atom machine)]
    (reset! a (:ns machine)))
  machine)

(defn step-eval-in-ns [machine frame]
  (let [[_ ns-sym-expr] (:expr frame)]
    ;; Evaluate the ns symbol
    (-> machine
        (m/replace-frame {:op :in-ns-apply})
        (m/push-frame {:op :eval :expr ns-sym-expr}))))

(defn step-in-ns-apply [machine frame]
  (let [ns-sym (:result machine)]
    (when-let [a (:current-ns-atom machine)]
      (reset! a ns-sym))
    (-> machine
        (assoc :current-ns ns-sym)
        (update :ns #(if (get % ns-sym) % (assoc % ns-sym {:aliases {} :refers {} :imports {}})))
        sync-ns-atom!
        (m/push-value ns-sym))))

(defn- load-ns-if-needed
  "If the namespace isn't loaded and a load-fn is available, load it."
  ([machine ns-sym] (load-ns-if-needed machine ns-sym nil))
  ([machine ns-sym require-opts]
   (let [ns-table (:ns machine)
         loaded? (contains? ns-table ns-sym)
         ns-str (str ns-sym)
         ;; Also check if any vars exist in the heap for this namespace
         heap-has-ns? (when-not loaded?
                        (let [heap (if-let [a (:heap-atom machine)] @a (:heap machine))]
                          (some (fn [[k _]] (= ns-str (namespace k))) heap)))]
     (if (and (or loaded?
                  heap-has-ns?
                  (contains? (set host/default-namespaces) ns-sym)
                  (get (:ns-aliases machine) ns-sym))
              (not (:force-reload machine)))
       machine ;; already loaded or aliased
       ;; Cyclic load detection
       (let [loading (or (:loading machine) #{})
             _ (when (contains? loading ns-sym)
                 (let [chain (:loading-chain machine)
                       ;; Find where ns-sym first appears in chain
                       cycle-start (or (some (fn [i] (when (= (get chain i) ns-sym) i))
                                             (range (count chain)))
                                       0)
                       cycle-chain (subvec chain cycle-start)
                       middle (clojure.string/join "->" (map str (rest cycle-chain)))]
                   (throw (ex-info (str "Cyclic load dependency: [ " (first cycle-chain) " ]->"
                                        middle "->[ " ns-sym " ]")
                                   {:type :sci/error}))))]
         (if-let [load-fn (:load-fn machine)]
           (let [current-ns (:current-ns machine)
                 result (load-fn {:namespace ns-sym
                                  :libname ns-sym
                                  :ctx (or (:ctx machine) machine)
                                  :ns current-ns
                                  :opts (or require-opts {})})]
             (if result
               ;; Evaluate the loaded source
               (let [source (:source result)
                     forms (edamame/parse-string-all source
                                                     {:all true :read-cond :allow :features #{:clj}
                                                      :fn true :quote true :var true :deref true :regex true
                                                      :location? seq? :row-key :line :col-key :column})
                     expr (if (= 1 (count forms)) (first forms) (cons 'do forms))
                     heap-atom (:heap-atom machine)
                     m2 (-> (m/make-machine {:heap (if heap-atom @heap-atom (:heap machine))
                                             :ns-table (:ns machine)})
                            (assoc :heap-atom heap-atom
                                   :ns-atom (:ns-atom machine)
                                   :load-fn load-fn
                                   :ctx (:ctx machine)
                                   :loading (conj loading ns-sym)
                                   :loading-chain (conj (or (:loading-chain machine) []) ns-sym)
                                   :current-ns ns-sym)
                            ;; Propagate reload-all to sub-machine so transitive deps reload
                            (cond-> (:reload-all machine)
                              (assoc :force-reload true :reload-all true))
                            (m/push-frame {:op :eval :expr expr}))]
                 (run m2)
                 ;; Return machine with updated heap and ns table
                 ;; Merge ns-atom changes (from sub-machine's ns form and transitive requires)
                 (let [loaded-ns (when-let [a (:ns-atom machine)] @a)]
                   (cond-> machine
                     heap-atom (assoc :heap @heap-atom)
                     loaded-ns (assoc :ns (merge (:ns machine) loaded-ns))
                     (not loaded-ns) (update :ns assoc ns-sym {:aliases {} :refers {} :imports {}}))))
               (throw (ex-info (str "Could not locate " (clojure.string/replace ns-str "." "/")
                                    "__init.class, " (clojure.string/replace ns-str "." "/")
                                    ".clj or " (clojure.string/replace ns-str "." "/")
                                    ".cljc on classpath.")
                               {:type :sci/error}))))
           (throw (ex-info (str "Could not locate " (clojure.string/replace ns-str "." "/")
                                "__init.class, " (clojure.string/replace ns-str "." "/")
                                ".clj or " (clojure.string/replace ns-str "." "/")
                                ".cljc on classpath.")
                           {:type :sci/error}))))))))

(defn- process-require-spec
  "Process a single require spec and update the machine's ns table."
  [machine spec]
  (let [current-ns (:current-ns machine)]
    (cond
      ;; Simple symbol: (require 'foo)
      (symbol? spec)
      (-> (load-ns-if-needed machine spec)
          (update-in [:ns current-ns :aliases] assoc spec spec))

      ;; Vector spec: (require '[foo :as f :refer [x y]])
      ;; Or nested: (require '[clojure [set :refer [union]] [string :as str]])
      (vector? spec)
      (let [first-elem (first spec)
            nested? (and (symbol? first-elem)
                         (> (count spec) 1)
                         (vector? (second spec)))]
        (if nested?
          ;; Nested: expand prefix and process each sub-spec
          (let [prefix first-elem]
            (reduce (fn [m sub-spec]
                      (let [expanded (if (symbol? sub-spec)
                                       [(symbol (str prefix "." sub-spec))]
                                       (vec (cons (symbol (str prefix "." (first sub-spec)))
                                                  (rest sub-spec))))]
                        (process-require-spec m expanded)))
                    machine
                    (rest spec)))
          ;; Normal: [ns-sym :as alias :refer [syms] :as-alias alias]
          (let [ns-sym first-elem
                opts (apply hash-map (rest spec))
                refers (:refer opts)
                rename-map (or (:rename opts) {})
                _ (when (and refers (not= refers :all) (not (sequential? refers)))
                    (throw (ex-info (str ":refer must be a sequential collection, got: " (pr-str refers))
                                    {:type :sci/error})))
                as-alias-sym (:as-alias opts)
                ;; Don't load the namespace if only :as-alias is used
                machine (if (and as-alias-sym (not (:as opts)) (not refers))
                          machine  ;; :as-alias only — skip loading
                          (load-ns-if-needed machine ns-sym (dissoc opts :as :refer :rename :as-alias)))
                alias-sym (or (:as opts) as-alias-sym)]
            (cond-> machine
              alias-sym (update-in [:ns current-ns :aliases] assoc alias-sym ns-sym)
              (= :all refers)
              (as-> m
                    (let [heap (if-let [a (:heap-atom m)] @a (:heap m))
                          ns-str (str ns-sym)
                          entries (filter (fn [[k _]] (= ns-str (namespace k))) heap)]
                      (reduce (fn [m [k entry]]
                                (let [sym-name (symbol (name k))
                                      renamed (get rename-map sym-name)
                                      target-name (or renamed sym-name)
                                      target-sym (symbol (str current-ns) (str target-name))]
                                  (when-let [a (:heap-atom m)]
                                    (swap! a assoc target-sym entry))
                                  (assoc-in m [:heap target-sym] entry)))
                              m entries)))
              (sequential? refers)
              (as-> m
                    (reduce (fn [m sym]
                              (let [qualified (symbol (str ns-sym) (str sym))
                                    heap (if-let [a (:heap-atom m)] @a (:heap m))]
                                (if-let [entry (get heap qualified)]
                                  (let [renamed (get rename-map sym)
                                        target-name (or renamed sym)
                                        target-sym (symbol (str current-ns) (str target-name))
                                    ;; Tag referred entries with original var-sym for syntax-quote
                                        entry' (update entry :meta
                                                       #(assoc (or % {}) :sci.impl/var-sym qualified))]
                                    (when-let [a (:heap-atom m)]
                                      (swap! a assoc target-sym entry'))
                                    (assoc-in m [:heap target-sym] entry'))
                                  (throw (ex-info (str sym " does not exist in " ns-sym)
                                                  {:type :sci/error})))))
                            m
                            refers))))))

      :else machine)))

(defn step-eval-require [machine frame]
  (let [specs (rest (:expr frame))
        ;; Unquote specs — require args are quoted
        specs (map (fn [s] (if (and (seq? s) (= 'quote (first s))) (second s) s)) specs)
        ;; Extract flags (:reload, :reload-all)
        flags (set (filter keyword? specs))
        specs (remove keyword? specs)
        ;; If :reload, force re-loading by clearing loaded ns entries
        machine (if (or (:reload flags) (:reload-all flags))
                  (cond-> (assoc machine :force-reload true)
                    (:reload-all flags) (assoc :reload-all true))
                  machine)
        machine (reduce process-require-spec machine specs)
        machine (dissoc machine :force-reload :reload-all)]
    (m/push-value (sync-ns-atom! machine) nil)))

(defn step-eval-ns [machine frame]
  ;; (ns name docstring? attr-map? & references)
  ;; Simplified: switch namespace + process :require, :import etc.
  (let [[_ ns-sym & rest-form] (:expr frame)
        _ (when-not (symbol? ns-sym)
            (throw (ex-info (str "Namespace name must be a symbol, got: " (pr-str ns-sym))
                            {:type :sci/error})))
        ;; Skip optional docstring
        [docstring rest-form] (if (string? (first rest-form))
                                [(first rest-form) (next rest-form)]
                                [nil rest-form])
        ;; Skip optional attr-map
        [attr-map refs] (if (and (map? (first rest-form))
                                 (not (keyword? (ffirst rest-form))))
                          [(first rest-form) (next rest-form)]
                          [nil rest-form])
        _ (when-let [a (:current-ns-atom machine)]
            (reset! a ns-sym))
        ns-meta (merge (meta ns-sym) attr-map (when docstring {:doc docstring}))
        machine (-> machine
                    (assoc :current-ns ns-sym)
                    (update :ns #(let [existing (get % ns-sym)
                                          ;; Preserve structural data, replace metadata
                                       structural (select-keys existing [:aliases :refers :imports])]
                                   (assoc % ns-sym
                                          (merge {:aliases {} :refers {} :imports {}}
                                                 structural
                                                 (when ns-meta ns-meta))))))]
    ;; Process references like (:require ...) (:import ...)
    (let [machine (reduce
                   (fn [m ref]
                     (if (seq? ref)
                       (let [ref-type (first ref)
                             ref-specs (rest ref)]
                         (case ref-type
                           :require (reduce process-require-spec m ref-specs)
                           :import (reduce (fn [m' imp-spec]
                                             (if (sequential? imp-spec)
                                               (let [pkg (first imp-spec)
                                                     classes (rest imp-spec)]
                                                 (reduce (fn [m'' cls]
                                                           (let [fqn (str pkg "." cls)
                                                                 short (symbol (str cls))]
                                                             #?(:clj
                                                                (let [klass (try (Class/forName fqn)
                                                                                 (catch ClassNotFoundException _ nil))
                                                                      sci-type (when-not klass (try-resolve-sci-type m'' fqn))]
                                                                  (cond
                                                                    klass (update m'' :env assoc short klass)
                                                                    sci-type (-> m''
                                                                                 (update :env assoc short sci-type)
                                                                                 (update-in [:ns ns-sym :types] assoc short sci-type))
                                                                    :else (let [ref-loc (form-location ref)]
                                                                            (throw (ex-info (str "Unable to resolve classname: " fqn)
                                                                                            (merge {:type :sci/error
                                                                                                    :sci.impl/callstack (when ref-loc
                                                                                                                          [{:ns (:current-ns m'')
                                                                                                                            :name (:current-fn-name m'')
                                                                                                                            :line (:line ref-loc)
                                                                                                                            :column (:column ref-loc)
                                                                                                                            :file (:current-file m'')}])}
                                                                                                   (when ref-loc
                                                                                                     {:line (:line ref-loc)
                                                                                                      :column (:column ref-loc)})))))))
                                                                :cljs m'')))
                                                         m' classes))
                                               m'))
                                           m ref-specs)
                           :refer-clojure
                           (let [opts (apply hash-map ref-specs)
                                 exclude-syms (set (:exclude opts))
                                 rename-map (or (:rename opts) {})]
                             (as-> m m'
                               (if (seq exclude-syms)
                                 (update-in m' [:ns ns-sym :refer-clojure-excludes]
                                            (fnil into #{}) exclude-syms)
                                 m')
                               ;; :rename — add renamed aliases + exclude originals
                               (if (seq rename-map)
                                 (let [heap-atom (:heap-atom m')
                                       heap (if heap-atom @heap-atom (:heap m'))]
                                   (reduce (fn [m'' [orig-sym new-sym]]
                                             (let [qualified (symbol "clojure.core" (str orig-sym))]
                                               (if-let [entry (get heap qualified)]
                                                 (let [target (symbol (str ns-sym) (str new-sym))
                                                       entry' (update entry :meta
                                                                      #(assoc (or % {}) :sci.impl/var-sym qualified))]
                                                   (when heap-atom (swap! heap-atom assoc target entry'))
                                                   (-> m''
                                                       (assoc-in [:heap target] entry')
                                                       (update-in [:ns ns-sym :refer-clojure-excludes]
                                                                  (fnil conj #{}) orig-sym)))
                                                 m'')))
                                           m'
                                           rename-map))
                                 m')))
                           :use
                           (reduce (fn [m' use-spec]
                                     ;; (use 'clojure.set) or (use '[clojure.set :only [union]])
                                     (let [spec (if (and (seq? use-spec) (= 'quote (first use-spec)))
                                                  (second use-spec)
                                                  use-spec)
                                           [ns-sym opts] (if (sequential? spec)
                                                           [(first spec) (apply hash-map (rest spec))]
                                                           [spec nil])
                                           ;; First require the namespace
                                           m' (process-require-spec m' (if opts
                                                                         (vec (cons ns-sym (mapcat identity opts)))
                                                                         ns-sym))
                                           ;; Then refer all public vars (or :only)
                                           only-syms (:only opts)
                                           heap-atom (:heap-atom m')
                                           heap (if heap-atom @heap-atom (:heap m'))
                                           ns-str (str ns-sym)]
                                       (reduce-kv (fn [m'' k v]
                                                    (if (and (= ns-str (namespace k))
                                                             (or (nil? only-syms)
                                                                 (contains? (set only-syms)
                                                                            (symbol (name k)))))
                                                      (let [target (symbol (str (:current-ns m'')) (name k))]
                                                        (when heap-atom
                                                          (swap! heap-atom assoc target v))
                                                        (assoc-in m'' [:heap target] v))
                                                      m''))
                                                  m' heap)))
                                   m ref-specs)
                           m))
                       m))
                   machine
                   refs)]
      (m/push-value (sync-ns-atom! machine) ns-sym))))

;; ============================================================
;; case*
;; ============================================================

(defn step-eval-case [machine frame]
  ;; (case* expr shift mask default map mode keys)
  (let [[_ expr shift mask default case-map mode keys-type] (:expr frame)]
    (-> machine
        (m/replace-frame {:op :case*
                          :default default
                          :case-map case-map})
        (m/push-frame {:op :eval :expr expr}))))

(defn step-case* [machine frame]
  (let [val (:result machine)
        case-map (:case-map frame)
        default (:default frame)]
    ;; case-map is {hash [test-val result-expr], ...}
    ;; Find matching entry
    (let [match (some (fn [[_ [test-val result-expr]]]
                        (when (= val test-val)
                          result-expr))
                      case-map)]
      (if match
        (m/replace-frame machine {:op :eval :expr match})
        (m/replace-frame machine {:op :eval :expr default})))))

;; ============================================================
;; suspend!
;; ============================================================

(defn step-eval-suspend [machine frame]
  (let [args (rest (:expr frame))]
    (if (empty? args)
      ;; (suspend!) — no data, suspend immediately
      (-> machine
          (m/pop-frame)
          (assoc :status :suspend :suspend-data nil))
      ;; (suspend! expr) — evaluate the expression first, then suspend
      (-> machine
          (m/replace-frame {:op :suspend-apply})
          (m/push-frame {:op :eval :expr (first args)})))))

(defn step-suspend-apply [machine _frame]
  (-> machine
      (m/pop-frame)
      (assoc :status :suspend :suspend-data (:result machine))))

;; ============================================================
;; deftype*
;; ============================================================

(defn- make-deftype-method-fn
  "Create a Clojure closure for a deftype method.
   fields = field-name symbols; params = [this ...]; body = seq of exprs."
  [machine ns-sym fields params body]
  (let [heap-atom (:heap-atom machine)
        ns-atom   (:ns-atom machine)
        base-env  (:env machine)]
    (fn [& args]
      (let [this-obj       (first args)
            ;; Bind field values from the instance map
            field-bindings (zipmap fields (map #(get this-obj (keyword %)) fields))
            fn-env         (merge base-env field-bindings (zipmap params args))
            heap           (if heap-atom @heap-atom (:heap machine))
            ;; Use latest ns-table (picks up types defined after this closure was created)
            ns-table       (if ns-atom @ns-atom (:ns machine))
            mini-m         (-> (m/make-machine {:heap heap :ns-table ns-table})
                               (assoc :env fn-env
                                      :heap-atom heap-atom
                                      :ns-atom ns-atom
                                      :current-ns ns-sym)
                               (m/push-frame {:op :eval
                                              :expr (if (= 1 (count body))
                                                      (first body)
                                                      (cons 'do body))}))]
        (run mini-m)))))

(defn step-eval-deftype* [machine frame]
  ;; (deftype* qualified-sym dotted-sym [fields] :implements [Proto1 ...] (method [this] body) ...)
  (let [form (:expr frame)
        parts         (vec (rest form))
        qualified-sym (nth parts 0)
        dotted-sym    (let [ds (nth parts 1)
                            s (str ds)]
                        ;; Munge dashes to underscores in ns part (before last dot)
                        ;; e.g. my-ns.Foo → my_ns.Foo (matching Java class naming)
                        (symbol (clojure.string/replace s #"^([^.]+)\." (fn [[_ ns-part]] (str (clojure.string/replace ns-part "-" "_") ".")))))
        fields-vec    (nth parts 2)
        ;; Find :implements keyword and its vector
        impl-idx (reduce-kv (fn [_ i v] (if (= :implements v) (reduced i) nil)) nil parts)
        protocols-vec (when impl-idx (nth parts (inc impl-idx) []))
        method-forms  (if impl-idx (drop (+ impl-idx 2) parts) (drop 3 parts))
        is-record?    (:sci.impl/record (meta form))
        ns-sym        (:current-ns machine)
        type-name     (symbol (name qualified-sym))
        clean-fields  (mapv #(with-meta % nil) fields-vec)
        field-keywords (mapv keyword clean-fields)
        ;; Build method-map: mname -> [{:params [...] :body [...] :fields [...]} ...]
        ;; Collect all arities per method name for multi-arity support.
        method-map (reduce (fn [acc mform]
                             (if (seq? mform)
                               (let [mname  (first mform)
                                     params (second mform)
                                     body   (vec (drop 2 mform))]
                                 (update acc mname (fnil conj [])
                                         {:params params :body body :fields clean-fields}))
                               acc))
                           {} method-forms)
        ;; Build closures for all defined methods — used for Object dispatch (toString etc.)
        ;; Normalize keys to unqualified so protocol dispatch works even when method names
        ;; are backtick-qualified (e.g. user/proto from `(defrecord ...)).
        method-fns (reduce-kv (fn [acc mname arities]
                                (let [fns (mapv (fn [{:keys [params body fields]}]
                                                  {:fn (make-deftype-method-fn machine ns-sym fields params body)
                                                   :arity (count params)})
                                                arities)
                                      ;; If single arity, use the fn directly; otherwise dispatch by arity
                                      method-fn (if (= 1 (count fns))
                                                  (:fn (first fns))
                                                  (fn [& args]
                                                    (let [n (count args)
                                                          match (first (filter #(= n (:arity %)) fns))]
                                                      (if match
                                                        (apply (:fn match) args)
                                                        (throw (ex-info (str "No matching arity for method " mname
                                                                             ", got " n " args")
                                                                        {:type :sci/error}))))))]
                                  (assoc acc (symbol (name mname)) method-fn)))
                              {} method-map)
        ;; Create the Type object — store method fns so str/prn can call them
        type-obj (sci.lang/->Type dotted-sym clean-fields {} method-fns {:record? is-record?})
        ;; Create positional constructor ->Name
        ctor-fn (if is-record?
                  (fn [& args]
                    (with-meta (zipmap field-keywords args)
                      {:type type-obj :sci.impl/record true}))
                  (fn [& args]
                    (with-meta (zipmap field-keywords args)
                      {:type type-obj})))
        ctor-sym      (symbol (str "->" type-name))
        ctor-qualified (symbol (str ns-sym) (str ctor-sym))
        ctor-entry    {:val ctor-fn
                       :meta {:name ctor-sym :arglists (list clean-fields)
                              :doc (str "Positional factory function for " dotted-sym ".")}
                       :bound? true}
        machine (-> machine
                    (update-in [:ns ns-sym :types] assoc type-name type-obj)
                    (update :env assoc type-name type-obj)
                    (assoc-in [:heap ctor-qualified] ctor-entry))
        ;; map->Name for records
        machine (if is-record?
                  (let [map-ctor-fn (fn [m]
                                      (with-meta (merge (zipmap field-keywords (repeat nil)) m)
                                        {:type type-obj :sci.impl/record true}))
                        map-ctor-sym (symbol (str "map->" type-name))
                        map-ctor-q   (symbol (str ns-sym) (str map-ctor-sym))
                        map-ctor-entry {:val map-ctor-fn
                                       :meta {:name map-ctor-sym
                                              :arglists (list '[m])
                                              :doc (str "Factory function for " dotted-sym ", taking a map of keywords to field values.")}
                                       :bound? true}]
                    (when-let [a (:heap-atom machine)] (swap! a assoc map-ctor-q map-ctor-entry))
                    (assoc-in machine [:heap map-ctor-q] map-ctor-entry))
                  machine)
        ;; Register protocol implementations
        machine (if (seq protocols-vec)
                  (let [heap (if-let [a (:heap-atom machine)] @a (:heap machine))
                        env  (:env machine)]
                    (reduce (fn [m proto-sym]
                              (let [proto-ns-str (when (qualified-symbol? proto-sym)
                                                   (namespace proto-sym))
                                    proto-name   (name proto-sym)
                                    proto (or (get env proto-sym)
                                              (let [the-ns (or proto-ns-str (str ns-sym))
                                                    q  (symbol the-ns proto-name)
                                                    cq (symbol "clojure.core" proto-name)]
                                                (or (:val (get heap q))
                                                    (:val (get heap cq)))))]
                                (if (and (map? proto) (= :sci/protocol (:type proto)))
                                  (let [proto-methods (:methods proto)
                                        impl-fns (reduce (fn [acc [mname _]]
                                                           (if-let [f (get method-fns mname)]
                                                             (assoc acc mname f)
                                                             acc))
                                                         {} proto-methods)]
                                    ;; Always register, even for marker protocols (empty impl-fns)
                                    (do-extend proto type-obj impl-fns)
                                    m)
                                  m)))
                            machine protocols-vec))
                  machine)]
    (when-let [a (:heap-atom machine)] (swap! a assoc ctor-qualified ctor-entry))
    (when-let [a (:ns-atom machine)]
      (swap! a update-in [ns-sym :types] assoc type-name type-obj))
    (m/push-value machine type-obj)))

(defn step-eval-reify* [machine frame]
  ;; (reify* [Interface1 ...] (method1 [this] body) (method2 [this a] body) ...)
  (let [form (:expr frame)
        parts (vec (rest form))
        interfaces-vec (nth parts 0)
        method-forms (drop 1 parts)
        ns-sym (:current-ns machine)
        ;; Build method-map
        method-map (reduce (fn [acc mform]
                             (if (seq? mform)
                               (let [mname (first mform)
                                     params (second mform)
                                     body (vec (drop 2 mform))]
                                 (update acc mname (fnil conj []) {:params params :body body}))
                               acc))
                           {} method-forms)
        ;; Build closures — normalize to unqualified names
        method-fns (reduce-kv (fn [acc mname arities]
                                (let [fns (mapv (fn [{:keys [params body]}]
                                                  {:fn (make-deftype-method-fn machine ns-sym [] params body)
                                                   :arity (count params)})
                                                arities)
                                      method-fn (if (= 1 (count fns))
                                                  (:fn (first fns))
                                                  (fn [& args]
                                                    (let [n (count args)
                                                          match (first (filter #(= n (:arity %)) fns))]
                                                      (if match
                                                        (apply (:fn match) args)
                                                        (throw (ex-info (str "No matching arity for method " mname
                                                                             ", got " n " args")
                                                                        {:type :sci/error}))))))]
                                  (assoc acc (symbol (name mname)) method-fn)))
                              {} method-map)
        ;; Create anonymous Type object
        type-obj (sci.lang/->Type "reified" [] {} method-fns {})
        ;; Register protocol implementations
        machine (if (seq interfaces-vec)
                  (let [heap (if-let [a (:heap-atom machine)] @a (:heap machine))
                        env (:env machine)]
                    (reduce (fn [m proto-sym]
                              (let [proto-ns-str (when (qualified-symbol? proto-sym)
                                                   (namespace proto-sym))
                                    proto-name (name proto-sym)
                                    proto (or (get env proto-sym)
                                              (let [the-ns (or proto-ns-str (str ns-sym))
                                                    q (symbol the-ns proto-name)
                                                    cq (symbol "clojure.core" proto-name)]
                                                (or (:val (get heap q))
                                                    (:val (get heap cq)))))]
                                (if (and (map? proto) (= :sci/protocol (:type proto)))
                                  (let [proto-methods (:methods proto)
                                        impl-fns (reduce (fn [acc [mname _]]
                                                           (if-let [f (get method-fns mname)]
                                                             (assoc acc mname f)
                                                             acc))
                                                         {} proto-methods)]
                                    (do-extend proto type-obj impl-fns)
                                    m)
                                  m)))
                            machine interfaces-vec))
                  machine)
        ;; Create instance: an empty map with {:type type-obj} metadata
        instance (with-meta {} {:type type-obj})]
    (m/push-value machine instance)))

;; ============================================================
;; Special form dispatch
;; ============================================================

(defn step-eval-special [machine frame]
  (let [raw-head (first (:expr frame))
        head (if (qualified-symbol? raw-head)
               (symbol (name raw-head))
               raw-head)
        ;; Check if the special form symbol has been overridden.
        ;; Check current namespace first, then clojure.core — but only apply
        ;; clojure.core overrides that were explicitly provided by the user
        ;; (marked :user-override? true). Default host heap entries like
        ;; clojure.core/require must NOT shadow SCI's special-form handlers.
        heap (if-let [a (:heap-atom machine)] @a (:heap machine))
        current-ns-override (get heap (symbol (str (:current-ns machine)) (str head)))
        core-override (get heap (symbol "clojure.core" (str head)))
        override-entry (or current-ns-override
                           (when (:user-override? core-override) core-override))]
    (if (and override-entry (not (:macro? override-entry)))
      ;; Override found — apply override value as a function (skip special form handling)
      (let [override-val (:val override-entry)
            arg-exprs (vec (rest (:expr frame)))]
        (-> machine
            (m/replace-frame {:op :eval-args
                              :pending arg-exprs
                              :done []
                              :phase :eval-f
                              :callstack-depth (count (:callstack machine))})
            (assoc :result override-val)))
      ;; No override — proceed with special form dispatch
      (do
        ;; Only check permissions for user-written forms (with :line metadata).
        ;; Macro-expanded special forms (e.g. loop*/recur from doseq) should not
        ;; be blocked by deny lists since the user didn't write them directly.
        (when (:line (meta (:expr frame)))
          (check-permission machine head))
        (case head
          if       (step-eval-if machine frame)
          do       (step-eval-do machine frame)
          let*     (step-eval-let machine frame)
          fn*      (step-eval-fn machine frame)
          def      (step-eval-def machine frame)
          quote    (step-eval-quote machine frame)
          loop*    (step-eval-loop machine frame)
          recur    (step-eval-recur machine frame)
          try      (step-eval-try machine frame)
          throw    (let [throw-loc (form-location (:expr frame))]
                     (-> machine
                         (m/replace-frame (merge {:op :throw} (when throw-loc {:throw-loc throw-loc})))
                         (m/push-frame {:op :eval :expr (second (:expr frame))})))
          var      (step-eval-var machine frame)
          case*    (step-eval-case machine frame)
          set!     (step-eval-set! machine frame)
          new      (step-eval-new machine frame)
          .        (step-eval-dot machine frame)
          import*  (step-eval-import machine frame)
          letfn*   (step-eval-letfn machine frame)
          ns       (step-eval-ns machine frame)
          in-ns    (step-eval-in-ns machine frame)
          require  (step-eval-require machine frame)
          defmacro (step-eval-defmacro machine frame)
          defmulti (step-eval-defmulti machine frame)
          defmethod (step-eval-defmethod machine frame)
          remove-method (step-eval-remove-method machine frame)
          prefer-method (step-eval-prefer-method machine frame)
          defprotocol (step-eval-defprotocol machine frame)
          extend   (step-eval-extend machine frame)
          extend-type (step-eval-extend-type machine frame)
          extend-protocol (step-eval-extend-protocol machine frame)
          binding  (step-eval-binding machine frame)
          deftype* (step-eval-deftype* machine frame)
          reify*   (step-eval-reify* machine frame)
          monitor-enter (m/push-value machine nil)
          monitor-exit  (m/push-value machine nil)
          suspend! (step-eval-suspend machine frame)
          (throw (ex-info (str "Special form not yet implemented: " head)
                          {:type :sci/error :form head})))))))

;; ============================================================
;; Macro expansion
;; ============================================================

(defn try-resolve-macro
  "If the head of a list form is a symbol that resolves to a macro,
   return [val host-macro?] where host-macro? means it takes &form &env as first two args.
   Returns nil if not a macro."
  [machine sym]
  (when (symbol? sym)
    (let [sym-ns (clojure.core/namespace sym)
          sym-name (name sym)
          heap (:heap machine)
          ;; Resolve namespace aliases
          resolved-ns (when sym-ns
                        (let [ns-table (:ns machine)
                              current-ns (:current-ns machine)
                              current-ns-data (get ns-table current-ns)
                              alias-sym (symbol sym-ns)]
                          (or (get (:aliases current-ns-data) alias-sym)
                              (get (:ns-aliases machine) alias-sym)
                              (symbol sym-ns))))
          candidates (if sym-ns
                       [(symbol (str resolved-ns) sym-name)]
                       [(symbol (str (:current-ns machine)) sym-name)
                        (symbol "clojure.core" sym-name)])]
      (some (fn [qualified]
              (when-let [entry (get heap qualified)]
                (when (:macro? entry)
                  (let [v (:val entry)]
                    ;; host-macro? = true when the value is a Clojure var (core macros)
                    ;; or when explicitly tagged :host-macro? (copy-var of defmacro/^:sci/macro)
                    [v (boolean (or (var? v) (:host-macro? entry)))]))))
            candidates))))

(defn macroexpand-form
  "If form is a list whose head resolves to a host macro, expand it.
   Returns [expanded? new-form]."
  [machine form]
  (if-not (seq? form)
    [false form]
    (let [head (first form)
          ;; Don't macro-expand forms whose head is a special form
          ;; (e.g. clojure.core/fn is a macro but fn* is the special form we want)
          bare (when (symbol? head) (symbol (name head)))]
      (if (and bare (contains? special-forms bare))
        ;; Rewrite qualified special form to unqualified, preserving metadata
        (if (= head bare)
          [false form]
          (let [rewritten (cons bare (rest form))]
            [true (if (meta form) (with-meta rewritten (meta form)) rewritten)]))

        (if (and (symbol? head) (contains? (:env machine) head))
          ;; Head is a local binding — don't macro-expand
          [false form]
          (if-let [[macro-val is-host-macro?] (try-resolve-macro machine head)]
            (let [macro-fn (if (var? macro-val) @macro-val macro-val)
                ;; All macros get &form and &env:
                ;; - host Clojure vars: the fn itself takes [&form &env ...args]
                ;; - SCI closures (defmacro in scripts): closure params have &form &env prepended
                ;; - internal SCI macros (doc, defonce, etc.): take just args (no &form &env)
                  current-env (:env machine)
                  expanded (if is-host-macro?
                             (apply macro-fn form current-env (rest form))
                           ;; SCI closures from defmacro: also get &form and &env
                             (if (:sci/closure (meta macro-val))
                               (apply macro-fn form current-env (rest form))
                             ;; Internal SCI macros: just args
                               (apply macro-fn (rest form))))
                ;; Preserve source location from original form on expanded form
                  expanded (if (and (seq? expanded) (:line (meta form)))
                             (with-meta expanded
                               (merge (meta expanded) (select-keys (meta form) [:line :column])))
                             expanded)]
              [true expanded])
            [false form]))))))

;; ============================================================
;; Macro expansion at definition time (Clojure semantics)
;; ============================================================

(defn- macroexpand-all
  "Fully expand all macros in a form at definition time (Clojure compile-time semantics).
   locals is an ordered map {sym nil} used both for local-shadowing checks and as &env."
  [machine form locals]
  (cond
    (not (seq? form)) form

    ;; Quoted forms: don't expand inside
    (= 'quote (first form)) form

    ;; fn*/letfn*/deftype*/reify*: new scope — each inner fn will expand itself when created
    (= 'fn* (first form)) form
    (= 'letfn* (first form)) form
    (= 'deftype* (first form)) form
    (= 'reify* (first form)) form

    ;; let*/loop*: expand binding values, then body with extended locals
    (or (= 'let* (first form)) (= 'loop* (first form)))
    (let [[head bindings & body] form
          pairs (partition 2 bindings)
          [exp-pairs new-locals]
          (reduce (fn [[acc locs] [sym val]]
                    [(conj acc sym (macroexpand-all machine val locs))
                     (assoc locs sym nil)])
                  [[] locals] pairs)
          exp-body (map #(macroexpand-all machine % new-locals) body)
          rebuilt (apply list head (vec exp-pairs) exp-body)]
      (if (meta form) (with-meta rebuilt (meta form)) rebuilt))

    :else
    ;; Try to expand the head as a macro (fixed point)
    (let [expanded
          (loop [f form]
            (let [head (first f)]
              (if (and (symbol? head) (not (contains? locals head)))
                (let [[did-expand? new-f] (macroexpand-form (assoc machine :env locals) f)]
                  (if did-expand? (recur new-f) f))
                f)))]
      (if (identical? expanded form)
        ;; Not a macro call — recurse into sub-forms, preserving source location metadata
        (let [rebuilt (apply list (map #(macroexpand-all machine % locals) form))]
          (if (meta form)
            (with-meta rebuilt (meta form))
            rebuilt))
        ;; Was expanded — re-process result
        (macroexpand-all machine expanded locals)))))

;; ============================================================
;; Static analysis helpers (fn body checking at definition time)
;; ============================================================

(defn- extract-param-hints
  "Extract {sym type-hint-symbol-or-nil} from a destructuring parameter list or single param.
   The type hint is taken from (:tag (meta sym)) when the symbol has a type annotation."
  [params]
  (reduce (fn [hints p]
            (cond
              (= '& p) hints
              (symbol? p) (assoc hints p (some-> (meta p) :tag))
              (vector? p)
              (into hints (extract-param-hints (remove #{'& :as} p)))
              (map? p)
              (let [k (concat (:keys p) (:strs p) (:syms p))
                    as (:as p)]
                (cond-> (into hints (map (fn [s] [s (some-> (meta s) :tag)]) (filter symbol? k)))
                  (symbol? as) (assoc as nil)))
              :else hints))
          {}
          params))

(defn- analyze-form
  "Walk a form at fn-definition time to catch obvious static errors:
   undefined free variables, macro-value references, and denied symbols.
   env: map of {sym type-hint-symbol-or-nil} for locally-in-scope symbols.
   Throws with :phase \"analysis\" if a problem is found."
  [machine env form]
  (letfn [(lookup [sym]
            ;; Returns heap entry or nil
            (let [heap (if-let [a (:heap-atom machine)] @a (:heap machine))
                  ns-sym (:current-ns machine)
                  sym-name (name sym)
                  sym-ns (namespace sym)
                  q-local (symbol (str ns-sym) sym-name)
                  q-core (symbol "clojure.core" sym-name)
                  q-qual (when sym-ns (symbol sym-ns sym-name))]
              (or (when q-qual (get heap q-qual))
                  (get heap q-local)
                  (get heap q-core))))
          (check [env frm]
            (cond
              ;; Nil / literals: ignore
              (nil? frm) nil
              (or (boolean? frm) (number? frm) (string? frm)
                  (keyword? frm) (char? frm)) nil

              ;; Symbol reference
              (symbol? frm)
              (when-not (contains? env frm)
                (let [entry (lookup frm)]
                  (cond
                    (nil? entry)
                    ;; Not in heap — check if it's a Java class
                    #?(:clj
                       (when-not (try-resolve-class (name frm))
                         (throw (ex-info (str "Unable to resolve symbol: " frm " in this context")
                                         {:type :sci/error :sym frm :phase "analysis"})))
                       :cljs
                       (throw (ex-info (str "Unable to resolve symbol: " frm " in this context")
                                       {:type :sci/error :sym frm :phase "analysis"})))
                    ;; In heap but is a macro — can't take value
                    (:macro? entry)
                    (throw (ex-info (str "Can't take value of a macro: " frm)
                                    {:type :sci/error :phase "analysis"})))))

              ;; Seq forms
              (seq? frm)
              (let [head (first frm)]
                (cond
                  ;; Quoted: don't analyze
                  (= 'quote head) nil

                  ;; var special form: check accessibility of the var name
                  (= 'var head)
                  (let [sym (second frm)
                        perms (:permissions machine)
                        deny (:deny perms)]
                    ;; Deny-list check
                    (when (and deny (seq deny))
                      (let [sym-name (name sym)
                            bare (symbol sym-name)
                            core-q (symbol "clojure.core" sym-name)]
                        (when (or (contains? (set deny) sym)
                                  (contains? (set deny) bare)
                                  (contains? (set deny) core-q))
                          (throw (ex-info (str sym " is not allowed!")
                                          {:type :sci/error})))))
                    ;; Existence check (unless it's a local)
                    (when-not (contains? env sym)
                      (when-not (lookup sym)
                        (throw (ex-info (str "Unable to resolve var: " sym " in this context")
                                        {:type :sci/error :sym sym :phase "analysis"})))))

                  ;; fn* — new scope with params
                  (= 'fn* head)
                  (let [fn-parsed (parse-fn-form frm)
                        fn-name (:name fn-parsed)
                        base (cond-> env fn-name (assoc fn-name nil))]
                    (doseq [{:keys [params body]} (:arities fn-parsed)
                            :let [new-env (into base (extract-param-hints params))]]
                      (doseq [bf body] (check new-env bf))))

                  ;; let* — sequential bindings
                  (= 'let* head)
                  (let [raw-bindings (vec (second frm))
                        pairs (partition 2 raw-bindings)
                        body (drop 2 frm)]
                    (loop [rem pairs cur-env env]
                      (if (empty? rem)
                        (doseq [bf body] (check cur-env bf))
                        (let [[sym init] (first rem)]
                          (check cur-env init)
                          (recur (rest rem)
                                 (into cur-env (extract-param-hints [sym])))))))

                  ;; loop* — like let* for init vals, then body with all bindings
                  (= 'loop* head)
                  (let [pairs (partition 2 (second frm))
                        body (drop 2 frm)
                        loop-env (into env (extract-param-hints (map first pairs)))]
                    (doseq [[_ init] pairs] (check env init))
                    (doseq [bf body] (check loop-env bf)))

                  ;; letfn* — all fns are mutually visible; skip detailed analysis
                  (= 'letfn* head) nil

                  ;; try / catch / finally
                  (= 'catch head)
                  (let [ex-sym (nth frm 2 nil)
                        body (drop 3 frm)
                        new-env (if (symbol? ex-sym) (assoc env ex-sym nil) env)]
                    (doseq [bf body] (check new-env bf)))

                  ;; (. target method-or-list args...) — canonical dot special form
                  ;; The target is a symbol/class; method is NOT a free variable
                  (= '. head)
                  (let [[_ target method-or-list & margs] frm]
                    (check env target)
                    (if (list? method-or-list)
                      ;; (. obj (method args...)) — args are inside the list
                      (doseq [a (rest method-or-list)] (check env a))
                      ;; (. obj method args...) — method is a symbol (skip it), args follow
                      (doseq [a margs] (check env a))))

                  ;; (.method obj args...) — instance dot call: check type hint
                  #?(:clj
                     (and (symbol? head)
                          (.startsWith ^String (name head) ".")
                          (not (.startsWith ^String (name head) ".-")))
                     :cljs false)
                  #?(:clj
                     (let [method-str (subs (name head) 1)
                           obj-expr (second frm)]
                       ;; Check all args
                       (doseq [arg (rest frm)] (check env arg))
                       ;; Type-hint check: if obj is a local with a known class hint, verify method
                       (when (symbol? obj-expr)
                         (when-let [tag (get env obj-expr)]
                           (when-let [klass (and (symbol? tag) (try-resolve-class (name tag)))]
                             (when-not (seq (filter #(= method-str (.getName ^java.lang.reflect.Method %))
                                                    (.getMethods ^Class klass)))
                               (throw (ex-info method-str
                                               {:type :sci/error :message method-str
                                                :phase "analysis"})))))))
                     :cljs nil)

                  ;; Default: try macro expansion; if expanded, re-check; else check sub-forms
                  :else
                  (let [[expanded? new-form] (try
                                               (macroexpand-form machine frm)
                                               (catch #?(:clj Throwable :cljs :default) _ [false frm]))]
                    (if expanded?
                      (check env new-form)
                      ;; Regular call — skip head (it may be a macro or special form symbol),
                      ;; check arg sub-forms
                      (doseq [sub (rest frm)] (check env sub))))))

              ;; Collections
              (vector? frm) (doseq [sub frm] (check env sub))
              (map? frm) (doseq [[k v] frm] (check env k) (check env v))
              (set? frm) (doseq [sub frm] (check env sub))

              :else nil))]
    (check env form)))

;; ============================================================
;; Permission checking
;; ============================================================

(def ^:private always-allowed-for-allow-list
  "Structural forms that are implicitly allowed when an allow-list is set.
   These are internal forms needed for basic execution (but NOT user-facing
   forms like def, defmacro, ns, require)."
  '#{do if let* fn* quote var loop* recur try catch finally throw
     new . set! case* binding monitor-enter monitor-exit suspend!})

(defn check-permission [machine sym]
  (let [perms (:permissions machine)
        allow (:allow perms)
        deny (:deny perms)]
    (when (and allow (seq allow))
      (let [sym-name (name sym)
            bare-sym (symbol sym-name)]
        ;; Skip allow-list check for structural forms that are always needed
        (when-not (contains? always-allowed-for-allow-list bare-sym)
          (let [sym-ns (clojure.core/namespace sym)
                qualified (when sym-ns (symbol sym-ns sym-name))
                core-qualified (symbol "clojure.core" sym-name)
                allowed? (or (contains? (set allow) sym)
                             (contains? (set allow) core-qualified)
                             (when qualified (contains? (set allow) qualified)))]
            (when-not allowed?
              (throw (ex-info (str sym " is not allowed!")
                              {:type :sci/error})))))))
    (when (and deny (seq deny))
      (let [sym-name (name sym)
            core-qualified (symbol "clojure.core" sym-name)]
        (when (or (contains? (set deny) sym)
                  (contains? (set deny) core-qualified))
          (throw (ex-info (str sym " is not allowed!")
                          {:type :sci/error})))))))

;; ============================================================
;; Main eval dispatch
;; ============================================================

(defn- form-location
  "Extract :line/:column from form metadata, or nil."
  [form]
  (when-let [m (meta form)]
    (when (:line m)
      {:line (:line m) :column (:column m)})))

(defn step-eval [machine frame]
  (let [form (:expr frame)
        ;; Track source locations for error reporting
        ;; :last-loc = most recent form with location (innermost)
        ;; :top-loc = outermost form with location (for error reporting)
        loc (and (seq? form) (form-location form))
        _ (when loc (set! *current-form-loc* loc))
        machine (if loc
                  (-> machine
                      (assoc :last-loc loc)
                      (cond-> (nil? (:top-loc machine)) (assoc :top-loc loc)))
                  machine)]
    (case (classify-form form)
      :literal (step-eval-literal machine frame)
      :symbol  (step-eval-symbol machine frame)
      :vector  (step-eval-vector machine frame)
      :map     (step-eval-map machine frame)
      :set     (step-eval-set machine frame)
      :special (step-eval-special machine frame)
      :dot-call
      ;; (.method obj args...) or (.-field obj) → (. obj method args...) or (. obj -field)
      (let [head (first form)
            raw-name (subs (name head) 1)]
        (when (or (empty? raw-name) (nil? (second form)))
          (throw (#?(:clj IllegalArgumentException. :cljs js/Error.)
                  (str "Malformed member expression, expecting (.member target ...)"))))
        (let [is-field? #?(:clj (.startsWith ^String raw-name "-")
                           :cljs (= "-" (subs raw-name 0 1)))
              member-name (if is-field?
                            (symbol (str "-" (subs raw-name 1)))
                            (symbol raw-name))
              obj-expr (second form)
              args (drop 2 form)
              dot-form (list* '. obj-expr member-name args)]
          (m/replace-frame machine {:op :eval :expr dot-form})))

      :new-call
      ;; (ClassName. args...) → (new ClassName args...)
      (let [head (first form)
            class-name (let [n (name head)] (subs n 0 (dec (count n))))
            new-form (list* 'new (symbol class-name) (rest form))]
        (m/replace-frame machine {:op :eval :expr new-form}))

      :invoke
      ;; Check both deny and allow lists for invoke forms
      (do (when (symbol? (first form))
            (let [perms (:permissions machine)]
              ;; Deny check
              (let [deny (:deny perms)]
                (when (and deny (seq deny))
                  (let [sym (first form)
                        sym-name (name sym)
                        core-qualified (symbol "clojure.core" sym-name)]
                    (when (or (contains? (set deny) sym)
                              (contains? (set deny) core-qualified))
                      (throw (ex-info (str sym " is not allowed!")
                                      {:type :sci/error}))))))
              ;; Allow check — only for user-written forms
              (let [allow (:allow perms)]
                (when (and allow (seq allow) (:line (meta form)))
                  (let [sym (first form)
                        sym-name (name sym)
                        bare-sym (symbol sym-name)]
                    (when-not (or (contains? always-allowed-for-allow-list bare-sym)
                                  (contains? (set allow) sym)
                                  (contains? (set allow) bare-sym)
                                  (contains? (set allow) (symbol "clojure.core" sym-name)))
                      (throw (ex-info (str sym " is not allowed!")
                                      {:type :sci/error}))))))))
          (let [[expanded? new-form] (macroexpand-form machine form)]
            (if expanded?
              (m/replace-frame machine {:op :eval :expr new-form})
              ;; Check for (Integer/SIZE) — static field access with parens but no args
              #?(:clj
                 (let [head (first form)]
                   (if (and (symbol? head)
                            (namespace head)
                            (empty? (rest form))
                            (try-resolve-class (namespace head)))
                     ;; Looks like (ClassName/field) — just evaluate head
                     (m/replace-frame machine {:op :eval :expr head})
                     (step-eval-invoke machine frame)))
                 :cljs
                 (step-eval-invoke machine frame))))))))

;; ============================================================
;; Main step function
;; ============================================================

(defn step [machine]
  (let [frame (m/peek-frame machine)]
    (if (nil? frame)
      (assoc machine :status :done)
      (case (:op frame)
        :eval            (step-eval machine frame)
        :apply           (step-apply machine frame)
        :eval-args       (step-eval-args machine frame)
        :eval-coll       (step-eval-coll machine frame)
        :apply-meta      (step-apply-meta machine frame)
        :if              (step-if machine frame)
        :do              (step-do machine frame)
        :let             (step-let machine frame)
        :do-restore-env  (step-do-restore-env machine frame)
        :def             (step-def machine frame)
        :def-with-meta   (step-def-with-meta machine frame)
        :fn-body         (if (= :return (:phase frame))
                           (step-fn-body-return machine frame)
                           (step-fn-body machine frame))
        :loop-init       (step-loop-init machine frame)
        :recur           (step-recur machine frame)
        :eval-recur-args (step-eval-recur-args machine frame)
        :try             (step-try machine frame)
        :case*           (step-case* machine frame)
        :in-ns-apply     (step-in-ns-apply machine frame)
        :defmulti-apply  (step-defmulti-apply machine frame)
        :binding-init    (step-binding-init machine frame)
        :binding-body    (step-binding-body machine frame)
        :set!-apply      (step-set!-apply machine frame)
        :suspend-apply   (step-suspend-apply machine frame)
        :throw           (let [v (:result machine)]
                           (if (instance? #?(:clj Throwable :cljs js/Error) v)
                             ;; Rethrow as-is (preserve user's ex-info data)
                             (throw v)
                             (let [loc (or (:top-loc machine) (last (:callstack machine)) (:last-loc machine))]
                               (throw (ex-info (str v)
                                               (merge {:type :sci/error
                                                       :sci.impl/callstack (:callstack machine)}
                                                      (when loc
                                                        {:line (:line loc)
                                                         :column (:column loc)
                                                         :file (:file loc)})))))))
        (throw (ex-info (str "Unknown op: " (:op frame))
                        {:type :sci/error}))))))

;; ============================================================
;; Run loop
;; ============================================================

(defn- find-try-frame
  "Walk the stack looking for a :try frame. Returns [stack-index frame] or nil."
  [stack]
  (loop [i (dec (count stack))]
    (when (>= i 0)
      (let [frame (nth stack i)]
        (if (= :try (:op frame))
          [i frame]
          (recur (dec i)))))))

(defn- handle-exception
  "Handle an exception by looking for a matching catch clause on the stack."
  [machine ^Throwable ex]
  ;; Unwrap ExecutionException (Clojure 1.10.x future.get wraps exceptions in ExecutionException)
  (let [ex #?(:clj (if (instance? java.util.concurrent.ExecutionException ex)
                     (or (.getCause ^java.util.concurrent.ExecutionException ex) ex)
                     ex)
              :cljs ex)])
  (if-let [[idx try-frame] (find-try-frame (:stack machine))]
    ;; Found a try frame — look for matching catch
    (let [catches (:catches try-frame)
          match (first
                 (filter (fn [catch-form]
                           (let [[_ class-sym _binding & _body] catch-form]
                             ;; Resolve the class
                             #?(:clj
                                (when-let [klass (try-resolve-class (str class-sym))]
                                  ;; Check both the exception and its cause (for wrapped exceptions)
                                  (or (instance? klass ex)
                                      (when-let [cause (ex-cause ex)]
                                        (instance? klass cause))))
                                :cljs true)))
                         catches))]
      (if match
        (let [[_ catch-class-sym binding-sym & body] match
              ;; Truncate stack to the try frame
              new-stack (subvec (vec (:stack machine)) 0 idx)
              ;; ^:sci/error on catch class: bind the SCI-wrapped exception using last-loc
              sci-error? #?(:clj (and (symbol? catch-class-sym)
                                      (:sci/error (meta catch-class-sym)))
                            :cljs false)
              bound-ex (if sci-error?
                         ;; Wrap exception as SCI error using last-loc for accurate location
                         (let [loc (or (:last-loc machine) (:top-loc machine)
                                       (first (:callstack machine)))]
                           (ex-info (or (ex-message ex)
                                        #?(:clj (.getName (class ex)) :cljs "Error"))
                                    (merge {:type :sci/error
                                            :message (ex-message ex)
                                            :sci.impl/callstack (:callstack machine)}
                                           (when loc {:line (:line loc) :column (:column loc)
                                                      :file (:file loc)}))
                                    ex))
                         ;; Normal: bind original exception (or cause if class didn't match directly)
                         #?(:clj (let [klass (or (try-resolve-class (str catch-class-sym)) Exception)]
                                   (if (instance? klass ex)
                                     ex
                                     (or (ex-cause ex) ex)))
                            :cljs ex))
              m (-> machine
                    (assoc :stack new-stack
                           :status :running)
                    (update :env assoc binding-sym bound-ex))]
          ;; Evaluate catch body
          (if (seq body)
            (let [catch-body-frame {:op :try
                                    :catches []
                                    :finally (:finally try-frame)
                                    :body (vec body)
                                    :phase :catch-body}]
              (-> m
                  (update :stack conj catch-body-frame)
                  (m/push-frame {:op :eval :expr (first body)})))
            (if (:finally try-frame)
              (-> m
                  (update :stack conj {:op :try
                                       :phase :finally
                                       :body-result nil
                                       :finally (:finally try-frame)})
                  (m/push-frame {:op :eval :expr (cons 'do (rest (:finally try-frame)))}))
              (m/set-result m nil))))
        ;; No matching catch — pop try frame and continue unwinding
        (let [new-stack (subvec (vec (:stack machine)) 0 idx)
              machine-without-try (assoc machine :stack new-stack)]
          (if (:finally try-frame)
            ;; TODO: run finally then rethrow
            (handle-exception machine-without-try ex)
            (handle-exception machine-without-try ex)))))
    ;; No try frame — wrap with location info and rethrow
    (let [;; Prefer throw-loc (saved from :throw special form) for accurate error location
          top-frame (peek (vec (:stack machine)))
          throw-loc (when (= :throw (:op top-frame)) (:throw-loc top-frame))
          already-wrapped? (and (instance? #?(:clj clojure.lang.ExceptionInfo :cljs cljs.core/ExceptionInfo) ex)
                                (= :sci/error (:type (ex-data ex))))
          ;; For SCI errors: use *current-form-loc* for the most specific sub-form location.
          ;; For host Java exceptions: if there is an :eval-args frame in the stack the error
          ;; occurred while evaluating a function argument, so use *current-form-loc* for the
          ;; argument's location; otherwise (body/implicit-do context) use :top-loc so the error
          ;; is attributed to the outermost enclosing form rather than a macro-expansion sub-form.
          loc (if already-wrapped?
                (or throw-loc *current-form-loc* (:last-loc machine) (:top-loc machine) (first (:callstack machine)))
                (let [has-eval-args? (some #(= :eval-args (:op %)) (:stack machine))]
                  (if has-eval-args?
                    (or throw-loc *current-form-loc* (:last-loc machine) (:top-loc machine) (first (:callstack machine)))
                    (or throw-loc (:top-loc machine) *current-form-loc* (:last-loc machine) (first (:callstack machine))))))]
      (if (and already-wrapped? (:line (ex-data ex)))
        ;; Already has location info — rethrow unchanged
        (throw ex)
        ;; Wrap or re-wrap with location info
        (let [original-raw-callstack (:callstack machine)
              raw-callstack original-raw-callstack
              ;; Synthesize callstack from loc when empty (e.g. analysis-phase errors)
              raw-callstack (if (and (empty? raw-callstack) loc)
                              [{:ns (:current-ns machine)
                                :name (:current-fn-name machine)
                                :line (:line loc)
                                :column (:column loc)
                                :file (:current-file machine)}]
                              raw-callstack)
              ;; Reverse: callstack is stored outermost-first; tests expect innermost-first
              callstack (vec (rseq (vec raw-callstack)))
              ;; For SCI internal errors (no :line in ex-data), prepend a no-loc frame for
              ;; the current function — indicates where the error occurred
              callstack (if (and (not-empty callstack)
                                 already-wrapped?
                                 (not (:line (ex-data ex)))
                                 (:current-fn-name machine))
                          (into [{:ns (:current-ns machine)
                                  :name (:current-fn-name machine)
                                  :file (:current-file machine)}]
                                callstack)
                          callstack)
              ;; Prepend built-in host function frame when the top stack frame is :apply
              ;; with a known host fn (looked up via inverse-registry)
              builtin-frame #?(:clj
                               (when-let [ir (:inverse-registry machine)]
                                 (let [tf (peek (vec (:stack machine)))]
                                   (when (and (= :apply (:op tf)) (fn? (:f tf)))
                                     (when-let [sym (.get ^java.util.IdentityHashMap ir (:f tf))]
                                       (let [entry (get @(:heap-atom machine) sym)
                                             m (or (:meta entry) {})]
                                         {:ns (symbol (str (or (:ns m) (namespace sym))))
                                          :name (or (:name m) (symbol (name sym)))
                                          :file (:file m)
                                          :line (:line m)
                                          :column (or (:column m) 1)})))))
                               :cljs nil)
              callstack (if builtin-frame
                          (into [builtin-frame] callstack)
                          callstack)
              ;; If the outermost callstack entry is deeper than :top-loc, it means the top-level
              ;; form was a macro call that didn't push a callstack entry. Add a synthetic frame
              ;; for the top-level form so the full call chain is visible.
              callstack (if (and (not-empty original-raw-callstack)
                                 (not-empty callstack)
                                 (:top-loc machine))
                          (let [top-loc (:top-loc machine)
                                last-e (peek callstack)]
                            (if (and (= (:line top-loc) (:line last-e))
                                     (= (:column top-loc) (:column last-e)))
                              callstack
                              (conj callstack {:ns (:current-ns machine)
                                               :name nil
                                               :line (:line top-loc)
                                               :column (:column top-loc)
                                               :file (:current-file machine)})))
                          callstack)]
          (throw (ex-info (or (ex-message ex) (str #?(:clj (.getName (class ex)) :cljs "Error")))
                          (merge (when already-wrapped? (ex-data ex))
                                 {:type :sci/error
                                  :message (ex-message ex)
                                  :sci.impl/callstack callstack}
                                 (when loc
                                   {:line (:line loc)
                                    :column (:column loc)})
                                 {:file (or (:file loc) (:current-file machine))})
                          (if already-wrapped? (ex-cause ex) ex))))))))

(def ^:dynamic *max-steps*
  "Maximum number of VM steps before throwing. nil = unlimited.
   Bind this to prevent infinite loops from hanging."
  nil)

(defn run [machine]
  (let [max-steps *max-steps*]
    (binding [current-dynamic-bindings nil
              *current-form-loc* nil]
      (loop [m machine
             steps 0]
        (case (:status m)
          :running (do
                     (when (and max-steps (>= steps max-steps))
                       (throw (ex-info "Execution limit reached"
                                       {:type :sci/error :steps steps})))
                     (let [pre-dyn (:dynamic-bindings m)
                           _ (set! current-dynamic-bindings pre-dyn)
                           next-m (try
                                    (step m)
                                    (catch #?(:clj Throwable :cljs :default) ex
                                      (handle-exception m ex)))
                           ;; Sync back var-set changes: only if a host fn modified
                           ;; current-dynamic-bindings (not if step itself changed it)
                           post-dyn current-dynamic-bindings
                           next-m (if (identical? post-dyn pre-dyn)
                                    next-m ;; No host-side changes
                                    ;; Host fn modified bindings — merge into step result
                                    (assoc next-m :dynamic-bindings post-dyn))]
                       (recur next-m (unchecked-inc steps))))
          :done    (:result m)
          :suspend m
          :effect  m)))))
