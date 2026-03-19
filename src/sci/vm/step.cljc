(ns sci.vm.step
  "The step function — heart of the VM. Each step processes one frame."
  (:require [sci.vm.machine :as m]
            [sci.lang]
            [clojure.string]))

(declare match-arity bind-params run check-permission form-location do-extend)

;; Shared dynamic bindings for closures called from host code (e.g. via map)
(def ^:private current-dynamic-bindings (atom nil))

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
  '#{if do let* fn* def quote var loop* recur try catch
     finally throw set! new . defmacro case* import*
     ns in-ns require letfn* binding
     defmulti defmethod remove-method prefer-method
     defprotocol extend extend-type extend-protocol
     reify monitor-enter monitor-exit})

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
        ;; ClassName. constructor call
        (and (symbol? head)
             (let [n (name head)]
               #?(:clj (.endsWith ^String n ".")
                  :cljs (= "." (subs n (dec (count n))))))) :new-call
        :else :invoke))
    :else :literal))

;; ============================================================
;; Symbol resolution
;; ============================================================

#?(:clj
   (defn- try-resolve-class
     "Try to resolve a class name string. Returns the Class or nil."
     [class-name]
     (try
       (Class/forName class-name)
       (catch ClassNotFoundException _
         (try
           (Class/forName (str "java.lang." class-name))
           (catch ClassNotFoundException _ nil))))))

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
           ;; Try as static method — return a wrapper function
           (fn [& args]
             (clojure.lang.Reflector/invokeStaticMethod
              klass member-name (to-array args))))))))

(defn resolve-symbol [machine sym]
  (let [env (:env machine)]
    (if (contains? env sym)
      (get env sym)
      (let [sym-ns (namespace sym)
            sym-name (name sym)
            heap (:heap machine)]
        (if sym-ns
          ;; Qualified symbol
          (let [ns-table (:ns machine)
                current-ns (:current-ns machine)
                current-ns-data (get ns-table current-ns)
                resolved-ns (or (get (:aliases current-ns-data) (symbol sym-ns))
                                (symbol sym-ns))
                qualified (symbol (str resolved-ns) sym-name)]
            (if (contains? heap qualified)
              (:val (get heap qualified))
              ;; Try as Java static field/method
              #?(:clj
                 (if-let [klass (try-resolve-class sym-ns)]
                   (resolve-static-member klass sym-name)
                   (throw (ex-info (str "Could not resolve symbol: " sym)
                                  {:type :sci/error :sym sym})))
                 :cljs
                 (throw (ex-info (str "Could not resolve symbol: " sym)
                                 {:type :sci/error :sym sym})))))
          ;; Unqualified
          (let [ns-sym (:current-ns machine)
                qualified (symbol (str ns-sym) sym-name)
                core-q (symbol "clojure.core" sym-name)
                dyn (:dynamic-bindings machine)]
            (or (when (and dyn (contains? dyn qualified)) (get dyn qualified))
                (when (and dyn (contains? dyn core-q)) (get dyn core-q))
                (when (contains? heap qualified) (:val (get heap qualified)))
                (when (contains? heap core-q) (:val (get heap core-q)))
                #?(:clj (try-resolve-class sym-name) :cljs nil)
                (throw (ex-info (str "Could not resolve symbol: " sym)
                                {:type :sci/error :sym sym})))))))))

;; ============================================================
;; Literals, symbols, collections
;; ============================================================

(defn step-eval-literal [machine frame]
  (m/push-value machine (:expr frame)))

(defn step-eval-symbol [machine frame]
  (let [sym (:expr frame)]
    (check-permission machine sym)
    (m/push-value machine (resolve-symbol machine sym))))

(defn step-eval-vector [machine frame]
  (let [exprs (:expr frame)
        form-meta (meta (:expr frame))]
    (if (empty? exprs)
      (m/push-value machine (if form-meta (with-meta [] form-meta) []))
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
      (m/push-value machine (if form-meta (with-meta {} form-meta) {}))
      (-> machine
          (m/replace-frame {:op :eval-coll :coll-type :map
                            :pending (vec (rest flat)) :done []
                            :form-meta form-meta})
          (m/push-frame {:op :eval :expr (first flat)})))))

(defn step-eval-set [machine frame]
  (let [exprs (vec (:expr frame))
        form-meta (meta (:expr frame))]
    (if (empty? exprs)
      (m/push-value machine (if form-meta (with-meta #{} form-meta) #{}))
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
                  :set    (set done)
                  :map    (apply hash-map done))
            val (if-let [fm (:form-meta frame)]
                  (with-meta raw fm)
                  raw)]
        (m/push-value machine val))
      (-> machine
          (m/replace-frame (assoc frame :done done :pending (vec (rest pending))))
          (m/push-frame {:op :eval :expr (first pending)})))))

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
;; fn*
;; ============================================================

(defn parse-fn-form [form]
  (let [args (rest form)
        [fname args] (if (symbol? (first args))
                       [(first args) (rest args)]
                       [nil args])
        arities (if (vector? (first args))
                  [{:params (vec (first args)) :body (vec (rest args))}]
                  (mapv (fn [arity-form]
                          {:params (vec (first arity-form))
                           :body (vec (rest arity-form))})
                        args))]
    {:name fname :arities arities}))

(defn make-callable-closure
  "Create a closure that is both an IFn (so host code like `map` can call it)
   and carries closure metadata for the VM."
  [closure-map machine]
  (let [f (fn callable-closure [& args]
            ;; Create a mini-machine and run the closure
            (let [arity (match-arity (:arities closure-map) (count args) (:name closure-map))
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
                                    :dynamic-bindings @current-dynamic-bindings))]
              ;; Push fn-body frame with recur-target so recur works
              (let [body (:body arity)
                    m (-> mini-m
                          (m/push-frame {:op :fn-body
                                         :body body
                                         :saved-env fn-env
                                         :recur-target true
                                         :params (:params arity)
                                         :loop-body body
                                         :closure closure-map})
                          (m/push-frame {:op :eval :expr (first body)}))]
                (run m))))]
    (with-meta f (assoc closure-map :sci/closure true))))

(defn step-eval-fn [machine frame]
  (let [parsed (parse-fn-form (:expr frame))
        closure-map {:type :closure
                     :name (:name parsed)
                     :arities (:arities parsed)
                     :env (:env machine)}
        callable (make-callable-closure closure-map machine)]
    (m/push-value machine callable)))

;; ============================================================
;; Function application
;; ============================================================

(defn step-eval-invoke [machine frame]
  (let [form (:expr frame)
        f-expr (first form)
        arg-exprs (vec (rest form))
        loc (form-location form)
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
                          :callstack-depth (count (:callstack machine))})
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
                 ;; Static access
                 (if (:field? frame)
                   (m/push-value machine (clojure.lang.Reflector/getStaticField ^Class f method-str))
                   ;; Try static field first, then no-arg static method
                   (m/push-value machine
                     (try
                       (clojure.lang.Reflector/getStaticField ^Class f method-str)
                       (catch Exception _
                         (clojure.lang.Reflector/invokeStaticMethod ^Class f method-str (to-array []))))))
                 ;; Instance access
                 (if (:field? frame)
                   (m/push-value machine (clojure.lang.Reflector/invokeNoArgInstanceMember f method-str false))
                   (m/push-value machine
                     (clojure.lang.Reflector/invokeInstanceMethod f method-str (to-array []))))))
             :cljs
             (throw (ex-info "Interop not supported in CLJS" {})))
          (:new? frame)
          #?(:clj
             (m/push-value machine
               (clojure.lang.Reflector/invokeConstructor
                ^Class f (to-array [])))
             :cljs
             (throw (ex-info "new not supported in CLJS" {})))
          :else
          (m/replace-frame machine {:op :apply :f f :args []}))
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
                 (m/push-value machine
                   (clojure.lang.Reflector/invokeStaticMethod ^Class obj method-str (to-array args)))
                 ;; Instance method call
                 (m/push-value machine
                   (clojure.lang.Reflector/invokeInstanceMethod obj method-str (to-array args))))
               :cljs
               (throw (ex-info "Interop not supported in CLJS" {}))))
          (:new? frame)
          #?(:clj
             (m/push-value machine
               (clojure.lang.Reflector/invokeConstructor
                ^Class (:f frame) (to-array done)))
             :cljs
             (throw (ex-info "new not supported in CLJS" {})))
          (:defmethod? frame)
          ;; f = multimethod, done = [dispatch-val method-fn]
          (let [mm (:f frame)
                [dispatch-val method-fn] done
                methods-atom (:methods (meta mm))]
            (swap! methods-atom assoc dispatch-val method-fn)
            (m/push-value machine mm))
          (:remove-method? frame)
          (let [mm (:f frame)
                [dispatch-val] done
                methods-atom (:methods (meta mm))]
            (swap! methods-atom dissoc dispatch-val)
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
          (m/replace-frame machine {:op :apply :f (:f frame) :args done}))
        (-> machine
            (m/replace-frame (assoc frame :done done
                                          :pending (subvec pending 1)))
            (m/push-frame {:op :eval :expr (nth pending 0)}))))))

(defn match-arity
  ([arities argc] (match-arity arities argc nil))
  ([arities argc fn-name]
   (or
    (first (filter (fn [{:keys [params]}]
                     (let [params-vec (vec params)
                           amp-pos (reduce-kv (fn [_ i v] (if (= '& v) (reduced i) nil))
                                              nil params-vec)]
                       (if amp-pos
                         (>= argc amp-pos)
                         (= argc (count params)))))
                   arities))
    (let [arity-desc (if fn-name
                       (str fn-name)
                       (let [arity-counts (map (fn [{:keys [params]}]
                                                 (let [pv (vec params)
                                                       amp (reduce-kv (fn [_ i v] (if (= '& v) (reduced i) nil)) nil pv)]
                                                   (if amp amp (count params))))
                                               arities)]
                         (str "function of arity " (clojure.string/join ", " arity-counts))))]
      (throw (ex-info (str "Wrong number of args (" argc ") passed to: " arity-desc)
                      {:type :sci/error}))))))

(defn bind-params [params args]
  (let [params-vec (vec params)
        amp-pos (reduce-kv (fn [_ i v] (if (= '& v) (reduced i) nil))
                           nil params-vec)]
    (if (nil? amp-pos)
      (zipmap params args)
      (let [fixed-params (subvec params-vec 0 amp-pos)
            rest-param (nth params-vec (inc amp-pos))
            fixed-args (take amp-pos args)
            rest-args (drop amp-pos args)]
        (-> (zipmap fixed-params fixed-args)
            (assoc rest-param (seq rest-args)))))))

(defn step-apply [machine frame]
  (let [f (:f frame)
        args (:args frame)]
    (cond
      ;; Host function
      (fn? f)
      (m/push-value machine (apply f args))

      ;; Host fn ref (for serialization)
      (and (map? f) (= :host-fn (:type f)))
      (m/push-value machine (apply (:fn f) args))

      ;; Closure
      (and (map? f) (= :closure (:type f)))
      (let [arity (match-arity (:arities f) (count args) (:name f))
            bindings (bind-params (:params arity) args)
            fn-env (merge (:env f)
                          bindings
                          (when-let [fname (:name f)]
                            {fname f}))]
        (-> machine
            (m/replace-frame {:op :fn-body
                              :body (:body arity)
                              :saved-env (:env machine)
                              :saved-fn-name (:current-fn-name machine)
                              :saved-callstack-depth (count (:callstack machine))
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

      ;; Symbol — resolve and retry
      (symbol? f)
      (m/replace-frame machine {:op :apply :f (resolve-symbol machine f) :args args})

      ;; Java class as constructor
      #?@(:clj
          [(instance? Class f)
           (m/push-value machine
             (clojure.lang.Reflector/invokeConstructor
              ^Class f (to-array args)))])

      :else
      (throw (ex-info (str "Cannot call " (pr-str f) " as a function")
                      {:type :sci/error})))))

;; ============================================================
;; fn-body
;; ============================================================

(defn step-fn-body [machine frame]
  (let [body (:body frame)]
    (if (empty? body)
      (-> machine
          (assoc :env (:saved-env frame))
          (m/push-value nil))
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
        ;; Handle (def name docstring init-expr)
        [doc-str init-expr meta-map]
        (cond
          (empty? init)       [nil nil (meta sym)]
          (and (= 2 (count init)) (string? (first init)))
          [(first init) (second init) (merge (meta sym) {:doc (first init)})]
          :else               [nil (first init) (meta sym)])]
    (if (nil? init-expr)
      (let [ns-sym (:current-ns machine)
            qualified (symbol (str ns-sym) (str sym))
            entry {:val nil :meta meta-map}]
        (when-let [a (:heap-atom machine)]
          (swap! a assoc qualified entry))
        (-> machine
            (assoc-in [:heap qualified] entry)
            (m/push-value (symbol (str ns-sym) (str sym)))))
      (-> machine
          (m/replace-frame {:op :def :sym sym
                            :ns-sym (:current-ns machine)
                            :meta-map meta-map})
          (m/push-frame {:op :eval :expr init-expr})))))

(defn step-def [machine frame]
  (let [sym (:sym frame)
        ns-sym (:ns-sym frame)
        qualified (symbol (str ns-sym) (str sym))
        val (:result machine)
        meta-map (:meta-map frame)
        entry {:val val :meta meta-map :dynamic? (:dynamic meta-map)}]
    ;; Update both the immutable heap and the shared atom
    (when-let [a (:heap-atom machine)]
      (swap! a assoc qualified entry))
    (-> machine
        (assoc-in [:heap qualified] entry)
        (m/push-value (symbol (str ns-sym) (str sym))))))

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
        binding-pairs (vec (partition 2 bindings))]
    (m/replace-frame machine {:op :loop-init
                              :bindings binding-pairs
                              :body (vec body)
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
        (throw (ex-info "recur without matching target" {:type :sci/error}))
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
        body (vec (remove #(and (seq? %) (contains? #{'catch 'finally} (first %))) clauses))
        catches (vec (filter #(and (seq? %) (= 'catch (first %))) clauses))
        finally-form (first (filter #(and (seq? %) (= 'finally (first %))) clauses))]
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
        qualified (if (qualified-symbol? sym)
                    sym
                    ;; Also check clojure.core
                    (let [local-q (symbol (str ns-sym) (str sym))]
                      (if (contains? (:heap machine) local-q)
                        local-q
                        (let [core-q (symbol "clojure.core" (str sym))]
                          (if (contains? (:heap machine) core-q)
                            core-q
                            local-q)))))
        entry (get (:heap machine) qualified)
        ;; Create an SCI var-like object
        var-obj (sci.lang/->Var qualified
                               (:val entry)
                               (merge (:meta entry)
                                      {:name (symbol (name qualified))
                                       :ns (symbol (namespace qualified))})
                               (:dynamic? entry))]
    (m/push-value machine var-obj)))

;; ============================================================
;; Dynamic binding + set!
;; ============================================================

(defn- resolve-var-qualified [machine sym]
  (let [sym-name (name sym)
        local-q (symbol (str (:current-ns machine)) sym-name)]
    (if (contains? (:heap machine) local-q)
      local-q
      (symbol "clojure.core" sym-name))))

(defn step-eval-binding [machine frame]
  (let [[_ bindings & body] (:expr frame)
        pairs (vec (partition 2 bindings))]
    (-> machine
        (m/replace-frame {:op :binding-init
                          :pairs pairs
                          :body (vec body)
                          :saved-dynamic-bindings (:dynamic-bindings machine)
                          :bind-idx 0}))))

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
        (let [body (:body frame)]
          (if (empty? body)
            (-> machine
                (assoc :dynamic-bindings (:saved-dynamic-bindings frame))
                (m/push-value nil))
            (-> machine
                (m/replace-frame {:op :binding-body
                                  :body (vec body)
                                  :saved-dynamic-bindings (:saved-dynamic-bindings frame)})
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
      (-> machine
          (assoc :dynamic-bindings (:saved-dynamic-bindings frame))
          (m/pop-frame))
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
      (let [entry (assoc (get (:heap machine) qualified) :val val)]
        (when-let [a (:heap-atom machine)]
          (swap! a assoc qualified entry))
        (-> machine
            (assoc-in [:heap qualified] entry)
            (m/push-value val))))))

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
           [method-name method-args]
           (if (seq? method-or-call)
             [(first method-or-call) (rest method-or-call)]
             [method-or-call args])
           method-str (str method-name)
           is-field? (.startsWith ^String method-str "-")]
       (-> machine
           (m/replace-frame {:op :eval-args
                             :pending (vec method-args)
                             :done []
                             :phase :eval-f
                             :dot? true
                             :method-name (if is-field?
                                            (symbol (subs method-str 1))
                                            method-name)
                             :field? is-field?})
           (m/push-frame {:op :eval :expr obj-expr}))))
   :cljs
   (defn step-eval-dot [machine frame]
     (throw (ex-info ". interop not implemented for ClojureScript" {}))))

;; ============================================================
;; import*
;; ============================================================

(defn step-eval-import [machine frame]
  ;; (import* "fully.qualified.ClassName")
  (let [[_ class-str] (:expr frame)]
    #?(:clj
       (let [klass (try (Class/forName class-str)
                        (catch ClassNotFoundException _
                          (throw (ex-info (str "Unable to resolve classname: " class-str)
                                         {:type :sci/error}))))
             short-name (symbol (.getSimpleName ^Class klass))]
         ;; Register the short name in the current env so it resolves
         (-> machine
             (update :env assoc short-name klass)
             (m/push-value klass)))
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
    ;; Evaluate the multimethod reference and the method fn
    (-> machine
        (m/replace-frame {:op :eval-args
                          :pending [(list 'quote dispatch-val) fn-form]
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
  [proto-name method-sigs ns-sym]
  {:type :sci/protocol
   :name proto-name
   :ns ns-sym
   :methods method-sigs
   :impls (atom {})}) ;; type -> {method-name -> fn}

(defn step-eval-defprotocol [machine frame]
  ;; (defprotocol Name (method1 [this]) (method2 [this x]))
  (let [[_ proto-name & method-defs] (:expr frame)
        ns-sym (:current-ns machine)
        ;; Parse method signatures
        method-sigs (into {} (keep (fn [md]
                                     (when (seq? md)
                                       (let [mname (first md)
                                             arglists (rest md)
                                             ;; Filter out docstrings
                                             arglists (remove string? arglists)]
                                         [mname {:arglists (vec arglists)}])))
                                   method-defs))
        protocol (make-protocol proto-name method-sigs ns-sym)
        qualified (symbol (str ns-sym) (str proto-name))
        ;; Create dispatch functions for each protocol method
        machine (reduce
                 (fn [m [mname {:keys [arglists]}]]
                   (let [method-fn (fn protocol-dispatch [& args]
                                     (let [target (first args)
                                           target-type (type target)
                                           impls @(:impls protocol)
                                           ;; Look up implementation: exact type match first, then supers
                                           impl (or (get impls target-type)
                                                    (some (fn [[t impl]]
                                                            (when (and (class? t) (instance? t target))
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
                                                         {:type :sci/error})))))
                         mq (symbol (str ns-sym) (str mname))
                         entry {:val method-fn :meta {:protocol protocol} :dynamic? false}]
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
        (m/push-value protocol))))

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
        ;; Build a do form: (do (def name1 (fn* ...)) (def name2 (fn* ...)) ... body...)
        defs (mapv (fn [[fname fn-form]] (list 'def fname fn-form)) pairs)
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
        ;; Parse like fn
        parsed (parse-fn-form (list* 'fn* rest-form))
        closure-map {:type :closure
                     :name macro-name
                     :arities (:arities parsed)
                     :env (:env machine)}
        ;; Create a callable that takes &form &env then the real args
        callable (make-callable-closure closure-map machine)
        ns-sym (:current-ns machine)
        qualified (symbol (str ns-sym) (str macro-name))
        entry {:val callable :meta {:macro true} :macro? true}]
    (when-let [a (:heap-atom machine)]
      (swap! a assoc qualified entry))
    (-> machine
        (assoc-in [:heap qualified] entry)
        (m/push-value (symbol (str ns-sym) (str macro-name))))))

;; ============================================================
;; ns / in-ns / require
;; ============================================================

(defn step-eval-in-ns [machine frame]
  (let [[_ ns-sym-expr] (:expr frame)]
    ;; Evaluate the ns symbol
    (-> machine
        (m/replace-frame {:op :in-ns-apply})
        (m/push-frame {:op :eval :expr ns-sym-expr}))))

(defn step-in-ns-apply [machine frame]
  (let [ns-sym (:result machine)]
    (-> machine
        (assoc :current-ns ns-sym)
        (update :ns #(if (get % ns-sym) % (assoc % ns-sym {:aliases {} :refers {} :imports {}})))
        (m/push-value ns-sym))))

(defn- process-require-spec
  "Process a single require spec and update the machine's ns table."
  [machine spec]
  (let [current-ns (:current-ns machine)]
    (cond
      ;; Simple symbol: (require 'foo)
      (symbol? spec)
      (update-in machine [:ns current-ns :aliases] assoc spec spec)

      ;; Vector spec: (require '[foo :as f :refer [x y]])
      (vector? spec)
      (let [ns-sym (first spec)
            opts (apply hash-map (rest spec))
            alias-sym (:as opts)
            refers (:refer opts)]
        (cond-> machine
          alias-sym (update-in [:ns current-ns :aliases] assoc alias-sym ns-sym)
          (= :all refers) (update-in [:ns current-ns :aliases] assoc ns-sym ns-sym)
          (sequential? refers)
          (as-> m
            (reduce (fn [m sym]
                      (let [qualified (symbol (str ns-sym) (str sym))]
                        (if-let [entry (get (:heap m) qualified)]
                          (assoc-in m [:heap (symbol (str current-ns) (str sym))] entry)
                          m)))
                    m
                    refers))))

      :else machine)))

(defn step-eval-require [machine frame]
  (let [specs (rest (:expr frame))
        ;; Unquote specs — require args are quoted
        specs (map (fn [s] (if (and (seq? s) (= 'quote (first s))) (second s) s)) specs)
        machine (reduce process-require-spec machine specs)]
    (m/push-value machine nil)))

(defn step-eval-ns [machine frame]
  ;; (ns name & references)
  ;; Simplified: switch namespace + process :require, :import etc.
  (let [[_ ns-sym & refs] (:expr frame)
        machine (-> machine
                    (assoc :current-ns ns-sym)
                    (update :ns #(if (get % ns-sym) % (assoc % ns-sym {:aliases {} :refers {} :imports {}}))))]
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
                                                           (let [fqn (str pkg "." cls)]
                                                             #?(:clj
                                                                (try
                                                                  (let [klass (Class/forName fqn)]
                                                                    (update m'' :env assoc (symbol (str cls)) klass))
                                                                  (catch ClassNotFoundException _
                                                                    (throw (ex-info (str "Unable to resolve classname: " fqn)
                                                                                    {:type :sci/error}))))
                                                                :cljs m'')))
                                                         m' classes))
                                               m'))
                                           m ref-specs)
                           :refer-clojure m ;; TODO
                           :use m ;; TODO
                           m))
                       m))
                   machine
                   refs)]
      (m/push-value machine ns-sym))))

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
;; Special form dispatch
;; ============================================================

(defn step-eval-special [machine frame]
  (let [raw-head (first (:expr frame))
        head (if (qualified-symbol? raw-head)
               (symbol (name raw-head))
               raw-head)]
    (check-permission machine head)
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
      throw    (-> machine
                   (m/replace-frame {:op :throw})
                   (m/push-frame {:op :eval :expr (second (:expr frame))}))
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
      monitor-enter (m/push-value machine nil)
      monitor-exit  (m/push-value machine nil)
      (throw (ex-info (str "Special form not yet implemented: " head)
                      {:type :sci/error :form head})))))

;; ============================================================
;; Macro expansion
;; ============================================================

(defn try-resolve-macro
  "If the head of a list form is a symbol that resolves to a Clojure macro,
   return the macro var. Otherwise nil."
  [machine sym]
  (when (symbol? sym)
    (let [sym-ns (clojure.core/namespace sym)
          sym-name (name sym)
          heap (:heap machine)
          candidates (if sym-ns
                       [(symbol sym-ns sym-name)]
                       [(symbol (str (:current-ns machine)) sym-name)
                        (symbol "clojure.core" sym-name)])]
      (some (fn [qualified]
              (when-let [entry (get heap qualified)]
                (when (:macro? entry)
                  (:val entry))))
            candidates))))

(defn macroexpand-form
  "If form is a list whose head resolves to a host macro, expand it.
   Returns [expanded? new-form]."
  [machine form]
  (if-not (seq? form)
    [false form]
    (let [head (first form)]
      (if-let [macro-val (try-resolve-macro machine head)]
        (let [is-host-macro? (var? macro-val)
              macro-fn (if is-host-macro? @macro-val macro-val)
              expanded (if is-host-macro?
                         ;; Host macros get &form and &env as first two args
                         (apply macro-fn form {} (rest form))
                         ;; SCI-defined macros just get the args directly
                         (apply macro-fn (rest form)))]
          [true expanded])
        [false form]))))

;; ============================================================
;; Permission checking
;; ============================================================

(defn check-permission [machine sym]
  (let [perms (:permissions machine)
        allow (:allow perms)
        deny (:deny perms)]
    (when (and allow (seq allow))
      (let [sym-name (name sym)
            sym-ns (clojure.core/namespace sym)
            qualified (when sym-ns (symbol sym-ns sym-name))
            core-qualified (symbol "clojure.core" sym-name)
            allowed? (or (contains? (set allow) sym)
                         (contains? (set allow) core-qualified)
                         (when qualified (contains? (set allow) qualified)))]
        (when-not allowed?
          (throw (ex-info (str sym " is not allowed!")
                          {:type :sci/error})))))
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
            raw-name (subs (name head) 1)
            is-field? #?(:clj (.startsWith ^String raw-name "-")
                         :cljs (= "-" (subs raw-name 0 1)))
            member-name (if is-field?
                          (symbol (str "-" (subs raw-name 1))) ;; keep the dash for (. obj -field)
                          (symbol raw-name))
            obj-expr (second form)
            args (drop 2 form)
            dot-form (list* '. obj-expr member-name args)]
        (m/replace-frame machine {:op :eval :expr dot-form}))

      :new-call
      ;; (ClassName. args...) → (new ClassName args...)
      (let [head (first form)
            class-name (let [n (name head)] (subs n 0 (dec (count n))))
            new-form (list* 'new (symbol class-name) (rest form))]
        (m/replace-frame machine {:op :eval :expr new-form}))

      :invoke
      ;; Before invoking, check if head is a macro
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
             (step-eval-invoke machine frame)))))))

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
        :if              (step-if machine frame)
        :do              (step-do machine frame)
        :let             (step-let machine frame)
        :do-restore-env  (step-do-restore-env machine frame)
        :def             (step-def machine frame)
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
        :throw           (let [v (:result machine)
                               loc (or (:top-loc machine) (last (:callstack machine)) (:last-loc machine))]
                           (if (instance? #?(:clj Throwable :cljs js/Error) v)
                             ;; Wrap the original exception with location info
                             (throw (ex-info (or (ex-message v) (str #?(:clj (.getName (class v)) :cljs "Error")))
                                            (merge {:type :sci/error
                                                    :message (ex-message v)
                                                    :sci.impl/callstack (:callstack machine)}
                                                   (when loc
                                                     {:line (:line loc)
                                                      :column (:column loc)
                                                      :file (:file loc)}))
                                            v))
                             (throw (ex-info (str v)
                                            (merge {:type :sci/error
                                                    :sci.impl/callstack (:callstack machine)}
                                                   (when loc
                                                     {:line (:line loc)
                                                      :column (:column loc)
                                                      :file (:file loc)}))))))
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
  (if-let [[idx try-frame] (find-try-frame (:stack machine))]
    ;; Found a try frame — look for matching catch
    (let [catches (:catches try-frame)
          match (first
                 (filter (fn [catch-form]
                           (let [[_ class-sym _binding & _body] catch-form]
                             ;; Resolve the class
                             #?(:clj
                                (try
                                  (let [klass (if (= 'Exception class-sym)
                                                Exception
                                                (Class/forName (str class-sym)))]
                                    (instance? klass ex))
                                  (catch ClassNotFoundException _ false))
                                :cljs true)))
                         catches))]
      (if match
        (let [[_ _class-sym binding-sym & body] match
              ;; Truncate stack to the try frame
              new-stack (subvec (vec (:stack machine)) 0 idx)
              ;; Restore env and bind exception
              m (-> machine
                    (assoc :stack new-stack
                           :status :running)
                    (update :env assoc binding-sym ex))]
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
    ;; Prefer top-loc (outermost form) for the reported error location
    (let [loc (or (:top-loc machine) (:last-loc machine) (first (:callstack machine)))
          already-wrapped? (and (instance? #?(:clj clojure.lang.ExceptionInfo :cljs cljs.core/ExceptionInfo) ex)
                                (= :sci/error (:type (ex-data ex))))]
      (if (and already-wrapped? (:line (ex-data ex)))
        ;; Already has location info
        (throw ex)
        ;; Wrap or re-wrap with location info
        (throw (ex-info (or (ex-message ex) (str #?(:clj (.getName (class ex)) :cljs "Error")))
                        (merge (when already-wrapped? (ex-data ex))
                               {:type :sci/error
                                :message (ex-message ex)
                                :sci.impl/callstack (:callstack machine)}
                               (when loc
                                 {:line (:line loc)
                                  :column (:column loc)
                                  :file (:file loc)}))
                        (if already-wrapped? (ex-cause ex) ex)))))))

(defn run [machine]
  (loop [m machine]
    (case (:status m)
      :running (let [;; Keep thread-local dynamic bindings in sync
                     _ (reset! current-dynamic-bindings (:dynamic-bindings m))
                     next-m (try
                              (step m)
                              (catch #?(:clj Throwable :cljs :default) ex
                                (handle-exception m ex)))]
                 (recur next-m))
      :done    (:result m)
      :suspend m
      :effect  m)))
