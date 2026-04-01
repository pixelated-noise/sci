(ns sci.vm.cljs-bindings
  "CLJS-specific bindings for the SCI VM heap.
   On JVM, host functions are auto-discovered via ns-publics.
   On CLJS, they must be listed explicitly."
  #?(:cljs (:refer-clojure :exclude [type]))
  (:require [clojure.string :as str]
            [clojure.set :as set]
            [clojure.walk :as walk]
            [sci.lang]
            #?(:cljs [cljs.reader :as edn]))
  #?(:cljs (:require-macros [sci.vm.cljs-bindings :refer [clj-docstrings]])))

;; ============================================================
;; Helper to build heap entries
;; ============================================================

(defn- entry
  "Create a heap entry for a regular function/value."
  ([val] {:val val :meta {:name nil}})
  ([val m] {:val val :meta m}))

(defn- macro-entry
  "Create a heap entry for a macro.
   Macro fns receive [&form &env & args]."
  [val m]
  {:val val :meta (assoc m :macro true) :macro? true :host-macro? true})

#?(:clj
   (defmacro ^:private clj-docstrings
     "Compile-time macro: generates a map of {symbol -> {:doc d :arglists al}} for all
      public vars in clojure.core. Uses CLJ metadata which is available at compile time
      on both platforms."
     []
     (into {}
           (keep (fn [[sym v]]
                   (let [m (meta v)
                         doc (:doc m)
                         arglists (:arglists m)]
                     (when (or doc arglists)
                       ;; Strip metadata from sym — some symbols (e.g. inst-ms*) carry
                       ;; {:protocol #'clojure.core/Inst} which is not a valid CLJS constant
                       [(list 'quote (with-meta sym nil))
                        (merge
                         (when doc {:doc doc})
                         (when arglists
                           ;; Keep outer as list (for display as ([x]) not [[x]])
                           ;; but convert inner to vectors to strip metadata
                           {:arglists (list 'quote (apply list (mapv vec arglists)))}))]))))
           (ns-publics 'clojure.core))))

(defn- dynamic-entry
  "Create a heap entry for a dynamic var."
  [val m]
  {:val val :meta m :dynamic? true})

;; ============================================================
;; Destructuring support
;; ============================================================

(defn- vec-index-of
  "Find index of val in vector, or -1 if not found."
  [v val]
  (loop [i 0]
    (if (>= i (count v))
      -1
      (if (= val (nth v i)) i (recur (inc i))))))

(defn- destructure-binding
  "Expand a single destructuring binding pair [pattern expr] into a flat
   vector of [sym val sym val ...] for let*."
  [pattern expr]
  (cond
    ;; Simple symbol — no destructuring needed
    (symbol? pattern) [pattern expr]

    ;; Sequential destructuring: [a b & rest :as all]
    (vector? pattern)
    (let [gs (gensym "vec__")
          as-idx (vec-index-of pattern :as)
          as-sym (when (>= as-idx 0) (nth pattern (inc as-idx)))
          ;; Filter out :as and its symbol
          elems (if (>= as-idx 0)
                  (vec (concat (subvec pattern 0 as-idx)
                               (when (< (+ as-idx 2) (count pattern))
                                 (subvec pattern (+ as-idx 2)))))
                  pattern)
          ;; Handle & rest
          amp-idx (vec-index-of elems '&)
          positional (if (>= amp-idx 0) (subvec elems 0 amp-idx) elems)
          rest-sym (when (>= amp-idx 0) (nth elems (inc amp-idx)))]
      (loop [binds [gs expr gs `(seq ~gs)]
             pos (seq positional)
             cur-gs gs]
        (if pos
          (let [elem (first pos)
                inner (destructure-binding elem `(first ~cur-gs))
                next-gs (gensym "seq__")]
            (recur (into (into binds inner) [next-gs `(next ~cur-gs)])
                   (next pos) next-gs))
          (let [binds (if rest-sym
                        (into binds (destructure-binding rest-sym cur-gs))
                        binds)
                binds (if as-sym (into binds [as-sym gs]) binds)]
            binds))))

    ;; Associative destructuring: {:keys [a b] :strs [c] :or {a 1} :as m}
    (map? pattern)
    (let [gs (gensym "map__")
          as-sym (:as pattern)
          or-map (or (:or pattern) {})]
      (let [binds [gs expr]
            ;; Handle :keys
            binds (reduce
                   (fn [binds k]
                     (let [sym (if (keyword? k) (symbol (name k))
                                   (if (symbol? k) k (symbol (str k))))
                           kw (if (keyword? k) k (keyword (name (if (symbol? k) k (symbol (str k))))))]
                       (into binds
                             (destructure-binding
                              sym (if (contains? or-map sym)
                                    `(get ~gs ~kw ~(get or-map sym))
                                    `(get ~gs ~kw))))))
                   binds (:keys pattern))
            ;; Handle :strs
            binds (reduce
                   (fn [binds k]
                     (let [sym (symbol k)]
                       (into binds
                             (destructure-binding
                              sym (if (contains? or-map sym)
                                    `(get ~gs (str '~sym) ~(get or-map sym))
                                    `(get ~gs (str '~sym)))))))
                   binds (:strs pattern))
            ;; Handle :syms
            binds (reduce
                   (fn [binds k]
                     (let [sym k]
                       (into binds
                             (destructure-binding
                              sym (if (contains? or-map sym)
                                    `(get ~gs '~sym ~(get or-map sym))
                                    `(get ~gs '~sym))))))
                   binds (:syms pattern))
            ;; Handle namespaced :ns/keys
            binds (reduce
                   (fn [binds [k v]]
                     (if (and (keyword? k)
                              (namespace k)
                              (= "keys" (name k))
                              (vector? v))
                       (let [ns-part (namespace k)]
                         (reduce (fn [binds sym-k]
                                   (let [sym (if (keyword? sym-k) (symbol (name sym-k)) sym-k)
                                         kw (keyword ns-part (name sym))]
                                     (into binds
                                           (destructure-binding
                                            sym (if (contains? or-map sym)
                                                  `(get ~gs ~kw ~(get or-map sym))
                                                  `(get ~gs ~kw))))))
                                 binds v))
                       binds))
                   binds pattern)
            ;; Handle regular key-value pairs: {local-sym lookup-key}
            ;; In Clojure: {foo-val k} means bind foo-val to (get map k)
            binds (reduce
                   (fn [binds [local-sym lookup-key]]
                     (if (or (#{:keys :strs :syms :or :as} local-sym)
                             (and (keyword? local-sym)
                                  (namespace local-sym)
                                  (= "keys" (name local-sym))))
                       binds
                       (into binds
                             (destructure-binding local-sym
                                                  (if (contains? or-map local-sym)
                                                    `(get ~gs ~lookup-key ~(get or-map local-sym))
                                                    `(get ~gs ~lookup-key))))))
                   binds pattern)
            ;; Handle :as
            binds (if as-sym (into binds [as-sym gs]) binds)]
        binds))

    :else (throw (ex-info (str "Unsupported binding form: " (pr-str pattern)) {}))))

(defn- sci-destructure
  "Like clojure.core/destructure — expand bindings vector into flat let* bindings."
  [bindings]
  (let [pairs (partition 2 bindings)]
    (reduce (fn [acc [pattern expr]]
              (into acc (destructure-binding pattern expr)))
            [] pairs)))

;; ============================================================
;; Core macro implementations for CLJS
;; These produce forms using special forms that the VM handles.
;; Signature: [&form &env & args]
;; ============================================================

(defn- when-impl [_ _ test & body]
  (list 'if test (cons 'do body)))

(defn- when-not-impl [_ _ test & body]
  (list 'if test nil (cons 'do body)))

(defn- when-let-impl [_ _ bindings & body]
  (let [[sym test] bindings]
    `(let [temp# ~test]
       (when temp#
         (let [~sym temp#]
           ~@body)))))

(defn- when-first-impl [_ _ bindings & body]
  (let [[sym expr] bindings]
    `(when-let [xs# (seq ~expr)]
       (let [~sym (first xs#)]
         ~@body))))

(defn- when-some-impl [_ _ bindings & body]
  (let [[sym test] bindings]
    `(let [temp# ~test]
       (when (some? temp#)
         (let [~sym temp#]
           ~@body)))))

(defn- if-let-impl [_ _ bindings then else]
  (let [[sym test] bindings]
    `(let [temp# ~test]
       (if temp#
         (let [~sym temp#] ~then)
         ~else))))

(defn- if-some-impl
  ([_ _ bindings then] (if-some-impl nil nil bindings then nil))
  ([_ _ bindings then else]
   (let [[sym test] bindings]
     `(let [temp# ~test]
        (if (some? temp#)
          (let [~sym temp#] ~then)
          ~else)))))

(defn- and-impl
  ([_ _] true)
  ([_ _ x] x)
  ([_ _ x & next]
   `(let [and# ~x]
      (if and# (and ~@next) and#))))

(defn- or-impl
  ([_ _] nil)
  ([_ _ x] x)
  ([_ _ x & next]
   `(let [or# ~x]
      (if or# or# (or ~@next)))))

(defn- cond-impl [_ _ & clauses]
  (when (seq clauses)
    (list 'if (first clauses)
          (if (next clauses) (second clauses)
              (throw (ex-info "cond requires an even number of forms" {})))
          (cons 'clojure.core/cond (next (next clauses))))))

(defn- condp-impl [_ _ pred expr & clauses]
  (let [gpred (gensym "pred__")
        gexpr (gensym "expr__")
        emit (fn emit [pred expr args]
               (let [[[a b c :as clause] more]
                     (split-at (if (= :>> (second args)) 3 2) args)
                     n (count clause)]
                 (cond
                   (= 0 n) `(throw (ex-info (str "No matching clause: " ~expr) {}))
                   (= 1 n) a
                   (= 2 n) `(if (~pred ~a ~expr) ~b ~(emit pred expr more))
                   :else `(if-let [p# (~pred ~a ~expr)] (~c p#) ~(emit pred expr more)))))]
    `(let [~gpred ~pred ~gexpr ~expr]
       ~(emit gpred gexpr clauses))))

(defn- ->-impl [_ _ x & forms]
  (loop [x x, forms forms]
    (if forms
      (let [form (first forms)
            threaded (if (seq? form)
                       (with-meta `(~(first form) ~x ~@(next form)) (meta form))
                       (list form x))]
        (recur threaded (next forms)))
      x)))

(defn- ->>-impl [_ _ x & forms]
  (loop [x x, forms forms]
    (if forms
      (let [form (first forms)
            threaded (if (seq? form)
                       (with-meta `(~(first form) ~@(next form) ~x) (meta form))
                       (list form x))]
        (recur threaded (next forms)))
      x)))

(defn- as->-impl [_ _ expr name & forms]
  `(let [~name ~expr
         ~@(interleave (repeat name) (butlast forms))]
     ~(if (empty? forms) name (last forms))))

(defn- cond->-impl [_ _ expr & clauses]
  (let [g (gensym)
        steps (map (fn [[test step]] `(if ~test (-> ~g ~step) ~g))
                   (partition 2 clauses))]
    `(let [~g ~expr
           ~@(interleave (repeat g) steps)]
       ~g)))

(defn- cond->>-impl [_ _ expr & clauses]
  (let [g (gensym)
        steps (map (fn [[test step]] `(if ~test (->> ~g ~step) ~g))
                   (partition 2 clauses))]
    `(let [~g ~expr
           ~@(interleave (repeat g) steps)]
       ~g)))

(defn- some->-impl [_ _ expr & forms]
  (let [g (gensym)
        steps (map (fn [step] `(if (nil? ~g) nil (-> ~g ~step)))
                   forms)]
    `(let [~g ~expr
           ~@(interleave (repeat g) steps)]
       ~g)))

(defn- some->>-impl [_ _ expr & forms]
  (let [g (gensym)
        steps (map (fn [step] `(if (nil? ~g) nil (->> ~g ~step)))
                   forms)]
    `(let [~g ~expr
           ~@(interleave (repeat g) steps)]
       ~g)))

(defn- doto-impl [_ _ x & forms]
  (let [gx (gensym)]
    `(let [~gx ~x]
       ~@(map (fn [f]
                (with-meta
                  (if (seq? f)
                    `(~(first f) ~gx ~@(next f))
                    `(~f ~gx))
                  (meta f)))
              forms)
       ~gx)))

(defn- dotimes-impl [_ _ bindings & body]
  (let [[i n] bindings]
    `(let [n# (int ~n)]
       (loop [~i 0]
         (when (< ~i n#)
           ~@body
           (recur (inc ~i)))))))

(defn- while-impl [_ _ test & body]
  `(loop []
     (when ~test
       ~@body
       (recur))))

(defn- let-impl [_ _ bindings & body]
  `(let* ~(sci-destructure bindings) ~@body))

(defn- fn-impl [_ _ & sigs]
  (let [[name sigs] (if (symbol? (first sigs))
                      [(first sigs) (rest sigs)]
                      [nil sigs])
        sigs (if (vector? (first sigs))
               ;; single arity: (fn [a b] body)
               (list sigs)
               ;; multi-arity: (fn ([a] ...) ([a b] ...))
               sigs)
        ;; Expand destructuring in params
        expand-arity (fn [sig]
                       (let [params (first sig)
                             body (rest sig)
                             ;; Extract pre/post conditions
                             [pre-post body] (if (and (map? (first body))
                                                      (or (:pre (first body)) (:post (first body))))
                                               [(first body) (rest body)]
                                               [nil body])
                             pre-checks (when-let [pres (:pre pre-post)]
                                          (map (fn [p] (list 'clojure.core/assert p)) pres))
                             post-check (:post pre-post)
                             ;; Wrap body with pre/post conditions
                             body (if (or pre-checks post-check)
                                    (let [inner (if (seq pre-checks)
                                                  (concat pre-checks body)
                                                  body)]
                                      (if post-check
                                        (let [ret (gensym "ret__")]
                                          (list (list 'let* [ret (cons 'do inner)]
                                                      (cons 'do (map (fn [p]
                                                                       (list 'when-not
                                                                             (clojure.walk/postwalk-replace {'% ret} p)
                                                                             (list 'throw (list 'ex-info
                                                                                                (str "Assert failed: " (pr-str p))
                                                                                                {}))))
                                                                     post-check))
                                                      ret)))
                                        inner))
                                    body)
                             ;; Check if params need destructuring
                             needs-destr? (some #(or (map? %) (vector? %)) params)]
                         (if needs-destr?
                           (let [;; Detect [... & map-pattern] for kwargs
                                 amp-idx (vec-index-of (vec params) '&)
                                 has-kwargs? (and (>= amp-idx 0)
                                                  (map? (nth params (inc amp-idx) nil)))
                                 ;; Replace complex params with gensyms
                                 new-params (mapv (fn [p] (if (symbol? p) p (gensym "p__"))) params)
                                 ;; Build let bindings for destructured params
                                 let-binds (reduce (fn [acc [orig new-p]]
                                                     (if (symbol? orig)
                                                       acc
                                                       ;; For kwargs map pattern: convert seq to map first
                                                       (if (and has-kwargs? (map? orig))
                                                         (let [map-gs (gensym "kwargs__")]
                                                           (into (conj acc
                                                                       map-gs (list 'if (list 'clojure.core/and
                                                                                              (list '= 1 (list 'clojure.core/count new-p))
                                                                                              (list 'map? (list 'first new-p)))
                                                                                    (list 'first new-p)
                                                                                    (list 'clojure.core/apply 'clojure.core/hash-map new-p)))
                                                                 (destructure-binding orig map-gs)))
                                                         (into acc (destructure-binding orig new-p)))))
                                                   [] (map vector params new-params))]
                             (if (seq let-binds)
                               `(~new-params (let* ~let-binds ~@body))
                               `(~params ~@body)))
                           `(~params ~@body))))
        expanded (map expand-arity sigs)]
    (if (= 1 (count expanded))
      (if name
        `(fn* ~name ~@(first expanded))
        `(fn* ~@(first expanded)))
      (if name
        `(fn* ~name ~@expanded)
        `(fn* ~@expanded)))))

(defn- loop-impl [_ _ bindings & body]
  (let [pairs (partition 2 bindings)
        syms (mapv first pairs)
        needs-destr? (some #(or (map? %) (vector? %)) syms)]
    (if needs-destr?
      ;; Destructuring in loop bindings requires:
      ;; 1. Sequential init evaluation (later inits may reference earlier destructured names)
      ;; 2. Simple symbols for loop* (needed by recur)
      ;; 3. Re-destructuring on each iteration
      ;; Strategy: use let* to sequentially init and destructure, then loop* with temps
      (let [temps (mapv (fn [s] (if (symbol? s) s (gensym "loop__"))) syms)
            init-vals (mapv second pairs)
            ;; Build sequential let bindings: temp = init, then destructure
            init-let-binds (reduce
                            (fn [acc [orig temp init]]
                              (let [acc (conj acc temp init)]
                                (if (symbol? orig)
                                  acc
                                  (into acc (destructure-binding orig temp)))))
                            [] (map vector syms temps init-vals))
            ;; Build loop body let bindings: re-destructure temps each iteration
            loop-let-binds (reduce
                            (fn [acc [orig temp]]
                              (if (symbol? orig)
                                acc
                                (into acc (destructure-binding orig temp))))
                            [] (map vector syms temps))]
        `(let* ~init-let-binds
           (loop* ~(vec (interleave temps temps))
                  (let* ~loop-let-binds ~@body))))
      `(loop* ~bindings ~@body))))

(defn- letfn-impl [_ _ fnspecs & body]
  (let [bindings (vec (mapcat (fn [spec]
                                (let [[name & sigs] spec]
                                  [name `(fn ~name ~@sigs)]))
                              fnspecs))]
    `(letfn* ~bindings ~@body)))

(defn- declare-impl [_ _ & names]
  (list* 'do (map (fn [n] (list 'def n)) names)))

(defn- defn-impl [_ _ & args]
  (let [[name args] [(first args) (rest args)]
        [docstring args] (if (string? (first args))
                           [(first args) (rest args)]
                           [nil args])
        [attr-map args] (if (map? (first args))
                          [(first args) (rest args)]
                          [nil args])
        _ (when (empty? args)
            (throw (ex-info (str "Parameter declaration missing") {})))
        _ (when (and (seq? (first args)) (not (vector? (first (first args)))))
            (throw (ex-info (str "Parameter declaration should be a vector") {})))
        _ (when (and (not (vector? (first args))) (not (seq? (first args))))
            (throw (ex-info (str "Parameter declaration should be a vector") {})))
        ;; Check for trailing attr-map in multi-arity form
        [trailing-map args] (if (and (not (vector? (first args)))
                                     (map? (last args))
                                     (> (count args) 1))
                              [(last args) (butlast args)]
                              [nil args])
        ;; fn body — single arity or multi-arity
        fn-form (if (vector? (first args))
                  ;; single arity: (defn name [params] body...)
                  `(fn ~name ~@args)
                  ;; multi-arity: (defn name ([p1] b1) ([p2 p3] b2) ...)
                  `(fn ~name ~@args))
        meta-map (merge (when docstring {:doc docstring})
                        attr-map
                        trailing-map)]
    (if (seq meta-map)
      `(def ~(with-meta name (merge (meta name) meta-map)) ~fn-form)
      `(def ~name ~fn-form))))

(defn- defn--impl [_ _ & args]
  (let [[name & rest-args] args]
    `(defn ~(with-meta name (assoc (meta name) :private true)) ~@rest-args)))

(defn- defonce-impl [_ _ name expr]
  ;; In SCI, just def if not yet defined
  `(when-not (clojure.core/resolve '~name)
     (def ~name ~expr)))

(defn- doseq-impl [_ _ seq-exprs & body]
  (cond
    (empty? seq-exprs)
    `(do ~@body)

    (keyword? (first seq-exprs))
    (let [[kw expr & more] seq-exprs]
      (case kw
        :let  `(let ~expr (doseq ~(vec more) ~@body))
        :when `(when ~expr (doseq ~(vec more) ~@body))
        :while `(if ~expr (doseq ~(vec more) ~@body) nil)))

    :else
    (let [[bind expr & more] seq-exprs]
      (if (empty? more)
        ;; Last binding — simple loop
        `(loop [s# (seq ~expr)]
           (when s#
             (let [~bind (first s#)]
               ~@body)
             (recur (next s#))))
        ;; More bindings remain — recurse
        `(loop [s# (seq ~expr)]
           (when s#
             (let [~bind (first s#)]
               (doseq ~(vec more) ~@body))
             (recur (next s#))))))))

(defn- for-impl [_ _ & args]
  (let [arg-count (count args)]
    (when-not (= 2 arg-count)
      (throw (ex-info (str "Wrong number of args (" arg-count ") passed to: clojure.core/for") {}))))
  (let [seq-exprs (first args)
        body-expr (second args)]
    (when-not (vector? seq-exprs)
      (throw (ex-info "for requires a vector for its binding" {})))
    (when-not (even? (count seq-exprs))
      (throw (ex-info "for requires an even number of forms in binding vector" {})))
    ;; Validate modifier keywords
    (doseq [[k _v] (partition 2 seq-exprs)]
      (when (keyword? k)
        (when-not (#{:let :when :while} k)
          (throw (ex-info (str "Unsupported keyword in for: " k ". Only :let, :when, :while are valid keyword modifiers.") {})))))
    (if (empty? seq-exprs)
      ;; Base case: no more bindings, just produce the body in a list
      (list 'list body-expr)
      (let [[bind expr & more] seq-exprs]
        (if (and (nil? more) (not (keyword? bind)))
          ;; Last binding — simple map
          `(map (fn [~bind] ~body-expr) ~expr)
          ;; Complex for with multiple bindings/modifiers
          (if (keyword? bind)
            (cond
              (= :let bind)
              `(let ~expr (for ~(vec more) ~body-expr))
              (= :when bind)
              `(if ~expr (for ~(vec more) ~body-expr) (list))
              (= :while bind)
              `(if ~expr (for ~(vec more) ~body-expr) (list)))
            `(mapcat (fn [~bind] (for ~(vec more) ~body-expr)) ~expr)))))))

(defn- comment-impl [_ _ & _body] nil)

(defn- assert-impl
  ([_ _ x]
   (list 'when (symbol "clojure.core" "*assert*")
         (list 'when-not x
               (list 'throw (list 'ex-info (list 'str "Assert failed: " (list 'quote x)) {})))))
  ([_ _ x message]
   (list 'when (symbol "clojure.core" "*assert*")
         (list 'when-not x
               (list 'throw (list 'ex-info (list 'str "Assert failed: " message "\n" (list 'quote x)) {}))))))

(defn- if-not-impl
  ([_ _ test then] `(if (not ~test) ~then nil))
  ([_ _ test then else] `(if (not ~test) ~then ~else)))

(defn- case-impl [_ _ expr & clauses]
  ;; The VM case* expects: (case* expr shift mask default case-map mode keys-type)
  ;; where case-map is {hash [test-val result-expr], ...}
  (let [default (when (odd? (count clauses)) (last clauses))
        clauses (if (odd? (count clauses)) (butlast clauses) clauses)
        pairs (partition 2 clauses)
        ;; Check for duplicate test constants
        _ (let [all-tests (mapcat (fn [[test _]]
                                    (if (and (sequential? test) (not (vector? test)))
                                      (seq test)
                                      [test]))
                                  pairs)
                freqs (frequencies all-tests)]
            (doseq [[t cnt] freqs]
              (when (> cnt 1)
                (throw (ex-info (str "Duplicate case test constant: " t) {})))))
        ge (gensym "case__")
        ;; Build case-map: for each test constant, map its hash to [test result]
        ;; For grouped tests like (2 3), create separate entries for each
        case-map (reduce (fn [acc [test then]]
                           (if (and (sequential? test) (not (vector? test)))
                             ;; Multiple test values: (2 3) matches either
                             (reduce (fn [a t]
                                       (assoc a (hash t) [t then]))
                                     acc test)
                             (assoc acc (hash test) [test then])))
                         {} pairs)
        default-expr (or default (list 'throw (list 'ex-info (list 'str "No matching clause: " ge) {})))]
    (list 'let* [ge expr]
          (list 'case* ge 0 0 default-expr case-map :int nil))))

(defn- lazy-seq-impl [_ _ & body]
  (list 'clojure.core/lazy-seq* (list 'fn* [] (cons 'do body))))

(defn- delay-impl [_ _ & body]
  (list 'clojure.core/delay* (list 'fn* [] (cons 'do body))))

(defn- with-meta-impl [_ _ obj m]
  `(clojure.core/with-meta ~obj ~m))

(defn- reify-impl [_ _ & specs]
  ;; Parse specs: alternating protocol-name then method forms
  ;; (reify Protocol (method [this] body) Protocol2 (method2 [this] body))
  ;; => (reify* [Protocol Protocol2] (method [this] body) (method2 [this] body))
  (let [{:keys [interfaces methods]}
        (reduce (fn [acc spec]
                  (if (symbol? spec)
                    (update acc :interfaces conj spec)
                    (update acc :methods conj spec)))
                {:interfaces [] :methods []}
                specs)]
    (list* 'reify* interfaces methods)))

(defn- import-impl [_ _ & import-specs]
  ;; (import foo.Bar) => (import* "foo.Bar")
  ;; (import (foo Bar Baz)) => (do (import* "foo.Bar") (import* "foo.Baz"))
  (let [forms (mapcat (fn [spec]
                        (if (symbol? spec)
                          [(list 'import* (str spec))]
                           ;; List form: (package Class1 Class2)
                          (let [package (first spec)]
                            (map (fn [cls]
                                   (list 'import* (str package "." cls)))
                                 (rest spec)))))
                      import-specs)]
    (if (= 1 (count forms))
      (first forms)
      (cons 'do forms))))

(defn- with-redefs-impl [_ _ bindings & body]
  ;; (with-redefs [var val ...] body) — temporarily redefine vars
  (let [pairs (partition 2 bindings)
        old-syms (mapv (fn [_] (gensym "old__")) pairs)
        save-forms (mapv (fn [old-sym [var-sym _]]
                           [old-sym (list 'deref (list 'var var-sym))])
                         old-syms pairs)
        set-forms (mapv (fn [[var-sym val-expr]]
                          (list 'set! var-sym val-expr))
                        pairs)
        restore-forms (mapv (fn [old-sym [var-sym _]]
                              (list 'set! var-sym old-sym))
                            old-syms pairs)]
    `(let [~@(apply concat save-forms)]
       ~@set-forms
       (try
         (do ~@body)
         (finally
           ~@restore-forms)))))

(defn- with-out-str-impl [_ _ & body]
  ;; with-out-str — capture print output to a string
  ;; Expands to code that calls helper fns to redirect *print-fn* to a buffer
  (let [state (gensym "wos__")]
    `(let [~state (clojure.core/--sci-with-out-str-start)]
       (try
         (do ~@body)
         (finally
           (clojure.core/--sci-with-out-str-end ~state)))
       (deref (first ~state)))))

(defn- with-local-vars-impl [_ _ bindings & body]
  ;; (with-local-vars [x 1 y 2] body) — create locally-scoped vars
  (when-not (vector? bindings)
    (throw (ex-info "with-local-vars requires a vector for its bindings" {:type :sci/error})))
  (when (odd? (count bindings))
    (throw (ex-info "with-local-vars requires an even number of forms in binding vector"
                    {:type :sci/error})))
  (let [pairs (partition 2 bindings)
        let-bindings (mapcat (fn [[sym val]]
                               [sym (list 'atom val)])
                             pairs)]
    `(let [~@let-bindings]
       ~@body)))

(defn- areduce-impl [_ _ a idx ret init expr]
  ;; (areduce a idx ret init expr) → loop over array indices
  (list 'let* [a a]
        (list 'loop* [idx (int 0) ret init]
              (list 'if (list '< idx (list 'clojure.core/alength a))
                    (list 'recur (list 'clojure.core/unchecked-inc idx) expr)
                    ret))))

(defn- ..-impl [_ _ x & forms]
  ;; (.. x (m1) (m2)) → (. (. x (m1)) (m2))
  (if forms
    (let [expanded (reduce (fn [acc form]
                             (if (seq? form)
                               (list* '. acc form)
                               (list '. acc form)))
                           x forms)]
      expanded)
    (list '. x)))

(defn- exists?-impl [_ _ sym]
  ;; exists? checks if a symbol is defined (not nil/undefined)
  ;; For dotted js/ paths like js/foo.bar, walk the property chain
  (let [s (str sym)]
    (if (and (clojure.string/starts-with? s "js/")
             (clojure.string/includes? (subs s 3) "."))
      ;; Dotted path: js/foo.bar.baz → check each step
      (let [parts (clojure.string/split (subs s 3) #"\.")
            ;; First part is looked up via js/
            first-sym (symbol "js" (first parts))
            rest-parts (rest parts)
            ;; Build a chain of property accesses
            g (gensym "obj__")]
        (list 'clojure.core/some?
              (list 'try
                    (list 'let [g first-sym]
                          (reduce (fn [expr part]
                                    (list 'when (list 'clojure.core/some? expr)
                                          (list '. expr (symbol (str "-" part)))))
                                  g rest-parts))
                    (list 'catch :default '_ nil))))
      ;; Simple symbol: just try to resolve it
      (list 'clojure.core/some? (list 'try sym (list 'catch :default '_ nil))))))

(defn- time-impl [_ _ expr]
  ;; (time expr) → prints elapsed time, returns value
  (let [start (gensym "start__")
        ret (gensym "ret__")]
    (list 'let* [start (list 'cljs.core/system-time)
                 ret expr]
          (list 'prn (list 'str "Elapsed time: "
                           (list '- (list 'cljs.core/system-time) start)
                           " msecs"))
          ret)))

(defn- memfn-impl [_ _ method-name & args]
  ;; (memfn method arg1 arg2) → (fn [target arg1 arg2] (. target method arg1 arg2))
  (let [target (gensym "target__")]
    (list 'fn* (vec (cons target args))
          (list '. target (cons method-name args)))))

(defn- amap-impl [_ _ a idx ret expr]
  ;; (amap a idx ret expr) → clone array, loop filling with expr
  (list 'let* [ret (list 'clojure.core/aclone a)]
        (list 'loop* [idx (list 'int 0)]
              (list 'if (list '< idx (list 'clojure.core/alength ret))
                    (list 'do
                          (list 'clojure.core/aset ret idx expr)
                          (list 'recur (list 'inc idx)))
                    ret))))

;; ============================================================
;; clojure.core function registry for CLJS
;; ============================================================

#?(:cljs
   (defn cljs-core-functions
     "Returns a map of qualified-symbol -> heap-entry for clojure.core functions."
     []
     (let [fns {'= = '< < '<= <= '> > '>= >= '+ + '- - '* * '/ /
                '== == 'aclone aclone 'aget aget 'alength alength 'aset aset 'apply apply
                'assoc assoc 'assoc-in assoc-in 'associative? associative?
                'array-map array-map 'atom atom
                'bit-and-not bit-and-not 'bit-set bit-set
                'bit-shift-left bit-shift-left 'bit-shift-right bit-shift-right
                'bit-xor bit-xor 'boolean boolean 'boolean? boolean?
                'butlast butlast 'bit-test bit-test
                'bit-and bit-and 'bounded-count bounded-count
                'bit-or bit-or 'bit-flip bit-flip 'bit-not bit-not
                'cat cat 'char char 'char? char?
                'conj conj 'cons cons 'contains? contains? 'count count
                'cycle cycle 'comp comp 'concat concat
                'comparator comparator 'coll? coll? 'compare compare
                'complement complement 'constantly constantly
                'completing completing 'counted? counted?
                'chunk chunk 'chunk-append chunk-append
                'chunk-buffer chunk-buffer 'chunk-cons chunk-cons
                'chunk-first chunk-first 'chunk-rest chunk-rest
                'chunk-next chunk-next 'chunked-seq? chunked-seq?
                'compare-and-set! compare-and-set!
                'dec dec 'dedupe dedupe
                'deref (fn sci-deref [ref]
                         (if-let [type-obj (:type (clojure.core/meta ref))]
                           (if (and (some? type-obj) (unchecked-get type-obj "methods$"))
                             (let [methods (unchecked-get type-obj "methods$")
                                   deref-fn (or (get methods 'deref) (get methods '-deref))]
                               (if deref-fn (deref-fn ref) (deref ref)))
                             (deref ref))
                           (deref ref)))
                'dissoc dissoc 'distinct distinct 'distinct? distinct?
                'disj disj 'doall doall 'dorun dorun
                'double double 'double? double?
                'drop drop 'drop-last drop-last 'drop-while drop-while
                'eduction eduction 'empty empty 'empty? empty?
                'even? even? 'every? every? 'every-pred every-pred
                'ensure-reduced ensure-reduced 'ex-info ex-info
                'ex-message ex-message 'ex-data ex-data 'ex-cause ex-cause
                'first first 'float float 'float? float? 'fnil fnil
                'fnext fnext 'ffirst ffirst 'flatten flatten
                'false? false? 'filter filter 'filterv filterv
                'find find 'frequencies frequencies 'fn? fn? 'ifn? ifn?
                'get get 'get-in get-in 'group-by group-by
                'gensym gensym 'hash hash 'hash-map hash-map
                'hash-set hash-set 'hash-unordered-coll hash-unordered-coll
                'ident? ident? 'identical? identical? 'identity identity
                'inc inc 'int-array int-array 'interleave interleave
                'js-in (fn [key obj] (js* "~{} in ~{}" key obj))
                'into into 'iterate iterate 'int int 'int? int?
                'interpose interpose 'indexed? indexed?
                'integer? integer? 'into-array into-array
                'juxt juxt 'keep keep 'keep-indexed keep-indexed
                'key key 'keys keys 'keyword keyword 'keyword? keyword?
                'last last 'list list 'list? list? 'list* list*
                'long-array long-array
                'map clojure.core/map 'map? map? 'map-indexed map-indexed
                'map-entry? map-entry? 'mapv mapv 'mapcat mapcat
                'max max 'max-key max-key 'memoize memoize 'meta meta
                'merge merge 'merge-with merge-with
                'min min 'min-key min-key 'munge munge 'mod mod
                'make-array make-array 'name name
                'namespace namespace 'newline newline
                'nfirst nfirst 'not not 'not= not=
                'not-every? not-every? 'neg? neg? 'neg-int? neg-int?
                'nth nth 'nthnext nthnext 'nthrest nthrest
                'nil? nil? 'nat-int? nat-int? 'number? number?
                'not-empty not-empty 'not-any? not-any?
                'next next 'nnext nnext
                'odd? odd? 'object-array object-array
                'peek peek 'pop pop 'pos? pos? 'pos-int? pos-int?
                'partial partial 'partition partition
                'partition-all partition-all 'partition-by partition-by
                'pr pr 'prn prn 'pr-str pr-str 'prn-str prn-str
                'print print 'println println
                'print-str print-str
                'qualified-ident? qualified-ident?
                'qualified-symbol? qualified-symbol?
                'qualified-keyword? qualified-keyword?
                'quot quot
                're-seq re-seq 're-find re-find
                're-pattern re-pattern 're-matches re-matches
                'rem rem 'remove remove 'rest rest
                'repeatedly repeatedly 'reverse reverse
                'rand-int rand-int 'rand-nth rand-nth
                'range range 'reduce reduce 'reduce-kv reduce-kv
                'reduced reduced 'reduced? reduced?
                'reversible? reversible? 'rsubseq rsubseq
                'reductions reductions 'rand rand
                'replace replace 'rseq rseq
                'random-sample random-sample 'repeat repeat
                'reset! (fn sci-reset! [ref v]
                          (if-let [type-obj (:type (clojure.core/meta ref))]
                            (if (and (some? type-obj) (unchecked-get type-obj "methods$"))
                              (let [methods (unchecked-get type-obj "methods$")
                                    reset-fn (or (get methods 'reset) (get methods '-reset!))]
                                (if reset-fn (reset-fn ref v) (reset! ref v)))
                              (reset! ref v))
                            (reset! ref v)))
                'reset-meta! reset-meta!
                'set? set? 'sequential? sequential?
                'select-keys select-keys
                'simple-keyword? simple-keyword?
                'simple-symbol? simple-symbol?
                'some? some? 'string? string?
                'str str 'second second 'set set 'seq seq 'seq? seq?
                'shuffle shuffle 'sort sort 'sort-by sort-by
                'subs subs
                'swap! (fn sci-swap!
                         ([ref f]
                          (if-let [type-obj (:type (clojure.core/meta ref))]
                            (if (and (some? type-obj) (unchecked-get type-obj "methods$"))
                              (let [methods (unchecked-get type-obj "methods$")
                                    swap-fn (or (get methods 'swap) (get methods '-swap!))]
                                (if swap-fn (swap-fn ref f) (swap! ref f)))
                              (swap! ref f))
                            (swap! ref f)))
                         ([ref f a]
                          (if-let [type-obj (:type (clojure.core/meta ref))]
                            (if (and (some? type-obj) (unchecked-get type-obj "methods$"))
                              (let [methods (unchecked-get type-obj "methods$")
                                    swap-fn (or (get methods 'swap) (get methods '-swap!))]
                                (if swap-fn (swap-fn ref f a) (swap! ref f a)))
                              (swap! ref f a))
                            (swap! ref f a)))
                         ([ref f a b]
                          (if-let [type-obj (:type (clojure.core/meta ref))]
                            (if (and (some? type-obj) (unchecked-get type-obj "methods$"))
                              (let [methods (unchecked-get type-obj "methods$")
                                    swap-fn (or (get methods 'swap) (get methods '-swap!))]
                                (if swap-fn (swap-fn ref f a b) (swap! ref f a b)))
                              (swap! ref f a b))
                            (swap! ref f a b)))
                         ([ref f a b & args]
                          (if-let [type-obj (:type (clojure.core/meta ref))]
                            (if (and (some? type-obj) (unchecked-get type-obj "methods$"))
                              (let [methods (unchecked-get type-obj "methods$")
                                    swap-fn (or (get methods 'swap) (get methods '-swap!))]
                                (if swap-fn (apply swap-fn ref f a b args) (apply swap! ref f a b args)))
                              (apply swap! ref f a b args))
                            (apply swap! ref f a b args))))
                'symbol symbol 'symbol? symbol?
                'special-symbol? special-symbol? 'subvec subvec
                'some-fn some-fn 'some some
                'split-at split-at 'split-with split-with
                'sorted-set sorted-set 'subseq subseq 'system-time system-time
                'sorted-set-by sorted-set-by
                'sorted-map-by sorted-map-by
                'sorted-map sorted-map 'sorted? sorted?
                'simple-ident? simple-ident?
                'sequence sequence 'seqable? seqable?
                'take take 'take-last take-last
                'take-nth take-nth 'take-while take-while
                'trampoline trampoline 'transduce transduce
                'tree-seq tree-seq
                'type clojure.core/type
                'true? true? 'to-array to-array 'to-array-2d to-array-2d
                'update update 'update-in update-in
                'uri? uri? 'uuid? uuid?
                'unchecked-inc-int unchecked-inc-int
                'unchecked-negate unchecked-negate
                'unsigned-bit-shift-right unsigned-bit-shift-right
                'unchecked-add-int unchecked-add-int
                'unchecked-multiply-int unchecked-multiply-int
                'unchecked-int unchecked-int
                'unchecked-multiply unchecked-multiply
                'unchecked-add unchecked-add
                'unreduced unreduced 'unquote nil 'unquote-splicing nil
                'unchecked-subtract unchecked-subtract
                'unchecked-inc unchecked-inc
                'val val 'vals vals 'vary-meta vary-meta
                'vec vec 'vector vector 'vector? vector?
                'volatile! volatile! 'vreset! vreset!
                'vswap! (fn [vol f & args] (vreset! vol (apply f @vol args)))
                'with-meta with-meta
                'zipmap zipmap 'zero? zero?
                ;; Additional CLJS functions
                'clj->js clj->js 'js->clj js->clj
                'undefined? undefined?
                'array array 'js-obj js-obj
                'regexp? regexp?
                ;; Atoms / state
                'add-watch add-watch 'remove-watch remove-watch
                ;; Lazy seqs
                'lazy-seq* (fn [thunk] (lazy-seq (thunk)))
                'delay* (fn [thunk] (delay (thunk)))
                'force force 'delay? delay?
                'realized? realized?
                ;; Collections
                'transient transient 'persistent! persistent!
                'conj! conj! 'assoc! assoc! 'dissoc! dissoc!
                'pop! pop! 'disj! disj!
                ;; Multimethods support
                'make-hierarchy make-hierarchy
                ;; Misc
                'tagged-literal tagged-literal 'tagged-literal? tagged-literal?
                'inst? inst? 'inst-ms inst-ms
                'abs abs 'parse-long parse-long 'parse-double parse-double
                'parse-boolean parse-boolean 'parse-uuid parse-uuid
                'NaN? NaN? 'Inf? Inf?
                '*assert* true
                ;; Dynamic vars (REPL and printer settings)
                '*1 nil '*2 nil '*3 nil '*e nil
                '*print-dup* false
                '*print-readably* true
                '*print-namespace-maps* true
                '*print-meta* false
                '*print-level* nil
                '*file* nil '*ns* nil
                ;; Protocol functions (for ifn? checks and extend-protocol)
                '-pr-writer -pr-writer
                '-write -write
                ;; Misc
                'random-uuid random-uuid
                ;; with-out-str helpers
                '--sci-with-out-str-start
                (fn []
                  (let [sb (volatile! "")
                        old-print-fn *print-fn*
                        old-print-err-fn *print-err-fn*]
                    (set! *print-fn* (fn [x] (vswap! sb str x)))
                    (set! *print-err-fn* (fn [x] (vswap! sb str x)))
                    [sb old-print-fn old-print-err-fn]))
                '--sci-with-out-str-end
                (fn [[_ old-print-fn old-print-err-fn]]
                  (set! *print-fn* old-print-fn)
                  (set! *print-err-fn* old-print-err-fn))}]
       (let [var-meta (clj-docstrings)]
         (reduce-kv
          (fn [acc sym v]
            (assoc acc (symbol "clojure.core" (str sym))
                   {:val v :meta (merge {:name sym}
                                        (get var-meta sym))}))
          {} fns)))))

;; ============================================================
;; clojure.core macros for CLJS
;; ============================================================

#?(:cljs
   (defn cljs-core-macros
     "Returns a map of qualified-symbol -> macro heap-entry for clojure.core macros."
     []
     (let [macros {'let        let-impl
                   'fn         fn-impl
                   'loop       loop-impl
                   'letfn      letfn-impl
                   'when       when-impl
                   'when-not   when-not-impl
                   'when-let   when-let-impl
                   'when-first when-first-impl
                   'when-some  when-some-impl
                   'if-let     if-let-impl
                   'if-some    if-some-impl
                   'if-not     if-not-impl
                   'and        and-impl
                   'or         or-impl
                   'cond       cond-impl
                   'condp      condp-impl
                   '->         ->-impl
                   '->>        ->>-impl
                   'as->       as->-impl
                   'cond->     cond->-impl
                   'cond->>    cond->>-impl
                   'some->     some->-impl
                   'some->>    some->>-impl
                   'doto       doto-impl
                   'dotimes    dotimes-impl
                   'while      while-impl
                   'declare    declare-impl
                   'defn       defn-impl
                   'defn-      defn--impl
                   'defonce    defonce-impl
                   'doseq      doseq-impl
                   'for        for-impl
                   'comment    comment-impl
                   'assert     assert-impl
                   'case       case-impl
                   'lazy-seq   lazy-seq-impl
                   'delay      delay-impl
                   'reify      reify-impl
                   'exists?    exists?-impl
                   'time       time-impl
                   'memfn      memfn-impl
                   'amap       amap-impl
                   'import     import-impl
                   'with-redefs with-redefs-impl
                   'with-local-vars with-local-vars-impl
                   'with-out-str with-out-str-impl
                   'areduce areduce-impl
                   '.. ..-impl}]
       (let [var-meta (clj-docstrings)]
         (reduce-kv
          (fn [acc sym v]
            (assoc acc (symbol "clojure.core" (str sym))
                   {:val v
                    :meta (merge {:name sym :macro true}
                                 (get var-meta sym))
                    :macro? true
                    :host-macro? true}))
          {} macros)))))

;; ============================================================
;; clojure.string for CLJS
;; ============================================================

#?(:cljs
   (defn cljs-string-ns
     "Returns a map of qualified-symbol -> heap-entry for clojure.string."
     []
     (let [fns {'blank?        str/blank?
                'capitalize    str/capitalize
                'ends-with?    str/ends-with?
                'escape        str/escape
                'includes?     str/includes?
                'index-of      str/index-of
                'join          str/join
                'last-index-of str/last-index-of
                'lower-case    str/lower-case
                'replace       str/replace
                'replace-first str/replace-first
                'reverse       str/reverse
                'split         str/split
                'split-lines   str/split-lines
                'starts-with?  str/starts-with?
                'trim          str/trim
                'trim-newline  str/trim-newline
                'triml         str/triml
                'trimr         str/trimr
                'upper-case    str/upper-case}]
       (reduce-kv
        (fn [acc sym v]
          (assoc acc (symbol "clojure.string" (str sym))
                 {:val v :meta {:name sym}}))
        {} fns))))

;; ============================================================
;; clojure.set for CLJS
;; ============================================================

#?(:cljs
   (defn cljs-set-ns
     "Returns a map of qualified-symbol -> heap-entry for clojure.set."
     []
     (let [fns {'difference  set/difference
                'index       set/index
                'intersection set/intersection
                'join        set/join
                'map-invert  set/map-invert
                'project     set/project
                'rename      set/rename
                'rename-keys set/rename-keys
                'select      set/select
                'subset?     set/subset?
                'superset?   set/superset?
                'union       set/union}]
       (reduce-kv
        (fn [acc sym v]
          (assoc acc (symbol "clojure.set" (str sym))
                 {:val v :meta {:name sym}}))
        {} fns))))

;; ============================================================
;; clojure.walk for CLJS
;; ============================================================

#?(:cljs
   (defn cljs-walk-ns
     "Returns a map of qualified-symbol -> heap-entry for clojure.walk."
     []
     (let [fns {'walk            walk/walk
                'postwalk        walk/postwalk
                'prewalk         walk/prewalk
                'postwalk-replace walk/postwalk-replace
                'prewalk-replace walk/prewalk-replace
                'keywordize-keys walk/keywordize-keys
                'stringify-keys  walk/stringify-keys}]
       (reduce-kv
        (fn [acc sym v]
          (assoc acc (symbol "clojure.walk" (str sym))
                 {:val v :meta {:name sym}}))
        {} fns))))

;; ============================================================
;; clojure.edn for CLJS
;; ============================================================

#?(:cljs
   (defn cljs-edn-ns
     "Returns a map of qualified-symbol -> heap-entry for clojure.edn."
     []
     (let [fns {'read-string edn/read-string}]
       (reduce-kv
        (fn [acc sym v]
          (assoc acc (symbol "clojure.edn" (str sym))
                 {:val v :meta {:name sym}}))
        {} fns))))

;; ============================================================
;; Combined CLJS heap
;; ============================================================

#?(:cljs
   (defn- mirror-cljs-core
     "For every clojure.core/* entry, add a cljs.core/* alias pointing to the
      same heap entry. This is needed because syntax-quote in CLJS qualifies
      symbols as cljs.core/foo, but the VM heap registers them as clojure.core/foo."
     [heap]
     (reduce-kv
      (fn [acc sym entry]
        (if (= "clojure.core" (namespace sym))
          (assoc acc (symbol "cljs.core" (name sym)) entry)
          acc))
      heap heap)))

#?(:cljs
   (defn- make-sci-protocol
     "Create a minimal SCI protocol map for a host CLJS protocol."
     [proto-name method-names]
     {:type :sci/protocol
      :name proto-name
      :methods (into {} (map (fn [m] [m {:name m}]) method-names))
      :impls (atom {})}))

#?(:cljs
   (defn cljs-heap
     "Build the full CLJS heap with all namespace bindings."
     []
     (let [;; SCI protocol entries for key CLJS host protocols
           ;; These allow extend-protocol, satisfies?, and custom dispatch to work
           protos {(symbol "clojure.core" "IPrintWithWriter")
                   {:val (make-sci-protocol 'clojure.core/IPrintWithWriter ['-pr-writer])
                    :meta {:name 'IPrintWithWriter}}
                   (symbol "clojure.core" "IDeref")
                   {:val (make-sci-protocol 'clojure.core/IDeref ['-deref])
                    :meta {:name 'IDeref}}
                   (symbol "clojure.core" "ISwap")
                   {:val (make-sci-protocol 'clojure.core/ISwap ['-swap!])
                    :meta {:name 'ISwap}}
                   (symbol "clojure.core" "IReset")
                   {:val (make-sci-protocol 'clojure.core/IReset ['-reset!])
                    :meta {:name 'IReset}}
                   (symbol "clojure.core" "IWriter")
                   {:val (make-sci-protocol 'clojure.core/IWriter ['-write '-flush])
                    :meta {:name 'IWriter}}
                   (symbol "clojure.core" "IRecord")
                   {:val (make-sci-protocol 'clojure.core/IRecord [])
                    :meta {:name 'IRecord}}
                   ;; sci.lang.Type — expose for instance? checks
                   (symbol "sci.lang" "Type")
                   {:val sci.lang/Type
                    :meta {:name 'Type}}}]
       (-> (merge (cljs-core-functions)
                  (cljs-core-macros)
                  (cljs-string-ns)
                  (cljs-set-ns)
                  (cljs-walk-ns)
                  (cljs-edn-ns)
                  protos)
           (mirror-cljs-core)))))
