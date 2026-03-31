(ns sci.freeze-test
  (:require [clojure.test :refer [deftest is testing]]
            [sci.core :as sci]
            [sci.vm.machine :as m]
            [sci.vm.freeze :as freeze]))

;; Helper: eval-string that returns the machine (not the result) when suspended
(defn eval-suspend
  "Evaluate code, expecting a suspended machine back."
  ([s] (eval-suspend s nil))
  ([s opts]
   (let [result (sci/eval-string s opts)]
     (assert (and (map? result) (= :suspend (:status result)))
             (str "Expected suspended machine, got: " (pr-str result)))
     result)))

;; ============================================================
;; Basic suspend/resume (no serialization)
;; ============================================================

(deftest suspend-returns-machine
  (testing "suspend! returns a suspended machine"
    (let [m (eval-suspend "(suspend!)")]
      (is (= :suspend (:status m)))
      (is (nil? (:suspend-data m))))))

(deftest suspend-with-data
  (testing "suspend! with an argument captures data"
    (let [m (eval-suspend "(suspend! {:reason :waiting})")]
      (is (= :suspend (:status m)))
      (is (= {:reason :waiting} (:suspend-data m))))))

(deftest resume-with-value
  (testing "resume with a value makes suspend! return that value"
    (let [m (eval-suspend "(let [x (suspend!)] (+ x 10))")
          result (sci/resume m 42)]
      (is (= 52 result)))))

(deftest resume-with-nil
  (testing "resume without a value makes suspend! return nil"
    (let [m (eval-suspend "(let [x (suspend!)] x)")
          result (sci/resume m)]
      (is (nil? result)))))

(deftest suspend-in-do
  (testing "suspend in the middle of a do block"
    (let [m (eval-suspend "(do (def x 1) (suspend!) (+ x 1))")
          result (sci/resume m)]
      (is (= 2 result)))))

;; ============================================================
;; Freeze/thaw round-trip
;; ============================================================

(deftest freeze-thaw-basic
  (testing "freeze → thaw → resume produces correct result"
    (let [m (eval-suspend "(do (def x 1) (suspend!) (+ x 1))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 2 result)))))

(deftest freeze-produces-valid-edn
  (testing "frozen output is valid EDN"
    (let [m (eval-suspend "(do (def x 42) (suspend!))")
          frozen (freeze/freeze m)]
      (is (string? frozen))
      (is (map? (clojure.edn/read-string frozen))))))

(deftest freeze-excludes-host-fns
  (testing "frozen output does NOT contain clojure.core entries"
    (let [m (eval-suspend "(suspend!)")
          frozen (freeze/freeze m)]
      (is (not (re-find #"clojure\.core/map" frozen))))))

;; ============================================================
;; Closures survive freeze
;; ============================================================

(deftest freeze-thaw-closure
  (testing "user-defined closure survives freeze/thaw"
    (let [m (eval-suspend "(let [f (fn [x] (+ x 1))] (suspend!) (f 10))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 11 result)))))

(deftest freeze-thaw-host-fn-ref
  (testing "host fn reference survives freeze/thaw"
    (let [m (eval-suspend "(let [f inc] (suspend!) (f 41))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 42 result)))))

(deftest freeze-thaw-host-fn-in-call
  (testing "host fns still callable after thaw (map, str, etc.)"
    (let [m (eval-suspend "(do (def xs [1 2 3]) (suspend!) (mapv inc xs))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [2 3 4] result)))))

;; ============================================================
;; Dynamic bindings survive freeze
;; ============================================================

(deftest freeze-thaw-dynamic-bindings
  (testing "dynamic bindings survive freeze/thaw"
    (let [m (eval-suspend "(do (def ^:dynamic *x* 1) (binding [*x* 2] (suspend!) *x*))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 2 result)))))

;; ============================================================
;; Resume value through freeze/thaw
;; ============================================================

(deftest freeze-thaw-resume-with-value
  (testing "resume with value works after freeze/thaw"
    (let [m (eval-suspend "(let [x (suspend!)] (* x 2))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed 21)]
      (is (= 42 result)))))

;; ============================================================
;; Loop/recur
;; ============================================================

(deftest freeze-thaw-loop-recur
  (testing "loop/recur result available after freeze/thaw"
    (let [m (eval-suspend
             "(do (suspend!)
                  (loop [i 0 acc 0]
                    (if (= i 3) acc (recur (inc i) (+ acc i)))))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 3 result)))))

(deftest freeze-thaw-loop-resume-value
  (testing "resume value injected into loop via suspend"
    (let [m (eval-suspend
             "(loop [i 0 acc []]
                (if (= i 3)
                  acc
                  (let [v (suspend!)]
                    (recur (inc i) (conj acc v)))))")
          ;; First suspend at i=0
          frozen1 (freeze/freeze m)
          m1 (freeze/thaw frozen1)
          m1 (sci/resume m1 :a)  ;; resume returns next suspended machine
          ;; Second suspend at i=1
          frozen2 (freeze/freeze m1)
          m2 (freeze/thaw frozen2)
          m2 (sci/resume m2 :b)
          ;; Third suspend at i=2
          frozen3 (freeze/freeze m2)
          m3 (freeze/thaw frozen3)
          result (sci/resume m3 :c)]
      (is (= [:a :b :c] result)))))

;; ============================================================
;; Try/catch/finally
;; ============================================================

(deftest freeze-thaw-try-catch
  (testing "suspend inside try body survives freeze/thaw"
    (let [m (eval-suspend
             "(try
                (suspend!)
                42
                (catch Exception e :error))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 42 result)))))

(deftest freeze-thaw-try-catch-exception
  (testing "suspend before exception in try survives freeze/thaw"
    (let [m (eval-suspend
             "(try
                (let [x (suspend!)]
                  (if (= x :throw)
                    (throw (ex-info \"boom\" {:val x}))
                    x))
                (catch Exception e
                  (str \"caught: \" (.getMessage e))))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed :throw)]
      (is (= "caught: boom" result)))))

;; ============================================================
;; Conditionals
;; ============================================================

(deftest freeze-thaw-if-branch
  (testing "suspend in if branch survives freeze/thaw"
    (let [m (eval-suspend
             "(if true
                (do (suspend!) :yes)
                :no)")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= :yes result)))))

(deftest freeze-thaw-cond
  (testing "suspend inside cond survives freeze/thaw"
    (let [m (eval-suspend
             "(let [x (suspend!)]
                (cond
                  (= x :a) 1
                  (= x :b) 2
                  :else 3))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed :b)]
      (is (= 2 result)))))

;; ============================================================
;; Nested closures and higher-order functions
;; ============================================================

(deftest freeze-thaw-nested-closure
  (testing "nested closures (closure over closure) survive freeze/thaw"
    (let [m (eval-suspend
             "(let [adder (fn [a] (fn [b] (+ a b)))
                    add5 (adder 5)]
                (suspend!)
                (add5 10))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 15 result)))))

(deftest freeze-thaw-higher-order-with-host
  (testing "host higher-order fn (map) with user closure survives freeze/thaw"
    (let [m (eval-suspend
             "(let [double (fn [x] (* x 2))]
                (suspend!)
                (mapv double [1 2 3 4]))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [2 4 6 8] result)))))

(deftest freeze-thaw-fn-composition
  (testing "manual fn composition survives freeze/thaw"
    (let [m (eval-suspend
             "(let [f (fn [x] (str (inc x)))]
                (suspend!)
                (f 41))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= "42" result)))))

;; ============================================================
;; Multiple suspends in sequence
;; ============================================================

(deftest freeze-thaw-multiple-suspends
  (testing "multiple suspend/freeze/thaw cycles in sequence"
    (let [m1 (eval-suspend
              "(do
                 (def a (suspend!))
                 (def b (suspend!))
                 (+ a b))")
          frozen1 (freeze/freeze m1)
          m2 (freeze/thaw frozen1)
          m2 (sci/resume m2 10)  ;; a = 10, hits second suspend
          frozen2 (freeze/freeze m2)
          m3 (freeze/thaw frozen2)
          result (sci/resume m3 32)]  ;; b = 32
      (is (= 42 result)))))

;; ============================================================
;; Atoms in environment
;; ============================================================

(deftest freeze-thaw-atom
  (testing "atoms in environment survive freeze/thaw"
    (let [m (eval-suspend
             "(do
                (def counter (atom 0))
                (swap! counter inc)
                (swap! counter inc)
                (suspend!)
                @counter)")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 2 result)))))

(deftest freeze-thaw-atom-swap-after-resume
  (testing "atoms remain mutable after thaw"
    (let [m (eval-suspend
             "(do
                (def counter (atom 10))
                (suspend!)
                (swap! counter + 5)
                @counter)")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 15 result)))))

;; ============================================================
;; Destructuring
;; ============================================================

(deftest freeze-thaw-destructuring-let
  (testing "let destructuring survives freeze/thaw"
    (let [m (eval-suspend
             "(let [{:keys [a b]} (suspend!)]
                (+ a b))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed {:a 10 :b 32})]
      (is (= 42 result)))))

(deftest freeze-thaw-destructuring-sequential
  (testing "sequential destructuring survives freeze/thaw"
    (let [m (eval-suspend
             "(let [[x y & rest] (suspend!)]
                {:x x :y y :rest rest})")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed [1 2 3 4 5])]
      (is (= {:x 1 :y 2 :rest '(3 4 5)} result)))))

;; ============================================================
;; Metadata preservation
;; ============================================================

(deftest freeze-thaw-metadata-on-suspend-data
  (testing "metadata on suspend-data keyword keys survives freeze/thaw"
    (let [m (eval-suspend "(suspend! {:a 1 :b 2})")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)]
      (is (= {:a 1 :b 2} (:suspend-data thawed))))))

;; ============================================================
;; Deep stack / nested calls
;; ============================================================

(deftest freeze-thaw-deep-calls
  (testing "deeply nested function calls survive freeze/thaw"
    (let [m (eval-suspend
             "(do (defn wrap [x] {:val x})
                  (defn double-wrap [x] (wrap (wrap x)))
                  (defn triple-wrap [x] (wrap (double-wrap x)))
                  (suspend!)
                  (triple-wrap 42))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= {:val {:val {:val 42}}} result)))))

(deftest freeze-thaw-recursive-fn
  (testing "recursive function defined before suspend works after thaw"
    (let [m (eval-suspend
             "(do (defn factorial [n]
                    (if (<= n 1) 1 (* n (factorial (dec n)))))
                  (suspend!)
                  (factorial 10))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 3628800 result)))))

;; ============================================================
;; Multimethod
;; ============================================================

(deftest suspend-resume-multimethod
  (testing "multimethod dispatch survives suspend/resume (without freeze)"
    (let [m (eval-suspend
             "(do (defmulti greet :lang)
                  (defmethod greet :en [_] \"hello\")
                  (defmethod greet :fr [_] \"bonjour\")
                  (suspend!)
                  [(greet {:lang :en}) (greet {:lang :fr})])")
          result (sci/resume m)]
      (is (= ["hello" "bonjour"] result)))))

;; ============================================================
;; Case expression
;; ============================================================

(deftest freeze-thaw-case
  (testing "case expression after suspend survives freeze/thaw"
    (let [m (eval-suspend
             "(let [x (suspend!)]
                (case x
                  :a 1
                  :b 2
                  :c 3
                  0))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed :b)]
      (is (= 2 result)))))

;; ============================================================
;; String operations / host interop
;; ============================================================

(deftest freeze-thaw-string-ops
  (testing "string operations (host fns from clojure.string) survive freeze/thaw"
    (let [m (eval-suspend
             "(do (require '[clojure.string :as str])
                  (suspend!)
                  (str/join \", \" [\"a\" \"b\" \"c\"]))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= "a, b, c" result)))))

;; ============================================================
;; Complex data in suspend-data
;; ============================================================

(deftest freeze-thaw-complex-suspend-data
  (testing "complex suspend data survives freeze/thaw"
    (let [m (eval-suspend
             "(suspend! {:items [1 2 3]
                         :nested {:a #{:x :y}}
                         :msg \"waiting\"})")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)]
      (is (= {:items [1 2 3]
              :nested {:a #{:x :y}}
              :msg "waiting"}
             (:suspend-data thawed))))))

;; ============================================================
;; Namespace state
;; ============================================================

(deftest freeze-thaw-def-and-defn
  (testing "def and defn bindings survive freeze/thaw"
    (let [m (eval-suspend
             "(do (def pi 3.14159)
                  (defn area [r] (* pi r r))
                  (suspend!)
                  (area 10))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (< (Math/abs (- 314.159 result)) 0.001)))))

;; ============================================================
;; Protocols
;; ============================================================

(deftest suspend-resume-protocol
  (testing "protocol extension survives suspend/resume (without freeze)"
    (let [m (eval-suspend
             "(do (defprotocol Greetable
                    (greet [this]))
                  (defrecord Person [name])
                  (extend-protocol Greetable
                    Person
                    (greet [this] (str \"Hello, \" (:name this))))
                  (suspend!)
                  (greet (->Person \"Alice\")))")
          result (sci/resume m)]
      (is (= "Hello, Alice" result)))))

;; ============================================================
;; Large / complex environment
;; ============================================================

(deftest freeze-thaw-large-env
  (testing "large environment with many bindings survives freeze/thaw"
    (let [m (eval-suspend
             "(let [a 1 b 2 c 3 d 4 e 5
                    f 6 g 7 h 8 i 9 j 10
                    data {:a a :b b :c c :d d :e e
                          :f f :g g :h h :i i :j j}]
                (suspend!)
                (apply + (vals data)))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 55 result)))))

;; ============================================================
;; Multimethod, protocol, comp, partial, and loop freeze/thaw
;; ============================================================

(deftest freeze-thaw-multimethod
  (testing "multimethod dispatch should survive freeze/thaw"
    (let [m (eval-suspend
             "(do (defmulti greet :lang)
                  (defmethod greet :en [_] \"hello\")
                  (suspend!)
                  (greet {:lang :en}))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= "hello" result)))))

(deftest freeze-thaw-protocol
  (testing "protocol dispatch should survive freeze/thaw"
    (let [m (eval-suspend
             "(do (defprotocol Greetable
                    (greet [this]))
                  (defrecord Person [name])
                  (extend-protocol Greetable
                    Person
                    (greet [this] (str \"Hello, \" (:name this))))
                  (suspend!)
                  (greet (->Person \"Alice\")))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= "Hello, Alice" result)))))

(deftest freeze-thaw-comp
  (testing "comp should survive freeze/thaw"
    (let [m (eval-suspend
             "(let [f (comp str inc)]
                (suspend!)
                (f 41))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= "42" result)))))

(deftest freeze-thaw-partial
  (testing "partial should survive freeze/thaw"
    (let [m (eval-suspend
             "(let [add5 (partial + 5)]
                (suspend!)
                (add5 10))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 15 result)))))

(deftest freeze-thaw-metadata
  (testing "metadata on collections should survive freeze/thaw"
    (let [m (eval-suspend
             "(do (def data (with-meta [1 2 3] {:source :test}))
                  (suspend!)
                  (meta data))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= {:source :test} result)))))

(deftest freeze-thaw-suspend-inside-loop-body
  (testing "suspend inside a loop body should resume to the correct value"
    (let [m (eval-suspend
             "(loop [i 0 acc 0]
                (if (= i 3)
                  (do (suspend!) acc)
                  (recur (inc i) (+ acc i))))")
          result (sci/resume m)]
      (is (= 3 result)))))

;; ============================================================
;; Known limitations — these tests assert desired behavior that
;; doesn't work yet. They are expected to FAIL.
;; ============================================================

(deftest freeze-thaw-multimethod-destructuring
  (testing "multimethod methods with destructuring params should survive freeze/thaw"
    (let [m (eval-suspend
             "(do (defmulti area :shape)
                  (defmethod area :circle [{:keys [r]}] (* 3.14 r r))
                  (defmethod area :rect [{:keys [w h]}] (* w h))
                  (suspend!)
                  [(area {:shape :circle :r 10}) (area {:shape :rect :w 3 :h 4})])")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [314.0 12] result)))))

(deftest freeze-thaw-deftype-inline-protocol
  (testing "deftype with inline protocol methods should survive freeze/thaw"
    (let [m (eval-suspend
             "(do (defprotocol Greetable (greet [this]))
                  (deftype Greeter [name]
                    Greetable
                    (greet [this] (str \"Hi, \" (:name this))))
                  (suspend!)
                  (greet (->Greeter \"Bob\")))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= "Hi, Bob" result)))))

(deftest freeze-thaw-multiple-protocols
  (testing "multiple protocols on the same record should survive freeze/thaw"
    (let [m (eval-suspend
             "(do (defprotocol Named (get-name [this]))
                  (defprotocol Aged (get-age [this]))
                  (defrecord Person [name age])
                  (extend-protocol Named Person (get-name [this] (:name this)))
                  (extend-protocol Aged Person (get-age [this] (:age this)))
                  (suspend!)
                  (let [p (->Person \"Alice\" 30)]
                    [(get-name p) (get-age p)]))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= ["Alice" 30] result)))))

(deftest freeze-thaw-extend-type
  (testing "extend-type should survive freeze/thaw"
    (let [m (eval-suspend
             "(do (defprotocol Describable (describe [this]))
                  (defrecord Dog [name breed])
                  (extend-type Dog
                    Describable
                    (describe [this] (str (:name this) \" the \" (:breed this))))
                  (suspend!)
                  (describe (->Dog \"Rex\" \"Lab\")))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= "Rex the Lab" result)))))

(deftest freeze-thaw-comp-user-fns
  (testing "comp of user-defined fns should survive freeze/thaw"
    (let [m (eval-suspend
             "(do (defn my-double [x] (* 2 x))
                  (defn add1 [x] (+ 1 x))
                  (let [f (comp my-double add1)]
                    (suspend!)
                    (f 5)))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 12 result)))))

(deftest freeze-thaw-partial-user-fn
  (testing "partial of user-defined fn should survive freeze/thaw"
    (let [m (eval-suspend
             "(do (defn add [a b] (+ a b))
                  (let [add10 (partial add 10)]
                    (suspend!)
                    (add10 5)))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 15 result)))))

(deftest freeze-thaw-atom-identity-in-closure
  (testing "atom identity should be preserved across closure env boundaries"
    (let [m (eval-suspend
             "(do (let [counter (atom 0)]
                    (defn bump [] (swap! counter inc))
                    (bump) (bump) (bump)
                    (suspend!)
                    (bump)
                    @counter))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 4 result)))))

;; ============================================================
;; Known limitations — host HOFs that return closures
;; ============================================================

(deftest ^:known-limitation freeze-thaw-juxt
  (testing "juxt of user fns should survive freeze/thaw"
    (let [m (eval-suspend
             "(do (defn double-it [x] (* 2 x))
                  (defn inc-it [x] (+ 1 x))
                  (let [f (juxt double-it inc-it)]
                    (suspend!)
                    (f 5)))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [10 6] result)))))

(deftest ^:known-limitation freeze-thaw-every-pred
  (testing "every-pred should survive freeze/thaw"
    (let [m (eval-suspend
             "(let [f (every-pred pos? even?)]
                (suspend!)
                [(f 4) (f 3) (f -2)])")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [true false false] result)))))

(deftest ^:known-limitation freeze-thaw-some-fn
  (testing "some-fn should survive freeze/thaw"
    (let [m (eval-suspend
             "(let [f (some-fn :a :b)]
                (suspend!)
                [(f {:a 1}) (f {:b 2}) (f {:c 3})])")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [1 2 nil] result)))))

(deftest ^:known-limitation freeze-thaw-complement
  (testing "complement should survive freeze/thaw"
    (let [m (eval-suspend
             "(let [f (complement pos?)]
                (suspend!)
                [(f 1) (f -1) (f 0)])")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [false true true] result)))))

(deftest ^:known-limitation freeze-thaw-memoize
  (testing "memoize should survive freeze/thaw"
    (let [m (eval-suspend
             "(do (defn slow-fn [x] (* x x))
                  (let [f (memoize slow-fn)]
                    (suspend!)
                    [(f 3) (f 4)]))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [9 16] result)))))

(deftest ^:known-limitation freeze-thaw-fnil
  (testing "fnil should survive freeze/thaw"
    (let [m (eval-suspend
             "(let [f (fnil + 0 0)]
                (suspend!)
                [(f 1 2) (f nil 5) (f 3 nil)])")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [3 5 3] result)))))

;; ============================================================
;; Known limitations — data types
;; ============================================================

(deftest ^:known-limitation freeze-thaw-sorted-set
  (testing "sorted-set ordering should be preserved after freeze/thaw"
    (let [m (eval-suspend
             "(let [s (sorted-set 5 3 1 4 2)]
                (suspend!)
                (vec s))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [1 2 3 4 5] result)))))

(deftest ^:known-limitation freeze-thaw-delay
  (testing "delay should survive freeze/thaw"
    (let [m (eval-suspend
             "(let [d (delay (+ 1 2))]
                (suspend!)
                @d)")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 3 result)))))

(deftest ^:known-limitation freeze-thaw-volatile
  (testing "volatile should survive freeze/thaw"
    (let [m (eval-suspend
             "(let [v (volatile! 42)]
                (suspend!)
                @v)")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 42 result)))))

;; ============================================================
;; Known limitations — deftype Object method dispatch
;; ============================================================

(deftest ^:known-limitation freeze-thaw-deftype-object-methods
  (testing "deftype Object methods (toString) should survive freeze/thaw"
    (let [m (eval-suspend
             "(do (deftype Counter [n]
                    Object
                    (toString [this] (str \"Counter(\" (:n this) \")\")))
                  (let [c (->Counter 42)]
                    (suspend!)
                    (str c)))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= "Counter(42)" result)))))
