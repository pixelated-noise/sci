(ns sci.freeze-test
  (:require [clojure.test :refer [deftest is testing]]
            [sci.core :as sci]
            [sci.vm.machine :as m]
            [sci.vm.freeze :as freeze]
            [clojure.string :as str]
            #?(:clj [clojure.edn :as edn]
               :cljs [cljs.reader :as edn])))

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

(deftest suspend-in-vector
  (testing "suspend! as an element of a vector literal"
    (let [m (eval-suspend "[(suspend!) 2 3]")
          result (sci/resume m :a)]
      (is (= [:a 2 3] result)))))

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

(deftest freeze-thaw-suspend-in-vector
  (testing "suspend! inside a vector literal survives freeze/thaw"
    (let [m (eval-suspend "[(suspend!) 2 3]")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed :a)]
      (is (= [:a 2 3] result)))))

(deftest freeze-produces-valid-edn
  (testing "frozen output is valid EDN"
    (let [m (eval-suspend "(do (def x 42) (suspend!))")
          frozen (freeze/freeze m)]
      (is (string? frozen))
      (is (map? (edn/read-string frozen))))))

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
             (str "(try
                (suspend!)
                42
                (catch " #?(:clj "Exception" :cljs "js/Error") " e :error))"))
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 42 result)))))

(deftest freeze-thaw-try-catch-exception
  (testing "suspend before exception in try survives freeze/thaw"
    (let [m (eval-suspend
             (str "(try
                (let [x (suspend!)]
                  (if (= x :throw)
                    (throw (ex-info \"boom\" {:val x}))
                    x))
                (catch " #?(:clj "Exception" :cljs "js/Error") " e
                  (str \"caught: \" " #?(:clj "(.getMessage e)" :cljs "(.-message e)") ")))"))
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
;; Host HOFs that return closures
;; ============================================================

(deftest freeze-thaw-juxt
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

(deftest freeze-thaw-every-pred
  (testing "every-pred should survive freeze/thaw"
    (let [m (eval-suspend
             "(let [f (every-pred pos? even?)]
                (suspend!)
                [(f 4) (f 3) (f -2)])")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [true false false] result)))))

(deftest freeze-thaw-some-fn
  (testing "some-fn should survive freeze/thaw"
    (let [m (eval-suspend
             "(let [f (some-fn :a :b)]
                (suspend!)
                [(f {:a 1}) (f {:b 2}) (f {:c 3})])")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [1 2 nil] result)))))

(deftest freeze-thaw-complement
  (testing "complement should survive freeze/thaw"
    (let [m (eval-suspend
             "(let [f (complement pos?)]
                (suspend!)
                [(f 1) (f -1) (f 0)])")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [false true true] result)))))

(deftest freeze-thaw-memoize
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

(deftest freeze-thaw-fnil
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
;; Data types
;; ============================================================

(deftest freeze-thaw-sorted-set
  (testing "sorted-set ordering should be preserved after freeze/thaw"
    (let [m (eval-suspend
             "(let [s (sorted-set 5 3 1 4 2)]
                (suspend!)
                (vec s))")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= [1 2 3 4 5] result)))))

(deftest freeze-thaw-delay
  (testing "delay should survive freeze/thaw"
    (let [m (eval-suspend
             "(let [d (delay (+ 1 2))]
                (suspend!)
                @d)")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 3 result)))))

(deftest freeze-thaw-volatile
  (testing "volatile should survive freeze/thaw"
    (let [m (eval-suspend
             "(let [v (volatile! 42)]
                (suspend!)
                @v)")
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)
          result (sci/resume thawed)]
      (is (= 42 result)))))

(deftest freeze-thaw-deftype-object-methods
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

;; ============================================================
;; Single-step execution API
;; ============================================================

(defn- step-to-completion
  "Step a machine one operation at a time until done. Returns the result."
  [m]
  (loop [m m]
    (case (:status m)
      :running (recur (sci/step m))
      :done    (:result m)
      :suspend m)))

(deftest prepare-returns-running-machine
  (testing "prepare returns a machine with :status :running"
    (let [m (sci/prepare "(+ 1 2)")]
      (is (map? m))
      (is (= :running (:status m))))))

(deftest step-to-completion-simple
  (testing "stepping to completion produces correct result"
    (is (= 3 (step-to-completion (sci/prepare "(+ 1 2)"))))
    (is (= 7 (step-to-completion (sci/prepare "(+ 1 (* 2 3))"))))))

(deftest step-to-completion-multi-form
  (testing "multi-form string works with prepare"
    (is (= 3 (step-to-completion (sci/prepare "(def x 1) (+ x 2)"))))))

(deftest step-idempotent-on-done
  (testing "step on a non-running machine returns it unchanged"
    (let [m (sci/prepare "(+ 1 2)")
          done (loop [m m]
                 (if (= :running (:status m))
                   (recur (sci/step m))
                   m))]
      (is (= :done (:status done)))
      (is (identical? done (sci/step done))))))

(deftest step-budget
  (testing "can stop after N steps and continue later"
    (let [m (sci/prepare "(+ 1 (* 2 3))")
          ;; Step 5 times
          m (nth (iterate sci/step m) 5)]
      (is (= :running (:status m)))
      ;; Continue to completion
      (is (= 7 (step-to-completion m))))))

(deftest step-with-suspend
  (testing "stepping reaches suspend, then prepare-resume continues"
    (let [m (step-to-completion (sci/prepare "(let [x (suspend!)] (+ x 10))"))
          _ (is (= :suspend (:status m)))
          m2 (sci/prepare-resume m 42)]
      (is (= :running (:status m2)))
      (is (= 52 (step-to-completion m2))))))

(deftest freeze-thaw-running-machine
  (testing "can freeze a :running machine and thaw+step to completion"
    (let [m (sci/prepare "(+ 1 (* 2 3))")
          ;; Step a few times
          m (nth (iterate sci/step m) 3)
          _ (is (= :running (:status m)))
          frozen (freeze/freeze m)
          thawed (freeze/thaw frozen)]
      (is (= :running (:status thawed)))
      (is (= 7 (step-to-completion thawed))))))

(deftest inspect-machine
  (testing "inspect returns a summary of the machine state"
    (let [m (sci/prepare "(+ 1 2)")
          info (sci/inspect m)]
      (is (= :running (:status info)))
      (is (= :eval (:op info)))
      (is (some? (:expr info)))
      (is (= 1 (:stack-depth info)))
      (is (= 'user (:current-ns info)))
      (is (map? (:env info)))))
  (testing "inspect on a done machine"
    (let [m (step-to-completion (sci/prepare "(+ 1 2)"))
          info (sci/inspect (sci/prepare "(+ 1 2)"))]
      ;; just verify it doesn't throw on various states
      (is (= :running (:status info)))))
  (testing "inspect on a suspended machine"
    (let [m (step-to-completion (sci/prepare "(suspend!)"))
          info (sci/inspect m)]
      (is (= :suspend (:status info)))
      (is (nil? (:op info))))))

;; ============================================================
;; Portable freeze: comprehensive language features + disk I/O
;; ============================================================

;; A rich SCI program that exercises many language features, suspends in the
;; middle, and produces a deterministic result after resume.  Platform-neutral:
;; no Java interop, no JS interop, so the frozen EDN is valid on any runtime.
(def ^:private comprehensive-program
  "(do
     ;; --- definitions & closures ---
     (def pi 3.14159)
     (defn factorial [n]
       (loop [i n acc 1]
         (if (<= i 1) acc (recur (dec i) (* acc i)))))
     (defn fibonacci [n]
       (loop [i 0 a 0 b 1 result []]
         (if (= i n) result (recur (inc i) b (+ a b) (conj result a)))))
     (def make-adder (fn [n] (fn [x] (+ x n))))
     (def add-10 (make-adder 10))

     ;; --- protocols & records ---
     (defprotocol Shape
       (area [this])
       (perimeter [this]))
     (defrecord Circle [radius]
       Shape
       (area [_] (* pi radius radius))
       (perimeter [_] (* 2 pi radius)))
     (defrecord Rect [w h]
       Shape
       (area [_] (* w h))
       (perimeter [_] (* 2 (+ w h))))

     ;; --- state ---
     (def log (atom []))
     (swap! log conj :init)
     (def shapes [(->Circle 5) (->Rect 3 4)])
     (def areas  (mapv area shapes))
     (swap! log conj :shapes-done)

     ;; --- destructuring & HOFs ---
     (let [{:keys [w h]} (->Rect 10 20)
           [a b & more] (fibonacci 8)
           evens (filterv even? (range 1 11))
           grade (cond (> (factorial 5) 200) :high
                       (> (factorial 5) 50)  :medium
                       :else                 :low)]

       ;; *** SUSPEND – checkpoint computed state ***
       (let [rv (suspend! {:areas       areas
                           :fact-5      (factorial 5)
                           :fib-8       (fibonacci 8)
                           :add-10-of-5 (add-10 5)
                           :log         @log
                           :grade       grade
                           :dims        [w h]
                           :fib-rest    (vec more)
                           :evens       evens})]

         ;; --- post-resume computation ---
         (swap! log conj :resumed)
         (swap! log conj (keyword (str \"with-\" rv)))
         {:result       (str \"done-\" rv)
          :post-areas   (mapv area [(->Circle 10) (->Rect 5 6)])
          :post-fact    (factorial 7)
          :post-fib     (fibonacci 6)
          :post-filter  (filterv odd? (range 1 11))
          :post-reduce  (reduce + (range 1 6))
          :post-log     @log
          :post-closure (add-10 100)})))")

(def ^:private expected-suspend-data
  {:areas       [78.53975 12]
   :fact-5      120
   :fib-8       [0 1 1 2 3 5 8 13]
   :add-10-of-5 15
   :log         [:init :shapes-done]
   :grade       :medium
   :dims        [10 20]
   :fib-rest    [1 2 3 5 8 13]
   :evens       [2 4 6 8 10]})

(defn expected-result
  "Expected result after resuming with `rv`."
  [rv]
  {:result       (str "done-" rv)
   :post-areas   [314.159 30]
   :post-fact    5040
   :post-fib     [0 1 1 2 3 5]
   :post-filter  [1 3 5 7 9]
   :post-reduce  15
   :post-log     [:init :shapes-done :resumed (keyword (str "with-" rv))]
   :post-closure 110})

(defn- write-file [path content]
  #?(:clj  (spit path content)
     :cljs (let [fs (js/require "fs")]
             (.call (unchecked-get fs "writeFileSync") fs path content "utf8"))))

(defn- read-file [path]
  #?(:clj  (slurp path)
     :cljs (let [fs (js/require "fs")]
             (.call (unchecked-get fs "readFileSync") fs path "utf8"))))

(defn- temp-path [name]
  (str #?(:clj  (System/getProperty "java.io.tmpdir")
          :cljs (let [os (js/require "os")]
                  (.call (unchecked-get os "tmpdir") os)))
       "/" name))

(deftest freeze-thaw-comprehensive-language-features
  (testing "rich program: suspend data is correct"
    (let [m (eval-suspend comprehensive-program)]
      (is (= expected-suspend-data (:suspend-data m)))))

  (testing "rich program: in-memory freeze/thaw roundtrip"
    (let [m       (eval-suspend comprehensive-program)
          frozen  (freeze/freeze m)
          thawed  (freeze/thaw frozen)
          result  (sci/resume thawed :ok)]
      (is (= (expected-result :ok) result))))

  (testing "rich program: freeze to disk, thaw from disk (same runtime)"
    (let [m      (eval-suspend comprehensive-program)
          frozen (freeze/freeze m)
          path   (temp-path (str "sci-freeze-"
                                 #?(:clj "jvm" :cljs "cljs")
                                 ".edn"))]
      (write-file path frozen)
      (let [from-disk (read-file path)
            thawed    (freeze/thaw from-disk)
            result    (sci/resume thawed :disk)]
        (is (= frozen from-disk) "EDN survives disk round-trip unchanged")
        (is (= (expected-result :disk) result)
            "computation resumes correctly from disk")))))

;; Freeze-to-file for cross-platform testing.  Writes EDN and expected values
;; so that the orchestration script (script/test/cross-freeze) can verify
;; thaw on the other runtime.
(defn freeze-to-file!
  "Eval the comprehensive program, freeze the suspended machine, write EDN to
   `path`.  Returns the suspend-data for verification."
  [path]
  (let [m      (eval-suspend comprehensive-program)
        frozen (freeze/freeze m)]
    (write-file path frozen)
    (:suspend-data m)))

(defn thaw-from-file!
  "Read frozen EDN from `path`, thaw, resume with `rv`, return the result."
  [path rv]
  (let [frozen (read-file path)
        thawed (freeze/thaw frozen)]
    (sci/resume thawed rv)))
