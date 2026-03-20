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
