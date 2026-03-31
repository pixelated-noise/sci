(ns sci.test-runner-utils
  "Utilities for running and diagnosing SCI tests interactively from the REPL.

   Key functions:
   - (run-ns 'sci.core-test)            — run all tests in a namespace, report summary
   - (run-ns 'sci.core-test :timeout 5) — with per-test timeout in seconds
   - (find-slow 'sci.core-test)         — find tests taking >1s
   - (find-hanging 'sci.core-test)      — find tests that hang (timeout)
   - (run-test 'sci.core-test/core-test) — run a single test by qualified name
   - (run-all)                           — run all SCI test namespaces
   - (bisect-hanging 'sci.core-test)    — binary search for the hanging test"
  (:require [clojure.test :as t]
            [clojure.string :as str]
            [sci.vm.step]))

;; ============================================================
;; Internals
;; ============================================================

(defn- test-ns-syms
  "Return all SCI test namespace symbols."
  []
  '[sci.core-test
    sci.vars-test
    sci.namespaces-test
    sci.error-test
    sci.interop-test
    sci.multimethods-test
    sci.protocols-test
    sci.io-test
    sci.read-test
    sci.parse-test
    sci.freeze-test
    sci.hierarchies-test
    sci.repl-test])

(defn- reload-sci-deps!
  "Reload SCI implementation namespaces in dependency order to avoid
   classloader identity issues (sci.lang.Var from DynamicClassLoader)."
  []
  (doseq [ns-sym '[sci.lang sci.impl.types sci.vm.step sci.core]]
    (when (find-ns ns-sym)
      (require ns-sym :reload))))

(defn- require-ns [ns-sym]
  (reload-sci-deps!)
  (try
    (require ns-sym :reload)
    true
    (catch Exception e
      (println "  ERROR requiring" ns-sym "-" (ex-message e))
      false)))

(defn- test-vars-in-ns
  "Return all test vars in a namespace, sorted by name."
  [ns-sym]
  (when (require-ns ns-sym)
    (->> (ns-publics (the-ns ns-sym))
         vals
         (filter #(:test (meta %)))
         (sort-by #(:name (meta %))))))

(defn- run-var-with-timeout
  "Run a single test var with a timeout (in seconds).
   Returns {:name :status :elapsed-ms :failures :errors}
   Status is :pass, :fail, :error, or :timeout."
  [v timeout-sec]
  (let [var-name (-> v meta :name)
        counters (ref t/*initial-report-counters*)
        start (System/nanoTime)
        fut (future
              (binding [t/*report-counters* counters
                        t/*testing-vars* []
                        sci.vm.step/*max-steps* 1000000]
                (try
                  (t/test-var v)
                  (catch Throwable e
                    (dosync (alter counters update :error inc))))))
        result (deref fut (* timeout-sec 1000) ::timeout)
        elapsed (/ (- (System/nanoTime) start) 1e6)]
    (when (= result ::timeout)
      (future-cancel fut))
    (let [c @counters]
      {:name    var-name
       :status  (cond
                  (= result ::timeout) :timeout
                  (pos? (:error c))    :error
                  (pos? (:fail c))     :fail
                  :else                :pass)
       :elapsed-ms (long elapsed)
       :pass   (:pass c 0)
       :fail   (:fail c 0)
       :error  (:error c 0)})))

;; ============================================================
;; Public API
;; ============================================================

(defn run-test
  "Run a single test by qualified symbol, e.g. 'sci.core-test/core-test.
   Options:
     :timeout  — seconds before killing (default 10)
     :verbose  — print full test output (default true)"
  [qualified-sym & {:keys [timeout verbose] :or {timeout 10 verbose true}}]
  (let [ns-sym (symbol (namespace qualified-sym))
        test-name (symbol (name qualified-sym))]
    (require-ns ns-sym)
    (if-let [v (resolve qualified-sym)]
      (let [result (binding [t/*test-out* (if verbose *out* (java.io.StringWriter.))]
                     (run-var-with-timeout v timeout))]
        (println (format "%-40s %6dms  %s"
                         (:name result)
                         (:elapsed-ms result)
                         (name (:status result))))
        result)
      (println "Not found:" qualified-sym))))

(defn run-ns
  "Run all tests in a namespace with per-test timeout.
   Options:
     :timeout  — seconds per test (default 10)
     :verbose  — print each test's output (default false)
     :only     — set of test name symbols to include

   Returns {:passed N :failed N :errored N :timed-out N :results [...]}"
  [ns-sym & {:keys [timeout verbose only] :or {timeout 10 verbose false}}]
  (println (str "=== " ns-sym " ==="))
  (if-let [vars (test-vars-in-ns ns-sym)]
    (let [vars (if only
                 (filter #(contains? only (-> % meta :name)) vars)
                 vars)
          results (mapv (fn [v]
                          (let [r (binding [t/*test-out* (if verbose *out* (java.io.StringWriter.))]
                                    (run-var-with-timeout v timeout))]
                            (let [icon (case (:status r)
                                         :pass "."
                                         :fail "F"
                                         :error "E"
                                         :timeout "T")]
                              (print icon)
                              (flush))
                            r))
                        vars)
          summary {:passed    (count (filter #(= :pass (:status %)) results))
                   :failed    (count (filter #(= :fail (:status %)) results))
                   :errored   (count (filter #(= :error (:status %)) results))
                   :timed-out (count (filter #(= :timeout (:status %)) results))
                   :results   results}]
      (println)
      (println (format "  %d passed, %d failed, %d errors, %d timeouts  (of %d tests)"
                       (:passed summary) (:failed summary)
                       (:errored summary) (:timed-out summary)
                       (count results)))
      ;; Print details for non-passing tests
      (doseq [r results
              :when (not= :pass (:status r))]
        (println (format "  %-6s %-35s %6dms"
                         (str/upper-case (name (:status r)))
                         (:name r)
                         (:elapsed-ms r))))
      summary)
    (do (println "  (no tests found)")
        {:passed 0 :failed 0 :errored 0 :timed-out 0 :results []})))

(defn find-slow
  "Find tests in a namespace that take longer than threshold-ms.
   Default threshold: 1000ms."
  [ns-sym & {:keys [threshold timeout] :or {threshold 1000 timeout 30}}]
  (println (str "Finding slow tests in " ns-sym " (threshold: " threshold "ms)..."))
  (when-let [vars (test-vars-in-ns ns-sym)]
    (let [results (mapv (fn [v]
                          (binding [t/*test-out* (java.io.StringWriter.)]
                            (run-var-with-timeout v timeout)))
                        vars)
          slow (filter #(> (:elapsed-ms %) threshold) results)]
      (if (seq slow)
        (do (println (str "  Found " (count slow) " slow test(s):"))
            (doseq [r (sort-by :elapsed-ms > slow)]
              (println (format "  %-35s %6dms  %s"
                               (:name r)
                               (:elapsed-ms r)
                               (name (:status r)))))
            slow)
        (do (println "  No slow tests found.")
            [])))))

(defn find-hanging
  "Find tests that hang (exceed timeout). Default timeout: 5s."
  [ns-sym & {:keys [timeout] :or {timeout 5}}]
  (println (str "Finding hanging tests in " ns-sym " (timeout: " timeout "s)..."))
  (when-let [vars (test-vars-in-ns ns-sym)]
    (let [hanging (atom [])]
      (doseq [v vars]
        (let [vname (-> v meta :name)
              r (binding [t/*test-out* (java.io.StringWriter.)]
                  (run-var-with-timeout v timeout))]
          (print (if (= :timeout (:status r)) "T" "."))
          (flush)
          (when (= :timeout (:status r))
            (swap! hanging conj vname))))
      (println)
      (if (seq @hanging)
        (do (println (str "  Found " (count @hanging) " hanging test(s):"))
            (doseq [n @hanging]
              (println "  " n))
            @hanging)
        (do (println "  No hanging tests found.")
            [])))))

(defn bisect-hanging
  "Binary search for a hanging test in a namespace.
   Runs halves of the test list to narrow down which test hangs.
   Returns the name of the hanging test, or nil."
  [ns-sym & {:keys [timeout] :or {timeout 5}}]
  (println (str "Bisecting " ns-sym " for hanging tests (timeout: " timeout "s)..."))
  (when-let [vars (test-vars-in-ns ns-sym)]
    (loop [candidates (vec vars)]
      (let [n (count candidates)]
        (cond
          (zero? n)
          (do (println "  No hanging test found.") nil)

          (= 1 n)
          (let [v (first candidates)
                vname (-> v meta :name)
                r (binding [t/*test-out* (java.io.StringWriter.)]
                    (run-var-with-timeout v timeout))]
            (if (= :timeout (:status r))
              (do (println (str "  Found hanging test: " vname))
                  vname)
              (do (println (str "  " vname " passed (" (:elapsed-ms r) "ms) — hang may be from test interaction"))
                  nil)))

          :else
          (let [mid (quot n 2)
                first-half (subvec candidates 0 mid)
                second-half (subvec candidates mid)]
            (println (str "  Testing first half (" (count first-half) " tests)..."))
            (let [hangs-first? (some (fn [v]
                                      (let [r (binding [t/*test-out* (java.io.StringWriter.)]
                                                (run-var-with-timeout v timeout))]
                                        (= :timeout (:status r))))
                                    first-half)]
              (if hangs-first?
                (do (println "  → Hang in first half")
                    (recur first-half))
                (do (println "  Testing second half (" (count second-half) " tests)...")
                    (let [hangs-second? (some (fn [v]
                                               (let [r (binding [t/*test-out* (java.io.StringWriter.)]
                                                          (run-var-with-timeout v timeout))]
                                                 (= :timeout (:status r))))
                                             second-half)]
                      (if hangs-second?
                        (do (println "  → Hang in second half")
                            (recur second-half))
                        (do (println "  Neither half hangs — may be test interaction")
                            nil))))))))))))

(defn run-all
  "Run all SCI test namespaces. Returns summary map.
   Options:
     :timeout  — seconds per test (default 10)
     :skip     — set of namespace symbols to skip"
  [& {:keys [timeout skip] :or {timeout 10 skip #{}}}]
  (let [namespaces (remove skip (test-ns-syms))
        all-results (atom [])]
    (doseq [ns-sym namespaces]
      (let [r (run-ns ns-sym :timeout timeout)]
        (swap! all-results conj (assoc r :ns ns-sym))))
    (println "\n=== SUMMARY ===")
    (let [totals (reduce (fn [acc r]
                           (-> acc
                               (update :passed + (:passed r))
                               (update :failed + (:failed r))
                               (update :errored + (:errored r))
                               (update :timed-out + (:timed-out r))))
                         {:passed 0 :failed 0 :errored 0 :timed-out 0}
                         @all-results)]
      (println (format "Total: %d passed, %d failed, %d errors, %d timeouts"
                       (:passed totals) (:failed totals)
                       (:errored totals) (:timed-out totals)))
      (doseq [r @all-results
              :when (or (pos? (:failed r)) (pos? (:errored r)) (pos? (:timed-out r)))]
        (println (format "  %-30s %dp %df %de %dt"
                         (:ns r) (:passed r) (:failed r) (:errored r) (:timed-out r))))
      totals)))
