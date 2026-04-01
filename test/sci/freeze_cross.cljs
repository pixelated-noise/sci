(ns sci.freeze-cross
  "CLI entry point for cross-platform freeze/thaw testing.
   Compiled to Node.js, invoked by script/test/cross-freeze."
  (:require [sci.freeze-test :as ft]))

(defn -main [& args]
  (let [[cmd path rv] args]
    (case cmd
      "freeze" (let [data (ft/freeze-to-file! path)]
                 (println "FREEZE_OK"))
      "thaw-verify"
      (let [result (ft/thaw-from-file! path (keyword rv))
            expected (ft/expected-result (keyword rv))]
        (if (= expected result)
          (println "THAW_VERIFY_PASS")
          (do (println "THAW_VERIFY_FAIL")
              (println "expected:" (pr-str expected))
              (println "actual:  " (pr-str result)))))
      (do (println "Usage: freeze|thaw-verify <path> [resume-value]")
          (.exit js/process 1)))))

(set! *main-cli-fn* -main)
