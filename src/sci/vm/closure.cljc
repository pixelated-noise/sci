(ns sci.vm.closure
  "Makes VM closures callable by host functions.")

(defn make-callable-closure
  "Wrap a closure map in an IFn so host code can call it."
  [closure-map apply-fn]
  (let [f (fn closure-wrapper [& args]
            (apply-fn closure-map args))]
    (with-meta f {:sci/closure closure-map})))
