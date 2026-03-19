(ns sci.impl.analyzer
  "Analyzer stub — for the VM, analysis is done inline during step.")

(defn analyze
  "Analyze a form. In the VM implementation, this is mostly a no-op
   since analysis happens during stepping."
  [ctx form]
  form)
