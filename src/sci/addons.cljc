(ns sci.addons
  "SCI addons.")

(defn future
  "Install future support into a context."
  [opts]
  (merge opts {:allow-futures true}))
