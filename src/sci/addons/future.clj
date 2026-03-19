(ns sci.addons.future
  "Future addon for SCI.")

(defn install
  "Install future support into a context."
  [opts]
  (merge opts {:allow-futures true}))
