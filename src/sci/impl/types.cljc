(ns sci.impl.types
  "SCI type definitions."
  (:refer-clojure :exclude [eval]))

#?(:clj
   (definterface ICustomType
     (getInterfaces [])
     (getMethods [])
     (getProtocols [])
     (getFields [])))

(defprotocol HasName
  (getName [this]))

(deftype ConstantNode [val]
  #?@(:clj [Object
             (toString [_] (str val))]
      :cljs [IPrintWithWriter
             (-pr-writer [_ writer _] (-write writer (str val)))]))

#?(:cljs
   (defrecord NodeR [f]))

(defn eval
  "Evaluate a type node."
  [node]
  (if (instance? ConstantNode node)
    (.-val node)
    node))

#?(:clj
   (do
     (defn getInterfaces [^ICustomType x]
       (.getInterfaces x))
     (defn getMethods [^ICustomType x]
       (.getMethods x))
     (defn getProtocols [^ICustomType x]
       (.getProtocols x))
     (defn getFields [^ICustomType x]
       (.getFields x))))
