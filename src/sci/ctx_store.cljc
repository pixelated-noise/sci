(ns sci.ctx-store
  "Context store — thread-local SCI context storage.")

(def ^:dynamic *ctx* nil)

(defmacro with-ctx [ctx & body]
  `(binding [*ctx* ~ctx]
     ~@body))

(defn get-ctx []
  *ctx*)
