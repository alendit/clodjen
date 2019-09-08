(ns clodjen.utils)

(defn extract-arg-meta [func]
  (let [arg-vars (first (:arglists (meta func)))]
    (into {} (for [arg arg-vars] [arg (meta arg)]))))
