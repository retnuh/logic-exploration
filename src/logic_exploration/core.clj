(ns logic_exploration.core
  (:refer-clojure :exclude [==])
  (:use clojure.core.logic))


(run* [q]
  (fresh [x y z]
    (== q [x y z])
    (appendo [1 2 x 5 y] z [1 2 3 5 y 9 10 11 15])))

(macroexpand '(defne righto [x y l]
                ([_ _ [x y . ?r]])
                ([_ _ [_ . ?r]] (righto x y ?r))))

(defn righto [x y l]
  (conde
    ((fresh [?r]
       (== (llist x y ?r) l)))
    ((fresh [?r]
       (== (llist (clojure.core.logic/lvar) ?r) l)
       (righto x y ?r)))))

(macroexpand '(defne membero
  "A relation where l is a collection, such that l contains x"
  [x   l]
  ([_ [x . tail]])
  ([_ [head . tail]]
    (membero x tail))))

(defne appendo
  "A relation where x, y, and z are proper collections,
such that z is x appended to y"
  [x y z]
  ([() _ y])
  ([[a . d] _ [a . r]] (appendo d y r)))
