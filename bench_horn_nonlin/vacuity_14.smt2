(declare-rel f (Int))

(declare-var x Int)
(declare-var x1 Int)

(declare-rel fail ())

(rule (=> (and (f x) (= x1 (+ x 2))) (f x1)))
(rule (=> (and (f x) (f (+ x 1))) fail))

(query fail)
