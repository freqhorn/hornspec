(declare-rel f (Int))
(declare-rel g (Int))

(declare-var x Int)
(declare-var y Int)

(declare-rel fail ())

(rule (=> (= x 20) (f x)))
(rule (=> (and (f x) (= y (- x 1))) (f y)))
(rule (=> (and (f x) (g y) (not (>= y x))) fail))

(query fail)
