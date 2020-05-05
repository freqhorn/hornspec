(declare-rel f (Int))
(declare-rel g (Int))

(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (= x 134) (f x)))
(rule (=> (and (f x) (= x1 (+ x 1))) (f x1)))
(rule (=> (and (g x) (f y) (= x1 (ite (< y 65) 52 87))) (g x1)))
(rule (=> (and (g x) (g y) (not (= x y))) fail))

(query fail)
