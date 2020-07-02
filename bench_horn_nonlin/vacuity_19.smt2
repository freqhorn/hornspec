(declare-rel f (Int Int))
(declare-rel g (Int))

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var x1 Int)
(declare-var y1 Int)


(declare-rel fail ())

(rule (=> (and (= x 13) (= y 42)) (f x y)))
(rule (=> (and (f x y) (= x1 (- x y)) (= y1 (+ y 1))) (f x1 y1)))
(rule (=> (and (f x z) (g y) (not (>= y x))) fail))

(query fail)
