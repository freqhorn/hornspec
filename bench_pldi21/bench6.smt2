(declare-rel f (Int Int))
(declare-rel g (Int))

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)
(declare-var x1 Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (and (= x 0) (= y 0)) (f x y)))
(rule (=> (and (f x y) (= x1 (+ x 1)) (= y1 (+ y x))) (f x1 y1)))
(rule (=> (and (f x y) (g z) (not (>= y z))) fail))

(query fail)
