(declare-rel inv1 (Int Int))
(declare-rel inv2 (Int Int))
(declare-var x Int)
(declare-var y Int)

(declare-rel fail ())

(rule (=> (and (= x -5) (= y 0)) (inv1 x y)))
(rule (=> (inv1 x y) (inv1 (+ x 1) (+ y 1))))
(rule (=> (and (>= x 0) (= y 7)) (inv2 x y)))
(rule (=> (and (inv1 x y) (inv2 x y) (= y 7)) fail))

(query fail)

