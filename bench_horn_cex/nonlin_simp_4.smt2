(declare-rel inv1 (Int Int))
(declare-rel inv2 (Int Int))
(declare-var x Int)
(declare-var y Int)
(declare-var x1 Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (and (= x 0) (= y 0)) (inv1 x y)))
(rule (=> (and (inv1 x y) (< x 2)) (inv1 (+ x 1) (+ y 1))))
(rule (=> (and (inv1 x y) (>= x 2)) (inv1 (+ x 1) (- y 1))))

(rule (=> (and (= x 4) (= y 4)) (inv2 x y)))
(rule (=> (and (inv2 x y) (< x 2)) (inv2 (- x 1) (+ y 1))))
(rule (=> (and (inv2 x y) (>= x 2)) (inv2 (- x 1) (- y 1))))

(rule (=> (and (inv1 x y) (inv2 x1 y1) (> (- y1 y) 4)) fail))

(query fail)
