(declare-rel inv1 (Int Int))
(declare-rel inv2 (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (and (= x 0) (= y 0)) (inv1 x y)))

(rule (=> (and (inv1 x y) (= y1 (+ y 1)) (= x1 (+ x 1))) (inv2 x1 y1)))

(rule (=> (and (inv2 x y) (= y1 (+ y 1)) (= x1 (- x 2))) (inv1 x1 y1)))

(rule (=> (and (inv1 x y) (= y 100) (not (= x 100))) fail))

(query fail)
