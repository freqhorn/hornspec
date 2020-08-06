(declare-rel inv1 (Int Int))
(declare-rel inv2 (Int Int))
(declare-var x Int)
(declare-var y Int)

(declare-rel fail ())

(rule (=> (and (= x 1) (= y 5)) (inv1 x y)))
(rule (=> (and (= x 2) (= y 5)) (inv1 x y)))
(rule (=> (and (= x 3) (= y 7)) (inv2 x y)))
(rule (=> (and (= x 1) (= y 7)) (inv2 x y)))
(rule (=> (and (inv1 x 5) (inv2 x 7)) fail))

(query fail)

