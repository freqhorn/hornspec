(declare-rel INV1 (Int Int))
(declare-rel INV2 (Int Int))
(declare-var a Int)
(declare-var a1 Int)
(declare-var b Int)
(declare-var b1 Int)

(declare-rel fail ())

(rule (=> (= 0 (* a b)) (INV1 a b)))

(rule (=> (and (INV1 a b) (> a 0) (= a1 (- a 1))) (INV1 a1 b)))

(rule (=> (and (INV1 a b) (<= a 0)) (INV2 a b)))

(rule (=> (and (INV2 a b) (< b 0) (= b1 (+ b 1))) (INV2 a b1)))

(rule (=> (and (INV2 a b) (>= b 0) (not (= (* a b) 0))) fail))

(query fail)
