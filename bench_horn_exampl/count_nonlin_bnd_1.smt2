(declare-rel inv1 (Int Int))
(declare-rel inv2 (Int Int))
(declare-var x Int)
(declare-var x1 Int)
(declare-var y Int)
(declare-var y1 Int)

(declare-rel fail ())

(rule (=> (and (<= x 0) (= y 0)) (inv1 x y)))

(rule (=> 
    (and 
	      (inv1 x y)
        (> x1 0)
        (= x1 (+ x 1))
        (= y1 (+ y 1)))
    (inv1 x1 y1)))

(rule (=> (and (<= x 0) (= y 0)) (inv2 x y)))

(rule (=>
    (and
        (inv2 x y)
        (> x1 0)
        (= x1 (+ x 1))
        (= y1 (- y 1)))
    (inv2 x1 y1)))

(rule (=> (and (inv1 40 y) (inv2 20 y1) (not (= y (- 20 y1)))) fail))

(query fail)
