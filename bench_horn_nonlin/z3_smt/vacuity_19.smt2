(declare-rel f (Int Int))
(declare-rel g (Int))

(assert (forall ((x Int) (y Int)) (=> (and (= x 13) (= y 42)) (f x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int)) (=> (and (f x y) (= x1 (- x y)) (= y1 (+ y 1))) (f x1 y1))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (f x z) (g y)) (>= y x))))

(assert (exists ((x Int) (y Int) (z Int)) (and (f x z) (g y))))

(check-sat)
(get-model)

