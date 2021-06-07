(declare-rel f (Int Int))
(declare-rel g (Int))

(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (f x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int)) (=> (and (f x y) (= x1 (+ x 1)) (= y1 (+ y x))) (f x1 y1))))

(assert (forall ((x Int) (y Int) (z Int)) (=> (and (f x y) (g z)) (>= y z))))

(assert (exists ((x Int) (y Int) (z Int)) (and (f x y) (g z))))

(check-sat)
(get-model)
