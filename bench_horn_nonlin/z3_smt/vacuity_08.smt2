(declare-rel f (Int Int))
(declare-rel g (Int))
(declare-rel h (Int Int))

(assert (forall ((z Int)) (=> (g z) (g (* 2 z)))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int)) (=> (and (f x y) (h x1 x) (= y1 (+ y x))) (f x1 y1))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (f x y) (g z)) (>= y (* 2 z)))))

(assert (exists ((x Int) (y Int) (z Int)) (and (f x y) (g z))))

(assert (exists ((x Int) (y Int) (x1 Int) (y1 Int)) (and (f x y) (h x1 x))))


(check-sat)
(get-model)

