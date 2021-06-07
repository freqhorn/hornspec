(declare-rel f (Int))
(declare-rel g (Int Int))
(declare-rel h (Int))


(assert (forall ((x Int)) (=> (< x 0) (h x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (f x) (= x1 (+ x 1))) (f x1))))
(assert (forall ((x Int) (y Int)) (=> (and (f x) (h y)) (g x y))))
(assert (forall ((x Int) (y Int)) (=> (g x y) (not (= x y)))))

(assert (exists ((x Int) (y Int)) (and (f x) (h y))))

(check-sat)
(get-model)

