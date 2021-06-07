(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))

(assert (forall ((x Int)) (=> (= x 20) (f x))))
(assert (forall ((x Int) (y Int) (z Int)) (=> (and (f x) (h z) (= y (+ x z))) (f y))))
(assert (forall ((x Int) (y Int)) (=> (and (f x) (g y)) (>= y x))))

(assert (exists ((x Int) (y Int)) (and (f x) (g y))))
(assert (exists ((x Int) (y Int)) (and (f x) (h y))))


(check-sat)
(get-model)

