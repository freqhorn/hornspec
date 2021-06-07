(declare-rel f (Int))
(declare-rel g (Int))


(assert (forall ((x Int)) (=> (= x 20) (f x))))
(assert (forall ((x Int) (y Int)) (=> (and (f x) (= y (- x 1))) (f y))))
(assert (forall ((x Int) (y Int)) (=> (and (f x) (g y)) (>= y x))))

(assert (exists ((x Int) (y Int)) (and (f x) (g y))))
	
(check-sat)
(get-model)

