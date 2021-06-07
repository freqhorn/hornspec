(declare-rel f (Int))
(declare-rel g (Int))


(assert (forall ((x Int)) (=> (= x 134) (f x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (f x) (= x1 (+ x 1))) (f x1))))
(assert (forall ((x Int) (y Int) (x1 Int)) (=> (and (g x) (f y) (= x1 (ite (< y 65) 52 87))) (g x1))))
(assert (forall ((x Int) (y Int)) (=> (and (g x) (g y)) (= x y))))

(assert (exists ((x Int) (y Int) (x1 Int)) (and (g x) (f y))))
(assert (exists ((x Int) (y Int) (x1 Int)) (and (g x) (g y))))
		
(check-sat)
(get-model)

