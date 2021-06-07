(declare-rel f (Int Int))


(assert (forall ((x Int) (b Int) (x1 Int)) (=> (and (f x b) (>= x 0) (= x1 (ite (= b 1) (- x) x))) (>= x1 0))))

(assert (exists ((x Int) (b Int)) (f x b)))

(check-sat)
(get-model)

