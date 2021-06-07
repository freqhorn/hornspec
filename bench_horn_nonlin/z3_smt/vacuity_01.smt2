(declare-rel f (Int))
(declare-rel g (Int))

(assert (forall ((x Int)) (=> (< x 0) (f x))))
(assert (forall ((x Int)) (=> (and (f x) (g x)) (>= x 0))))
(assert (exists ((x Int)) (and (f x) (g x))))

(check-sat)
(get-model)
