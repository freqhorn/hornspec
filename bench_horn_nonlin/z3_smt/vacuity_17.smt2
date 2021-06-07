(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))

(assert (forall ((x Int)) (=> (<= x 5) (f x))))
(assert (forall ((x Int)) (=> (<= x 7) (g x))))

(assert (forall ((x Int) (y Int) (z Int)) (=> (and (f x) (g y) (h z) ) (<= (+ x y) z))))

(assert (exists ((x Int) (y Int) (z Int)) (and (f x) (g y) (h z))))

(check-sat)
(get-model)
