(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))


(assert (forall ((x Int) (y Int)) (=> (and (h x) (h y)) (f (+ x y)))))
(assert (forall ((x Int) (y Int)) (=> (and (h x) (h y)) (g (+ x y)))))
(assert (forall ((x Int) (y Int)) (=> (and (f x) (g y)) (>= (+ x y) -100))))

(assert (exists ((x Int) (y Int)) (and (h x) (h y))))

(check-sat)
(get-model)
