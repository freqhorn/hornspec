(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))
(declare-rel k (Int))
(declare-rel l (Int))


(assert (forall ((x Int)) (=> (= x -1) (k x))))
(assert (forall ((x Int) (y Int)) (=> (and (k x) (h y)) (f (+ x y)))))
(assert (forall ((x Int) (y Int)) (=> (and (l x) (h y)) (g (+ x y)))))
(assert (forall ((x Int) (y Int)) (=> (and (f x) (g y)) (>= (+ x y) -2))))

(assert (exists ((x Int) (y Int)) (and (k x) (h y))))
(assert (exists ((x Int) (y Int)) (and (l x) (h y))))

(check-sat)
(get-model)

