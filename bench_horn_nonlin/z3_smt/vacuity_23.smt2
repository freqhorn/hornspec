(declare-rel f (Int))
(declare-rel g (Int))

(assert (forall ((x Int)) (=> (= x -10) (g x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (f x) (= x1 (+ x 1))) (f x1)))) 
(assert (forall ((x Int) (y Int)) (=> (and (f x) (g y)) (> x y))))

(assert (exists ((x Int) (y Int)) (and (f x) (g y))))

(check-sat)
(get-model)
