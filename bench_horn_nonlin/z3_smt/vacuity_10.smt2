(declare-rel f (Int))
(declare-rel g (Int))

(assert (forall ((x Int) (x1 Int)) (=> (and (f x) (= x1 (+ x 1))) (f x1))))
(assert (forall ((x Int) (x1 Int)) (=> (and (g x) (= x1 (- x 1))) (g x1))))
(assert (forall ((x Int) (y Int) (z Int) (w Int)) (=> (and (g x) (g y) (f z) (f w)) (< (+ x y) (+ z w)))))

(assert (exists ((x Int) (y Int) (z Int) (w Int)) (and (g x) (g y) (f z) (f w))))

(check-sat)
(get-model)
