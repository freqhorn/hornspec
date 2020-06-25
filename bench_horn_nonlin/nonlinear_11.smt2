(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))
(declare-var a Int)
(declare-var a1 Int)

(declare-rel fail ())

(rule (=> (= a 11) (f a)))
(rule (=> (and (f a) (= a1 (- a 2))) (f a1)))
(rule (=> (< a 12) (g a)))
(rule (=> (and (> a 9) (f a) (g a)) (h a)))
(rule (=> (and (h a) (= a1 (+ a 2))) (h a1)))
(rule (=> (and (h a) (= a 12)) fail))

(query fail)
