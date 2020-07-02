(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)

(declare-rel fail ())

(rule (=> (= x 20) (f x)))
(rule (=> (and (f x) (h z) (= y (+ x z))) (f y)))
(rule (=> (and (f x) (g y) (not (>= y x))) fail))

(query fail)
