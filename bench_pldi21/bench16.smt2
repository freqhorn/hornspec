(declare-rel f (Int))
(declare-rel g (Int))
(declare-rel h (Int))

(declare-var x Int)
(declare-var y Int)
(declare-var z Int)

(declare-rel fail ())

(rule (=> (<= x 5) (f x)))
(rule (=> (<= x 7) (g x)))

(rule (=> (and (f x) (g y) (h z) (not (<= (+ x y) z))) fail))

(query fail)
