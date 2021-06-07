(declare-rel f (Int))
(declare-rel g (Int))

(declare-var x Int)

(declare-rel fail ())

(rule (=> (< x 0) (f x)))
(rule (=> (and (f x) (g x) (not (>= x 0))) fail))

(query fail)
