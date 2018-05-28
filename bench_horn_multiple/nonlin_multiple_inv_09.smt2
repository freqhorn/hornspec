(declare-rel PRE (Int))
(declare-rel POST (Int Int))
(declare-var m Int)
(declare-var m1 Int)
(declare-var n Int)
(declare-var n1 Int)

(declare-rel fail ())

(rule (=> (< m 0) (PRE m)))

(rule (=> (and (PRE m) (= m1 (- m 1))) (PRE m1)))

(rule (=> (PRE m) (POST m m)))

(rule (=> (and (POST m n) (= m1 (* m n)) (= n1 (+ n 1))) (POST m1 n1)))

(rule (=> (and (POST m n) (> n 0) (not (= m 0))) fail))

(query fail)
