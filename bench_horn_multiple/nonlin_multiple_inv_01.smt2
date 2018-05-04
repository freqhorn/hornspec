(declare-rel PRE (Int))
(declare-rel POST (Int))
(declare-var m Int)
(declare-var m1 Int)

(declare-rel fail ())

(rule (=> (= m 1) (PRE m)))

(rule (=> (and (PRE m) (= m1 (+ m m))) (PRE m1)))

(rule (=> (PRE m) (POST m)))

(rule (=> (and (POST m) (= m1 (* m m))) (POST m1)))

(rule (=> (and (POST m) (not (>= m 1))) fail))

(query fail)
