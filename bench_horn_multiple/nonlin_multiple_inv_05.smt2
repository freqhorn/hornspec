(declare-rel PRE (Int Int))
(declare-rel POST (Int Int))
(declare-var m Int)
(declare-var m1 Int)
(declare-var n Int)
(declare-var n1 Int)

(declare-rel fail ())

(rule (=> (and (> m 0) (> n 0)) (PRE m n)))

(rule (=> (and (PRE m n) (> m 1) (= m1 (- m 1)) (= n1 (* m1 n))) (PRE m1 n1)))

(rule (=> (and (PRE m n) (= m 1) (= m1 (- m 2)) (= n1 (* m1 n))) (POST m1 n1)))

(rule (=> (and (POST m n) (= m1 (+ m 2)) (= n1 (* m1 n))) (POST m1 n1)))

(rule (=> (and (POST m n) (not (< n 0))) fail))

(query fail)
