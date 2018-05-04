(declare-rel PRE (Int))
(declare-rel POST (Int Int Int))
(declare-var m Int)
(declare-var m1 Int)
(declare-var n Int)
(declare-var i Int)
(declare-var i1 Int)

(declare-rel fail ())

(rule (=> (> m 0) (PRE m)))

(rule (=> (PRE m) (PRE m))) ; very stupid

(rule (=> (PRE m) (POST m m 1)))

(rule (=> (and (POST m n i) (= m1 (+ m n)) (= i1 (+ i 1))) (POST m1 n i1)))

(rule (=> (and (POST m n i) (not (= (* i n) m))) fail))

(query fail)
