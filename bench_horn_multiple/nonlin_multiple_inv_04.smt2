(declare-rel PRE (Int Int))
(declare-rel POST (Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)

(declare-rel fail ())

(rule (=> (and (> i 0) (> j 0)) (PRE i j)))

(rule (=> (and (PRE i j) (= i1 (+ i 1)) (= j1 (+ j 1))) (PRE i1 j1)))

(rule (=> (and (PRE i j) (= i1 (* i j))) (POST i1 j)))

(rule (=> (and (POST i j) (= i1 (- i 1)) (= j1 (- j 1))) (POST i1 j1)))

(rule (=> (and (POST i j) (not (>= i j))) fail))

(query fail)

