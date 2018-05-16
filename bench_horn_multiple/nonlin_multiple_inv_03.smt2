(declare-rel PRE (Int Int Int))
(declare-rel POST (Int Int Int Int))
(declare-var m Int)
(declare-var m1 Int)
(declare-var n Int)
(declare-var n1 Int)
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)

(declare-rel fail ())

(rule (=> (> n 0) (PRE n 0 0)))

(rule (=> (and (PRE n i j) (> n 0)
    (= n1 (- n 1))
    (or
        (and (= i1 (+ i 1)) (= j1 j))
        (and (= i1 i) (= j1 (+ j 1)))))
  (PRE n1 i1 j1)))

(rule (=> (and (PRE n i j) (= n 0)) (POST 0 0 i j)))

(rule (=> (and (POST m n i j) (= m1 (+ m j)) (= n1 (+ n 1)) ) (POST m1 n1 i j)))

(rule (=> (and (POST m n i j) (not (= (* n j) m))) fail))

(query fail)
