(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var N Int)

(declare-rel inv ((Array Int Int) Int Int))
(declare-rel fail ())

(rule (inv a 0 100000))

(rule (=> (and (inv a i N) (<= i N) (= a1 (store (store a (* 2 i) 0) (+ (* 2 i) 1) 0)) (= i1 (+ i 1))) (inv a1 i1 N)))

(rule (=> (and (inv a i N) (> i N) (<= 0 i1) (<= i1 (* N 2)) (not (>= (select a i1) 0))) fail))

(query fail)
