(declare-var a (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var n Int)
(declare-var x Int)

(declare-rel inv ((Array Int Int) Int Int Int))
(declare-rel fail ())

(rule (inv a 0 x n))

(rule (=> (and (inv a i x n) (< i n) (not (= (select a i) x)) (= i1 (+ i 1))) (inv a i1 x n)))

(rule (=> (and (inv a i x n) (or (not (< i n)) (= (select a i) x))
  (and (>= i1 0) (< i1 i)) (= (select a i1) x)) fail))

(query fail)
