(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var b1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)
(declare-var j1 Int)
(declare-var n Int)

(declare-rel inv ((Array Int Int) (Array Int Int) Int Int Int))
(declare-rel fail ())

(rule (inv a b 0 0 n))

(rule (=> (and (inv a b i j n)
  (< i n)
  (= i1 (+ i 1))
  (= b1 (ite (>= (select a i) 0) (store b j (select a i)) b))
  (= j1 (ite (>= (select a i) 0) (+ j 1) j)))
    (inv a b1 i1 j1 n)))

(rule (=> (and (inv a b i j n) (not (< i n))
  (not (forall ((j1 Int)) (=> (and (>= j1 0) (< j1 j))
    (exists ((i2 Int)) (= (select b j1) (select a i2))))))) fail))

(query fail)
