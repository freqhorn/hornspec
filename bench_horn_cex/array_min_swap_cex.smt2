(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j Int)

(declare-rel inv ((Array Int Int) Int Int))
(declare-rel fail ())

(rule (inv a j j))

(rule (=> (and (inv a i j)
      (= a1 (ite
          (< (select a i) (select a j))
          (store (store a i (select a j)) j (select a i))
          a))
      (= i1 (+ i 1)))
  (inv a1 i1 j)))

(rule (=> (and (inv a i j) (< j i1) (< i1 i) (not (< (select a j) (select a i1)))) fail))

(query fail)
