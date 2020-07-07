(declare-rel inv ((Array Int Int) Int Int Int Int))
(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var c1 Int)
(declare-var c2 Int)
(declare-var c3 Int)
(declare-var c4 Int)
(declare-rel fail ())

(rule (inv (store (store (store (store a c1 0) c2 0) c3 0) c4 0) c1 c2 c3 c4))

(rule (=> 
  (and
    (inv a c1 c2 c3 c4)
    (= a1 (store
      (store
        (store
          (store a c1 (+ 1 (select a c1)))
        c2 (+ (select a c1) (select a c2)))
      c3 (+ (select a c2) (select a c3)))
    c4 (+ (select a c3) (select a c4)))))
  (inv a1 c1 c2 c3 c4)))

(rule (=> (and (inv a c1 c2 c3 c4) (not (>= (select a c4) 0))) fail))

(query fail)

