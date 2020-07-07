(declare-rel inv ((Array Int Int)))
(declare-var a (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-rel fail ())

(rule (inv (store (store (store (store a 0 0) 1 0) 2 0) 3 0)))

(rule (=> 
  (and
    (inv a)
    (= a1 (store
      (store
        (store
          (store a 0 (+ 1 (select a 0)))
        1 (+ (select a 0) (select a 1)))
      2 (+ (select a 1) (select a 2)))
    3 (+ (select a 2) (select a 3)))))
  (inv a1)))

(rule (=> (and (inv a) (not (>= (select a 3) 0))) fail))

(query fail)

