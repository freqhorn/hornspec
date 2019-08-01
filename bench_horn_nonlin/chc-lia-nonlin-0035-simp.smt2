(set-logic HORN)
(declare-fun P0 (Int Int Int) Bool)
(declare-fun P1 (Int) Bool)
(declare-fun P2 (Int Int) Bool)

(assert (forall ((x0 Int)) (=> (= x0 0) (P1 x0))))
(assert (forall ((x0 Int) (x1 Int)) (=> (and (= x0 0) (= x1 50)) (P2 x0 x1))))

(assert (forall ((x0 Int) (x1 Int) (x2 Int)) (=> (and (P1 x1) (P2 x1 x2) (<= x1 49) (= x0 (+ 1 x1))) (P1 x0))))
(assert (forall ((x0 Int) (x2 Int) (x1 Int)) (=> (and (P1 x1) (P2 x1 x2) (<= x1 49) (= x0 (+ 1 x1))) (P2 x0 x2))))

(assert (forall ((x1 Int) (x2 Int) (x0 Int) (x3 Int)) (=> (and (P1 x2) (P2 x2 x3) (<= 50 x2) (<= x2 99)                 (= x1 (+ 1 x2))) (P1 x1))))
(assert (forall ((x0 Int) (x1 Int) (x2 Int) (x3 Int)) (=> (and (P1 x2) (P2 x2 x3) (<= 50 x2) (<= x2 99) (= x0 (+ 1 x2)) (= x1 (+ 1 x3))) (P2 x0 x1))))

(assert (forall ((x2 Int) (x0 Int) (x1 Int) (x3 Int))
    (=> (and (P1 x2) (P2 x2 x3)
      (>= x2 100)
      (> x3 100)
) false)))


(check-sat)
