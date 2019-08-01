;; Original file: pow_inc.smt2
(set-logic HORN)
;(declare-fun P4 (Int Int Int) Bool) ; replaced to true
(declare-fun P3 (Int Int Int) Bool)
(declare-fun P1 (Int Int) Bool)
(declare-fun P9 (Int Int) Bool)
(declare-fun P0 (Int) Bool)
; (declare-fun P2 (Int Int) Bool)   ; replaced to true
; (declare-fun P10 (Int Int) Bool)  ; replaced to true
; (declare-fun P11 (Int Int Int) Bool)  ; replaced to true
(declare-fun P5 (Int Int Int Int) Bool)
; (declare-fun P6 (Int) Bool)  ; replaced to true
; (declare-fun P7 (Int) Bool)  ; replaced to true
; (declare-fun P8 (Int Int) Bool) ; simply eliminated
(declare-fun P12 (Int Int Int Int) Bool)

(assert (forall ((x1 Int) (x0 Int)) (=> (= x0 (+ 1 x1)) (P9 x1 x0))))
(assert (forall ((x0 Int) (x1 Int) (x2 Int) (x3 Int)) (=> (P9 x2 x3) (P12 x0 x1 x2 x3))))
(assert (forall ((x1 Int) (x4 Int) (x5 Int) (x0 Int) (x3 Int) (x2 Int)) (=> (P12 x2 x3 x4 x5) (P3 x1 x4 x5))))
(assert (forall ((x3 Int) (x4 Int) (x0 Int) (x2 Int) (x1 Int)) (=> (and  (P12 x1 x2 x3 x4) ) (P1 x3 x4))))
(assert (forall ((x1 Int) (x0 Int) (x2 Int) (x4 Int) (x3 Int)) (=> (and  (P3 x1 x2 x3) (P1 x3 x4)) (P5 x1 x0 x2 x4))))
(assert (forall ((x1 Int) (x2 Int) (x5 Int) (x6 Int) (x0 Int) (x3 Int) (x4 Int)) (=> (P5 x3 x4 x5 x6) (P12 x1 x2 x5 x6))))

(assert (forall ((x3 Int) (x2 Int) (x0 Int) (x1 Int)) (=> (and (P12 x0 x1 x2 x3) (>= x2 (+ 1 x3))) false)))
(check-sat)
;(get-model)
