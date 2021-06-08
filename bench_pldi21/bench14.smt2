(declare-rel f (Int Int))

(declare-var x Int)
(declare-var x1 Int)
(declare-var b Int)

(declare-rel fail ())

; to continue

(rule (=> (and (f x b) (>= x 0) (= x1 (ite (= b 1) (- x) x)) (not (>= x1 0))) fail))

(query fail)

;
; unsat
;  (define-fun f ((x Int) (b Bool)) Bool
;  (or (not b) (< x 0) (>= (ite b (- x) x) 0)))
;
; (>= (ite b (- x) x) 0)  <=>  b = (<= x 0)
;

;
; (define-fun f ((x Int) (b Int)) Bool
;   (or (< x 0) (and (or (distinct b 1) (<= x 0)) (or (= b 1) (>= x 0)))))
;
;             <==>            ite (b = 1, x <= 0, x >= 0)
;
;
