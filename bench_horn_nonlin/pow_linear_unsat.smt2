(declare-rel ImportInt (Int Int Int Int))
(declare-rel Exp2 (Int Int))
(declare-rel fail ())
(declare-rel Bad ())
(declare-var pow Int)
(declare-var prev_pow Int)
(declare-var out Int)
(declare-var prev_out Int)
(declare-var r Int)
(declare-var log_r Int)
(declare-var modulus Int)
(declare-var r_mod_modulus Int)
(declare-var n Int)

(rule (=> (= pow 0) (Exp2 pow 1)))
(rule (=> (and (> pow 0) (= prev_pow (- pow 1)) (Exp2 prev_pow prev_out) (= out (* 2 prev_out))) (Exp2 pow out)))

(rule (=>
  (and (Exp2 log_r r) (= r_mod_modulus (mod r modulus)) (= out (mod (* (mod n modulus) r_mod_modulus) modulus)))
  (ImportInt n log_r modulus out))) 

(rule (=> (and (ImportInt 20 10 997 out) (not (= out 540))) fail))

(query fail)
