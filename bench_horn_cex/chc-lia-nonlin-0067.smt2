;; Original file: kind_479.smt2
(set-logic HORN)
(declare-fun top_reset (Int Bool Int Bool) Bool)
(declare-fun top_step (Int Bool Int Bool Int Bool) Bool)
(declare-fun INIT_STATE () Bool)
(declare-fun MAIN (Int Bool Bool) Bool)

(assert (forall ((top.__top_2_m Int)
         (top.__top_2_c Int)
         (top.ni_0._arrow._first_m Bool)
         (top.ni_0._arrow._first_c Bool))
  (=> (and (= top.__top_2_m top.__top_2_c) (= top.ni_0._arrow._first_m true))
      (top_reset top.__top_2_c
                 top.ni_0._arrow._first_c
                 top.__top_2_m
                 top.ni_0._arrow._first_m))))
(assert (forall ((top.__top_3 Bool)
         (top.__top_2_c Int)
         (top.ni_0._arrow._first_m Bool)
         (top.ni_0._arrow._first_c Bool)
         (top.__top_1 Bool)
         (top.ni_0._arrow._first_x Bool)
         (top.time Int)
         (top.__top_2_x Int)
         (top.OK Bool)
         (top.init Int))
  (let ((a!1 (and (or (not (= top.__top_3 true)) (= top.time 0))
                  (or (not (= top.__top_3 false))
                      (= top.time (+ top.__top_2_c 1))))))
  (let ((a!2 (and (= top.__top_3 (= top.__top_2_c 5))
                  (= top.ni_0._arrow._first_m top.ni_0._arrow._first_c)
                  (= top.__top_1 (ite top.ni_0._arrow._first_m true false))
                  (= top.ni_0._arrow._first_x false)
                  (or (not (= top.__top_1 true)) (= top.time 0))
                  (or (not (= top.__top_1 false)) a!1)
                  (= top.__top_2_x top.time)
                  (= top.OK (< top.time 0)))))
    (=> a!2
        (top_step top.init
                  top.OK
                  top.__top_2_c
                  top.ni_0._arrow._first_c
                  top.__top_2_x
                  top.ni_0._arrow._first_x))))))
(assert (=> true INIT_STATE))
(assert (forall ((top.__top_2_c Int)
         (top.ni_0._arrow._first_c Bool)
         (top.__top_2_m Int)
         (top.ni_0._arrow._first_m Bool)
         (top.init Int)
         (top.OK Bool)
         (top.__top_2_x Int)
         (top.ni_0._arrow._first_x Bool))
  (=> (and INIT_STATE
           (top_reset top.__top_2_c
                      top.ni_0._arrow._first_c
                      top.__top_2_m
                      top.ni_0._arrow._first_m)
           (top_step top.init
                     top.OK
                     top.__top_2_m
                     top.ni_0._arrow._first_m
                     top.__top_2_x
                     top.ni_0._arrow._first_x))
      (MAIN top.__top_2_x top.ni_0._arrow._first_x top.OK))))
(assert (forall ((top.__top_2_c Int)
         (top.ni_0._arrow._first_c Bool)
         (dummytop.OK Bool)
         (top.init Int)
         (top.OK Bool)
         (top.__top_2_x Int)
         (top.ni_0._arrow._first_x Bool))
  (=> (and (MAIN top.__top_2_c top.ni_0._arrow._first_c dummytop.OK)
           (top_step top.init
                     top.OK
                     top.__top_2_c
                     top.ni_0._arrow._first_c
                     top.__top_2_x
                     top.ni_0._arrow._first_x))
      (MAIN top.__top_2_x top.ni_0._arrow._first_x top.OK))))
(assert (forall ((top.OK Bool)
         (top.__top_2_x Int)
         (top.ni_0._arrow._first_x Bool)
         (ERR Bool))
  (=> (and (not top.OK) (MAIN top.__top_2_x top.ni_0._arrow._first_x top.OK))
      false)))
(check-sat)
