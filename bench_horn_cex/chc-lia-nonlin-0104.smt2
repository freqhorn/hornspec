;; Original file: kind_883.smt2
(set-logic HORN)
(declare-fun greycounter_reset (Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun greycounter_step (Bool Bool Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun intloopcounter_reset (Int Bool Int Bool) Bool)
(declare-fun intloopcounter_step (Bool Bool Int Bool Int Bool) Bool)
(declare-fun top_reset (Bool Bool Bool Int Bool Bool Bool Bool Int Bool) Bool)
(declare-fun top_step
             (Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool)
             Bool)
(declare-fun INIT_STATE () Bool)
(declare-fun MAIN (Bool Bool Bool Int Bool Bool) Bool)

(assert (forall ((greycounter.__greycounter_2_m Bool)
         (greycounter.__greycounter_2_c Bool)
         (greycounter.__greycounter_3_m Bool)
         (greycounter.__greycounter_3_c Bool)
         (greycounter.ni_3._arrow._first_m Bool)
         (greycounter.ni_3._arrow._first_c Bool))
  (=> (and (= greycounter.__greycounter_2_m greycounter.__greycounter_2_c)
           (= greycounter.__greycounter_3_m greycounter.__greycounter_3_c)
           (= greycounter.ni_3._arrow._first_m true))
      (greycounter_reset
        greycounter.__greycounter_2_c
        greycounter.__greycounter_3_c
        greycounter.ni_3._arrow._first_c
        greycounter.__greycounter_2_m
        greycounter.__greycounter_3_m
        greycounter.ni_3._arrow._first_m))))
(assert (forall ((greycounter.ni_3._arrow._first_m Bool)
         (greycounter.ni_3._arrow._first_c Bool)
         (greycounter.__greycounter_1 Bool)
         (greycounter.ni_3._arrow._first_x Bool)
         (greycounter.b Bool)
         (greycounter.__greycounter_2_c Bool)
         (greycounter.a Bool)
         (greycounter.__greycounter_3_c Bool)
         (greycounter.out Bool)
         (greycounter.__greycounter_3_x Bool)
         (greycounter.__greycounter_2_x Bool)
         (greycounter.x Bool))
  (let ((a!1 (or (not (= greycounter.__greycounter_1 false))
                 (and (= greycounter.b greycounter.__greycounter_2_c)
                      (= greycounter.a (not greycounter.__greycounter_3_c))))))
  (let ((a!2 (and (= greycounter.ni_3._arrow._first_m
                     greycounter.ni_3._arrow._first_c)
                  (= greycounter.__greycounter_1
                     (ite greycounter.ni_3._arrow._first_m true false))
                  (= greycounter.ni_3._arrow._first_x false)
                  a!1
                  (or (not (= greycounter.__greycounter_1 true))
                      (and (= greycounter.b false) (= greycounter.a false)))
                  (= greycounter.out (and greycounter.a greycounter.b))
                  (= greycounter.__greycounter_3_x greycounter.b)
                  (= greycounter.__greycounter_2_x greycounter.a))))
    (=> a!2
        (greycounter_step greycounter.x
                          greycounter.out
                          greycounter.__greycounter_2_c
                          greycounter.__greycounter_3_c
                          greycounter.ni_3._arrow._first_c
                          greycounter.__greycounter_2_x
                          greycounter.__greycounter_3_x
                          greycounter.ni_3._arrow._first_x))))))
(assert (forall ((intloopcounter.__intloopcounter_2_m Int)
         (intloopcounter.__intloopcounter_2_c Int)
         (intloopcounter.ni_2._arrow._first_m Bool)
         (intloopcounter.ni_2._arrow._first_c Bool))
  (=> (and (= intloopcounter.__intloopcounter_2_m
              intloopcounter.__intloopcounter_2_c)
           (= intloopcounter.ni_2._arrow._first_m true))
      (intloopcounter_reset
        intloopcounter.__intloopcounter_2_c
        intloopcounter.ni_2._arrow._first_c
        intloopcounter.__intloopcounter_2_m
        intloopcounter.ni_2._arrow._first_m))))
(assert (forall ((intloopcounter.__intloopcounter_3 Bool)
         (intloopcounter.__intloopcounter_2_c Int)
         (intloopcounter.ni_2._arrow._first_m Bool)
         (intloopcounter.ni_2._arrow._first_c Bool)
         (intloopcounter.__intloopcounter_1 Bool)
         (intloopcounter.ni_2._arrow._first_x Bool)
         (intloopcounter.time Int)
         (intloopcounter.out Bool)
         (intloopcounter.__intloopcounter_2_x Int)
         (intloopcounter.x Bool))
  (let ((a!1 (or (not (= intloopcounter.__intloopcounter_3 false))
                 (= intloopcounter.time
                    (+ (- intloopcounter.__intloopcounter_2_c 1) 1)))))
  (let ((a!2 (and (or (not (= intloopcounter.__intloopcounter_3 true))
                      (= intloopcounter.time 0))
                  a!1)))
  (let ((a!3 (and (= intloopcounter.__intloopcounter_3
                     (= intloopcounter.__intloopcounter_2_c 3))
                  (= intloopcounter.ni_2._arrow._first_m
                     intloopcounter.ni_2._arrow._first_c)
                  (= intloopcounter.__intloopcounter_1
                     (ite intloopcounter.ni_2._arrow._first_m true false))
                  (= intloopcounter.ni_2._arrow._first_x false)
                  (or (not (= intloopcounter.__intloopcounter_1 true))
                      (= intloopcounter.time 0))
                  (or (not (= intloopcounter.__intloopcounter_1 false)) a!2)
                  (= intloopcounter.out (= intloopcounter.time 2))
                  (= intloopcounter.__intloopcounter_2_x intloopcounter.time))))
    (=> a!3
        (intloopcounter_step
          intloopcounter.x
          intloopcounter.out
          intloopcounter.__intloopcounter_2_c
          intloopcounter.ni_2._arrow._first_c
          intloopcounter.__intloopcounter_2_x
          intloopcounter.ni_2._arrow._first_x)))))))
(assert (forall ((top.ni_1.intloopcounter.__intloopcounter_2_c Int)
         (top.ni_1.intloopcounter.ni_2._arrow._first_c Bool)
         (top.ni_1.intloopcounter.__intloopcounter_2_m Int)
         (top.ni_1.intloopcounter.ni_2._arrow._first_m Bool)
         (top.ni_0.greycounter.__greycounter_2_c Bool)
         (top.ni_0.greycounter.__greycounter_3_c Bool)
         (top.ni_0.greycounter.ni_3._arrow._first_c Bool)
         (top.ni_0.greycounter.__greycounter_2_m Bool)
         (top.ni_0.greycounter.__greycounter_3_m Bool)
         (top.ni_0.greycounter.ni_3._arrow._first_m Bool))
  (=> (and (intloopcounter_reset
             top.ni_1.intloopcounter.__intloopcounter_2_c
             top.ni_1.intloopcounter.ni_2._arrow._first_c
             top.ni_1.intloopcounter.__intloopcounter_2_m
             top.ni_1.intloopcounter.ni_2._arrow._first_m)
           (greycounter_reset
             top.ni_0.greycounter.__greycounter_2_c
             top.ni_0.greycounter.__greycounter_3_c
             top.ni_0.greycounter.ni_3._arrow._first_c
             top.ni_0.greycounter.__greycounter_2_m
             top.ni_0.greycounter.__greycounter_3_m
             top.ni_0.greycounter.ni_3._arrow._first_m))
      (top_reset top.ni_0.greycounter.__greycounter_2_c
                 top.ni_0.greycounter.__greycounter_3_c
                 top.ni_0.greycounter.ni_3._arrow._first_c
                 top.ni_1.intloopcounter.__intloopcounter_2_c
                 top.ni_1.intloopcounter.ni_2._arrow._first_c
                 top.ni_0.greycounter.__greycounter_2_m
                 top.ni_0.greycounter.__greycounter_3_m
                 top.ni_0.greycounter.ni_3._arrow._first_m
                 top.ni_1.intloopcounter.__intloopcounter_2_m
                 top.ni_1.intloopcounter.ni_2._arrow._first_m))))
(assert (forall ((top.ni_1.intloopcounter.__intloopcounter_2_m Int)
         (top.ni_1.intloopcounter.__intloopcounter_2_c Int)
         (top.ni_1.intloopcounter.ni_2._arrow._first_m Bool)
         (top.ni_1.intloopcounter.ni_2._arrow._first_c Bool)
         (top.x Bool)
         (top.d Bool)
         (top.ni_1.intloopcounter.__intloopcounter_2_x Int)
         (top.ni_1.intloopcounter.ni_2._arrow._first_x Bool)
         (top.ni_0.greycounter.__greycounter_2_m Bool)
         (top.ni_0.greycounter.__greycounter_2_c Bool)
         (top.ni_0.greycounter.__greycounter_3_m Bool)
         (top.ni_0.greycounter.__greycounter_3_c Bool)
         (top.ni_0.greycounter.ni_3._arrow._first_m Bool)
         (top.ni_0.greycounter.ni_3._arrow._first_c Bool)
         (top.b Bool)
         (top.ni_0.greycounter.__greycounter_2_x Bool)
         (top.ni_0.greycounter.__greycounter_3_x Bool)
         (top.ni_0.greycounter.ni_3._arrow._first_x Bool)
         (top.OK Bool))
  (=> (and (= top.ni_1.intloopcounter.__intloopcounter_2_m
              top.ni_1.intloopcounter.__intloopcounter_2_c)
           (= top.ni_1.intloopcounter.ni_2._arrow._first_m
              top.ni_1.intloopcounter.ni_2._arrow._first_c)
           (intloopcounter_step
             top.x
             top.d
             top.ni_1.intloopcounter.__intloopcounter_2_m
             top.ni_1.intloopcounter.ni_2._arrow._first_m
             top.ni_1.intloopcounter.__intloopcounter_2_x
             top.ni_1.intloopcounter.ni_2._arrow._first_x)
           (= top.ni_0.greycounter.__greycounter_2_m
              top.ni_0.greycounter.__greycounter_2_c)
           (= top.ni_0.greycounter.__greycounter_3_m
              top.ni_0.greycounter.__greycounter_3_c)
           (= top.ni_0.greycounter.ni_3._arrow._first_m
              top.ni_0.greycounter.ni_3._arrow._first_c)
           (greycounter_step top.x
                             top.b
                             top.ni_0.greycounter.__greycounter_2_m
                             top.ni_0.greycounter.__greycounter_3_m
                             top.ni_0.greycounter.ni_3._arrow._first_m
                             top.ni_0.greycounter.__greycounter_2_x
                             top.ni_0.greycounter.__greycounter_3_x
                             top.ni_0.greycounter.ni_3._arrow._first_x)
           (= top.OK (= top.b top.d)))
      (top_step top.x
                top.OK
                top.ni_0.greycounter.__greycounter_2_c
                top.ni_0.greycounter.__greycounter_3_c
                top.ni_0.greycounter.ni_3._arrow._first_c
                top.ni_1.intloopcounter.__intloopcounter_2_c
                top.ni_1.intloopcounter.ni_2._arrow._first_c
                top.ni_0.greycounter.__greycounter_2_x
                top.ni_0.greycounter.__greycounter_3_x
                top.ni_0.greycounter.ni_3._arrow._first_x
                top.ni_1.intloopcounter.__intloopcounter_2_x
                top.ni_1.intloopcounter.ni_2._arrow._first_x))))
(assert (=> true INIT_STATE))
(assert (forall ((top.ni_0.greycounter.__greycounter_2_c Bool)
         (top.ni_0.greycounter.__greycounter_3_c Bool)
         (top.ni_0.greycounter.ni_3._arrow._first_c Bool)
         (top.ni_1.intloopcounter.__intloopcounter_2_c Int)
         (top.ni_1.intloopcounter.ni_2._arrow._first_c Bool)
         (top.ni_0.greycounter.__greycounter_2_m Bool)
         (top.ni_0.greycounter.__greycounter_3_m Bool)
         (top.ni_0.greycounter.ni_3._arrow._first_m Bool)
         (top.ni_1.intloopcounter.__intloopcounter_2_m Int)
         (top.ni_1.intloopcounter.ni_2._arrow._first_m Bool)
         (top.x Bool)
         (top.OK Bool)
         (top.ni_0.greycounter.__greycounter_2_x Bool)
         (top.ni_0.greycounter.__greycounter_3_x Bool)
         (top.ni_0.greycounter.ni_3._arrow._first_x Bool)
         (top.ni_1.intloopcounter.__intloopcounter_2_x Int)
         (top.ni_1.intloopcounter.ni_2._arrow._first_x Bool))
  (=> (and INIT_STATE
           (top_reset top.ni_0.greycounter.__greycounter_2_c
                      top.ni_0.greycounter.__greycounter_3_c
                      top.ni_0.greycounter.ni_3._arrow._first_c
                      top.ni_1.intloopcounter.__intloopcounter_2_c
                      top.ni_1.intloopcounter.ni_2._arrow._first_c
                      top.ni_0.greycounter.__greycounter_2_m
                      top.ni_0.greycounter.__greycounter_3_m
                      top.ni_0.greycounter.ni_3._arrow._first_m
                      top.ni_1.intloopcounter.__intloopcounter_2_m
                      top.ni_1.intloopcounter.ni_2._arrow._first_m)
           (top_step top.x
                     top.OK
                     top.ni_0.greycounter.__greycounter_2_m
                     top.ni_0.greycounter.__greycounter_3_m
                     top.ni_0.greycounter.ni_3._arrow._first_m
                     top.ni_1.intloopcounter.__intloopcounter_2_m
                     top.ni_1.intloopcounter.ni_2._arrow._first_m
                     top.ni_0.greycounter.__greycounter_2_x
                     top.ni_0.greycounter.__greycounter_3_x
                     top.ni_0.greycounter.ni_3._arrow._first_x
                     top.ni_1.intloopcounter.__intloopcounter_2_x
                     top.ni_1.intloopcounter.ni_2._arrow._first_x))
      (MAIN top.ni_0.greycounter.__greycounter_2_x
            top.ni_0.greycounter.__greycounter_3_x
            top.ni_0.greycounter.ni_3._arrow._first_x
            top.ni_1.intloopcounter.__intloopcounter_2_x
            top.ni_1.intloopcounter.ni_2._arrow._first_x
            top.OK))))
(assert (forall ((top.ni_0.greycounter.__greycounter_2_c Bool)
         (top.ni_0.greycounter.__greycounter_3_c Bool)
         (top.ni_0.greycounter.ni_3._arrow._first_c Bool)
         (top.ni_1.intloopcounter.__intloopcounter_2_c Int)
         (top.ni_1.intloopcounter.ni_2._arrow._first_c Bool)
         (dummytop.OK Bool)
         (top.x Bool)
         (top.OK Bool)
         (top.ni_0.greycounter.__greycounter_2_x Bool)
         (top.ni_0.greycounter.__greycounter_3_x Bool)
         (top.ni_0.greycounter.ni_3._arrow._first_x Bool)
         (top.ni_1.intloopcounter.__intloopcounter_2_x Int)
         (top.ni_1.intloopcounter.ni_2._arrow._first_x Bool))
  (=> (and (MAIN top.ni_0.greycounter.__greycounter_2_c
                 top.ni_0.greycounter.__greycounter_3_c
                 top.ni_0.greycounter.ni_3._arrow._first_c
                 top.ni_1.intloopcounter.__intloopcounter_2_c
                 top.ni_1.intloopcounter.ni_2._arrow._first_c
                 dummytop.OK)
           (top_step top.x
                     top.OK
                     top.ni_0.greycounter.__greycounter_2_c
                     top.ni_0.greycounter.__greycounter_3_c
                     top.ni_0.greycounter.ni_3._arrow._first_c
                     top.ni_1.intloopcounter.__intloopcounter_2_c
                     top.ni_1.intloopcounter.ni_2._arrow._first_c
                     top.ni_0.greycounter.__greycounter_2_x
                     top.ni_0.greycounter.__greycounter_3_x
                     top.ni_0.greycounter.ni_3._arrow._first_x
                     top.ni_1.intloopcounter.__intloopcounter_2_x
                     top.ni_1.intloopcounter.ni_2._arrow._first_x))
      (MAIN top.ni_0.greycounter.__greycounter_2_x
            top.ni_0.greycounter.__greycounter_3_x
            top.ni_0.greycounter.ni_3._arrow._first_x
            top.ni_1.intloopcounter.__intloopcounter_2_x
            top.ni_1.intloopcounter.ni_2._arrow._first_x
            top.OK))))
(assert (forall ((top.OK Bool)
         (top.ni_0.greycounter.__greycounter_2_x Bool)
         (top.ni_0.greycounter.__greycounter_3_x Bool)
         (top.ni_0.greycounter.ni_3._arrow._first_x Bool)
         (top.ni_1.intloopcounter.__intloopcounter_2_x Int)
         (top.ni_1.intloopcounter.ni_2._arrow._first_x Bool)
         (ERR Bool))
  (=> (and (not top.OK)
           (MAIN top.ni_0.greycounter.__greycounter_2_x
                 top.ni_0.greycounter.__greycounter_3_x
                 top.ni_0.greycounter.ni_3._arrow._first_x
                 top.ni_1.intloopcounter.__intloopcounter_2_x
                 top.ni_1.intloopcounter.ni_2._arrow._first_x
                 top.OK))
      false)))
(check-sat)
