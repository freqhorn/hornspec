;; Original file: kind_481.smt2
(set-logic HORN)
(declare-fun bool6_reset (Bool Bool Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun bool6_step
             (Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool)
             Bool)
(declare-fun int6I_reset (Int Bool Int Bool) Bool)
(declare-fun int6I_step (Bool Bool Int Bool Int Bool) Bool)
(declare-fun top_reset
             (Int Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Bool)
             Bool)
(declare-fun top_step
             (Bool
              Bool
              Int
              Bool
              Bool
              Bool
              Bool
              Bool
              Int
              Bool
              Bool
              Bool
              Bool
              Bool)
             Bool)
(declare-fun INIT_STATE () Bool)
(declare-fun MAIN (Int Bool Bool Bool Bool Bool Bool) Bool)

(assert (forall ((bool6.__bool6_2_m Bool)
         (bool6.__bool6_2_c Bool)
         (bool6.__bool6_3_m Bool)
         (bool6.__bool6_3_c Bool)
         (bool6.__bool6_4_m Bool)
         (bool6.__bool6_4_c Bool)
         (bool6.ni_3._arrow._first_m Bool)
         (bool6.ni_3._arrow._first_c Bool))
  (=> (and (= bool6.__bool6_2_m bool6.__bool6_2_c)
           (= bool6.__bool6_3_m bool6.__bool6_3_c)
           (= bool6.__bool6_4_m bool6.__bool6_4_c)
           (= bool6.ni_3._arrow._first_m true))
      (bool6_reset bool6.__bool6_2_c
                   bool6.__bool6_3_c
                   bool6.__bool6_4_c
                   bool6.ni_3._arrow._first_c
                   bool6.__bool6_2_m
                   bool6.__bool6_3_m
                   bool6.__bool6_4_m
                   bool6.ni_3._arrow._first_m))))
(assert (forall ((bool6.ni_3._arrow._first_m Bool)
         (bool6.ni_3._arrow._first_c Bool)
         (bool6.__bool6_1 Bool)
         (bool6.ni_3._arrow._first_x Bool)
         (bool6.c Bool)
         (bool6.__bool6_4_c Bool)
         (bool6.__bool6_2_c Bool)
         (bool6.__bool6_3_c Bool)
         (bool6.a Bool)
         (bool6.out Bool)
         (bool6.b Bool)
         (bool6.__bool6_4_x Bool)
         (bool6.__bool6_3_x Bool)
         (bool6.__bool6_2_x Bool)
         (bool6.x Bool))
  (let ((a!1 (and (= bool6.c
                     (and bool6.__bool6_4_c
                          (not bool6.__bool6_2_c)
                          bool6.__bool6_3_c
                          bool6.__bool6_2_c))
                  (= bool6.a (not bool6.__bool6_2_c))))
        (a!2 (= bool6.b
                (or (and (not bool6.__bool6_4_c)
                         (not bool6.__bool6_3_c)
                         bool6.__bool6_2_c)
                    (and bool6.__bool6_3_c (not bool6.__bool6_2_c))))))
  (let ((a!3 (and (= bool6.ni_3._arrow._first_m bool6.ni_3._arrow._first_c)
                  (= bool6.__bool6_1
                     (ite bool6.ni_3._arrow._first_m true false))
                  (= bool6.ni_3._arrow._first_x false)
                  (or (not (= bool6.__bool6_1 false)) a!1)
                  (or (not (= bool6.__bool6_1 true))
                      (and (= bool6.c false) (= bool6.a false)))
                  (= bool6.out (and bool6.a bool6.c))
                  (or (not (= bool6.__bool6_1 true)) (= bool6.b false))
                  (or (not (= bool6.__bool6_1 false)) a!2)
                  (= bool6.__bool6_4_x bool6.c)
                  (= bool6.__bool6_3_x bool6.b)
                  (= bool6.__bool6_2_x bool6.a))))
    (=> a!3
        (bool6_step bool6.x
                    bool6.out
                    bool6.__bool6_2_c
                    bool6.__bool6_3_c
                    bool6.__bool6_4_c
                    bool6.ni_3._arrow._first_c
                    bool6.__bool6_2_x
                    bool6.__bool6_3_x
                    bool6.__bool6_4_x
                    bool6.ni_3._arrow._first_x))))))
(assert (forall ((int6I.__int6I_2_m Int)
         (int6I.__int6I_2_c Int)
         (int6I.ni_2._arrow._first_m Bool)
         (int6I.ni_2._arrow._first_c Bool))
  (=> (and (= int6I.__int6I_2_m int6I.__int6I_2_c)
           (= int6I.ni_2._arrow._first_m true))
      (int6I_reset int6I.__int6I_2_c
                   int6I.ni_2._arrow._first_c
                   int6I.__int6I_2_m
                   int6I.ni_2._arrow._first_m))))
(assert (forall ((int6I.__int6I_3 Bool)
         (int6I.__int6I_2_c Int)
         (int6I.ni_2._arrow._first_m Bool)
         (int6I.ni_2._arrow._first_c Bool)
         (int6I.__int6I_1 Bool)
         (int6I.ni_2._arrow._first_x Bool)
         (int6I.time Int)
         (int6I.out Bool)
         (int6I.__int6I_2_x Int)
         (int6I.x Bool))
  (let ((a!1 (and (or (not (= int6I.__int6I_3 true)) (= int6I.time 1))
                  (or (not (= int6I.__int6I_3 false))
                      (= int6I.time (- int6I.__int6I_2_c 1))))))
  (let ((a!2 (and (= int6I.__int6I_3 (= int6I.__int6I_2_c 5))
                  (= int6I.ni_2._arrow._first_m int6I.ni_2._arrow._first_c)
                  (= int6I.__int6I_1
                     (ite int6I.ni_2._arrow._first_m true false))
                  (= int6I.ni_2._arrow._first_x false)
                  (or (not (= int6I.__int6I_1 true)) (= int6I.time 0))
                  (or (not (= int6I.__int6I_1 false)) a!1)
                  (= int6I.out (= int6I.time 5))
                  (= int6I.__int6I_2_x int6I.time))))
    (=> a!2
        (int6I_step int6I.x
                    int6I.out
                    int6I.__int6I_2_c
                    int6I.ni_2._arrow._first_c
                    int6I.__int6I_2_x
                    int6I.ni_2._arrow._first_x))))))
(assert (forall ((top.ni_1.bool6.__bool6_2_c Bool)
         (top.ni_1.bool6.__bool6_3_c Bool)
         (top.ni_1.bool6.__bool6_4_c Bool)
         (top.ni_1.bool6.ni_3._arrow._first_c Bool)
         (top.ni_1.bool6.__bool6_2_m Bool)
         (top.ni_1.bool6.__bool6_3_m Bool)
         (top.ni_1.bool6.__bool6_4_m Bool)
         (top.ni_1.bool6.ni_3._arrow._first_m Bool)
         (top.ni_0.int6I.__int6I_2_c Int)
         (top.ni_0.int6I.ni_2._arrow._first_c Bool)
         (top.ni_0.int6I.__int6I_2_m Int)
         (top.ni_0.int6I.ni_2._arrow._first_m Bool))
  (=> (and (bool6_reset top.ni_1.bool6.__bool6_2_c
                        top.ni_1.bool6.__bool6_3_c
                        top.ni_1.bool6.__bool6_4_c
                        top.ni_1.bool6.ni_3._arrow._first_c
                        top.ni_1.bool6.__bool6_2_m
                        top.ni_1.bool6.__bool6_3_m
                        top.ni_1.bool6.__bool6_4_m
                        top.ni_1.bool6.ni_3._arrow._first_m)
           (int6I_reset top.ni_0.int6I.__int6I_2_c
                        top.ni_0.int6I.ni_2._arrow._first_c
                        top.ni_0.int6I.__int6I_2_m
                        top.ni_0.int6I.ni_2._arrow._first_m))
      (top_reset top.ni_0.int6I.__int6I_2_c
                 top.ni_0.int6I.ni_2._arrow._first_c
                 top.ni_1.bool6.__bool6_2_c
                 top.ni_1.bool6.__bool6_3_c
                 top.ni_1.bool6.__bool6_4_c
                 top.ni_1.bool6.ni_3._arrow._first_c
                 top.ni_0.int6I.__int6I_2_m
                 top.ni_0.int6I.ni_2._arrow._first_m
                 top.ni_1.bool6.__bool6_2_m
                 top.ni_1.bool6.__bool6_3_m
                 top.ni_1.bool6.__bool6_4_m
                 top.ni_1.bool6.ni_3._arrow._first_m))))
(assert (forall ((top.ni_1.bool6.__bool6_2_m Bool)
         (top.ni_1.bool6.__bool6_2_c Bool)
         (top.ni_1.bool6.__bool6_3_m Bool)
         (top.ni_1.bool6.__bool6_3_c Bool)
         (top.ni_1.bool6.__bool6_4_m Bool)
         (top.ni_1.bool6.__bool6_4_c Bool)
         (top.ni_1.bool6.ni_3._arrow._first_m Bool)
         (top.ni_1.bool6.ni_3._arrow._first_c Bool)
         (top.x Bool)
         (top.b Bool)
         (top.ni_1.bool6.__bool6_2_x Bool)
         (top.ni_1.bool6.__bool6_3_x Bool)
         (top.ni_1.bool6.__bool6_4_x Bool)
         (top.ni_1.bool6.ni_3._arrow._first_x Bool)
         (top.ni_0.int6I.__int6I_2_m Int)
         (top.ni_0.int6I.__int6I_2_c Int)
         (top.ni_0.int6I.ni_2._arrow._first_m Bool)
         (top.ni_0.int6I.ni_2._arrow._first_c Bool)
         (top.a Bool)
         (top.ni_0.int6I.__int6I_2_x Int)
         (top.ni_0.int6I.ni_2._arrow._first_x Bool)
         (top.OK Bool))
  (=> (and (= top.ni_1.bool6.__bool6_2_m top.ni_1.bool6.__bool6_2_c)
           (= top.ni_1.bool6.__bool6_3_m top.ni_1.bool6.__bool6_3_c)
           (= top.ni_1.bool6.__bool6_4_m top.ni_1.bool6.__bool6_4_c)
           (= top.ni_1.bool6.ni_3._arrow._first_m
              top.ni_1.bool6.ni_3._arrow._first_c)
           (bool6_step top.x
                       top.b
                       top.ni_1.bool6.__bool6_2_m
                       top.ni_1.bool6.__bool6_3_m
                       top.ni_1.bool6.__bool6_4_m
                       top.ni_1.bool6.ni_3._arrow._first_m
                       top.ni_1.bool6.__bool6_2_x
                       top.ni_1.bool6.__bool6_3_x
                       top.ni_1.bool6.__bool6_4_x
                       top.ni_1.bool6.ni_3._arrow._first_x)
           (= top.ni_0.int6I.__int6I_2_m top.ni_0.int6I.__int6I_2_c)
           (= top.ni_0.int6I.ni_2._arrow._first_m
              top.ni_0.int6I.ni_2._arrow._first_c)
           (int6I_step top.x
                       top.a
                       top.ni_0.int6I.__int6I_2_m
                       top.ni_0.int6I.ni_2._arrow._first_m
                       top.ni_0.int6I.__int6I_2_x
                       top.ni_0.int6I.ni_2._arrow._first_x)
           (= top.OK (= top.a top.b)))
      (top_step top.x
                top.OK
                top.ni_0.int6I.__int6I_2_c
                top.ni_0.int6I.ni_2._arrow._first_c
                top.ni_1.bool6.__bool6_2_c
                top.ni_1.bool6.__bool6_3_c
                top.ni_1.bool6.__bool6_4_c
                top.ni_1.bool6.ni_3._arrow._first_c
                top.ni_0.int6I.__int6I_2_x
                top.ni_0.int6I.ni_2._arrow._first_x
                top.ni_1.bool6.__bool6_2_x
                top.ni_1.bool6.__bool6_3_x
                top.ni_1.bool6.__bool6_4_x
                top.ni_1.bool6.ni_3._arrow._first_x))))
(assert (=> true INIT_STATE))
(assert (forall ((top.ni_0.int6I.__int6I_2_c Int)
         (top.ni_0.int6I.ni_2._arrow._first_c Bool)
         (top.ni_1.bool6.__bool6_2_c Bool)
         (top.ni_1.bool6.__bool6_3_c Bool)
         (top.ni_1.bool6.__bool6_4_c Bool)
         (top.ni_1.bool6.ni_3._arrow._first_c Bool)
         (top.ni_0.int6I.__int6I_2_m Int)
         (top.ni_0.int6I.ni_2._arrow._first_m Bool)
         (top.ni_1.bool6.__bool6_2_m Bool)
         (top.ni_1.bool6.__bool6_3_m Bool)
         (top.ni_1.bool6.__bool6_4_m Bool)
         (top.ni_1.bool6.ni_3._arrow._first_m Bool)
         (top.x Bool)
         (top.OK Bool)
         (top.ni_0.int6I.__int6I_2_x Int)
         (top.ni_0.int6I.ni_2._arrow._first_x Bool)
         (top.ni_1.bool6.__bool6_2_x Bool)
         (top.ni_1.bool6.__bool6_3_x Bool)
         (top.ni_1.bool6.__bool6_4_x Bool)
         (top.ni_1.bool6.ni_3._arrow._first_x Bool))
  (=> (and INIT_STATE
           (top_reset top.ni_0.int6I.__int6I_2_c
                      top.ni_0.int6I.ni_2._arrow._first_c
                      top.ni_1.bool6.__bool6_2_c
                      top.ni_1.bool6.__bool6_3_c
                      top.ni_1.bool6.__bool6_4_c
                      top.ni_1.bool6.ni_3._arrow._first_c
                      top.ni_0.int6I.__int6I_2_m
                      top.ni_0.int6I.ni_2._arrow._first_m
                      top.ni_1.bool6.__bool6_2_m
                      top.ni_1.bool6.__bool6_3_m
                      top.ni_1.bool6.__bool6_4_m
                      top.ni_1.bool6.ni_3._arrow._first_m)
           (top_step top.x
                     top.OK
                     top.ni_0.int6I.__int6I_2_m
                     top.ni_0.int6I.ni_2._arrow._first_m
                     top.ni_1.bool6.__bool6_2_m
                     top.ni_1.bool6.__bool6_3_m
                     top.ni_1.bool6.__bool6_4_m
                     top.ni_1.bool6.ni_3._arrow._first_m
                     top.ni_0.int6I.__int6I_2_x
                     top.ni_0.int6I.ni_2._arrow._first_x
                     top.ni_1.bool6.__bool6_2_x
                     top.ni_1.bool6.__bool6_3_x
                     top.ni_1.bool6.__bool6_4_x
                     top.ni_1.bool6.ni_3._arrow._first_x))
      (MAIN top.ni_0.int6I.__int6I_2_x
            top.ni_0.int6I.ni_2._arrow._first_x
            top.ni_1.bool6.__bool6_2_x
            top.ni_1.bool6.__bool6_3_x
            top.ni_1.bool6.__bool6_4_x
            top.ni_1.bool6.ni_3._arrow._first_x
            top.OK))))
(assert (forall ((top.ni_0.int6I.__int6I_2_c Int)
         (top.ni_0.int6I.ni_2._arrow._first_c Bool)
         (top.ni_1.bool6.__bool6_2_c Bool)
         (top.ni_1.bool6.__bool6_3_c Bool)
         (top.ni_1.bool6.__bool6_4_c Bool)
         (top.ni_1.bool6.ni_3._arrow._first_c Bool)
         (dummytop.OK Bool)
         (top.x Bool)
         (top.OK Bool)
         (top.ni_0.int6I.__int6I_2_x Int)
         (top.ni_0.int6I.ni_2._arrow._first_x Bool)
         (top.ni_1.bool6.__bool6_2_x Bool)
         (top.ni_1.bool6.__bool6_3_x Bool)
         (top.ni_1.bool6.__bool6_4_x Bool)
         (top.ni_1.bool6.ni_3._arrow._first_x Bool))
  (=> (and (MAIN top.ni_0.int6I.__int6I_2_c
                 top.ni_0.int6I.ni_2._arrow._first_c
                 top.ni_1.bool6.__bool6_2_c
                 top.ni_1.bool6.__bool6_3_c
                 top.ni_1.bool6.__bool6_4_c
                 top.ni_1.bool6.ni_3._arrow._first_c
                 dummytop.OK)
           (top_step top.x
                     top.OK
                     top.ni_0.int6I.__int6I_2_c
                     top.ni_0.int6I.ni_2._arrow._first_c
                     top.ni_1.bool6.__bool6_2_c
                     top.ni_1.bool6.__bool6_3_c
                     top.ni_1.bool6.__bool6_4_c
                     top.ni_1.bool6.ni_3._arrow._first_c
                     top.ni_0.int6I.__int6I_2_x
                     top.ni_0.int6I.ni_2._arrow._first_x
                     top.ni_1.bool6.__bool6_2_x
                     top.ni_1.bool6.__bool6_3_x
                     top.ni_1.bool6.__bool6_4_x
                     top.ni_1.bool6.ni_3._arrow._first_x))
      (MAIN top.ni_0.int6I.__int6I_2_x
            top.ni_0.int6I.ni_2._arrow._first_x
            top.ni_1.bool6.__bool6_2_x
            top.ni_1.bool6.__bool6_3_x
            top.ni_1.bool6.__bool6_4_x
            top.ni_1.bool6.ni_3._arrow._first_x
            top.OK))))
(assert (forall ((top.OK Bool)
         (top.ni_0.int6I.__int6I_2_x Int)
         (top.ni_0.int6I.ni_2._arrow._first_x Bool)
         (top.ni_1.bool6.__bool6_2_x Bool)
         (top.ni_1.bool6.__bool6_3_x Bool)
         (top.ni_1.bool6.__bool6_4_x Bool)
         (top.ni_1.bool6.ni_3._arrow._first_x Bool)
         (ERR Bool))
  (=> (and (not top.OK)
           (MAIN top.ni_0.int6I.__int6I_2_x
                 top.ni_0.int6I.ni_2._arrow._first_x
                 top.ni_1.bool6.__bool6_2_x
                 top.ni_1.bool6.__bool6_3_x
                 top.ni_1.bool6.__bool6_4_x
                 top.ni_1.bool6.ni_3._arrow._first_x
                 top.OK))
      false)))
(check-sat)
