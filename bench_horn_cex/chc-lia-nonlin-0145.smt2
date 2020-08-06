;; Original file: kind_533.smt2
(set-logic HORN)
(declare-fun Sofar_reset (Bool Bool Bool Bool) Bool)
(declare-fun Sofar_step (Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun excludes2_fun (Bool Bool Bool) Bool)
(declare-fun voiture_reset (Int Int Int Bool Bool Int Int Int Bool Bool) Bool)
(declare-fun voiture_step
             (Bool
              Bool
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Bool
              Bool
              Int
              Int
              Int
              Bool
              Bool)
             Bool)
(declare-fun top_reset
             (Bool
              Bool
              Int
              Int
              Int
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Bool
              Bool
              Bool
              Bool)
             Bool)
(declare-fun top_step
             (Bool
              Bool
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Bool
              Bool
              Bool
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Bool
              Bool
              Bool
              Bool)
             Bool)
(declare-fun INIT_STATE () Bool)
(declare-fun MAIN (Bool Bool Int Int Int Bool Bool Bool Bool Bool) Bool)

(assert (forall ((Sofar.__Sofar_2_m Bool)
         (Sofar.__Sofar_2_c Bool)
         (Sofar.ni_4._arrow._first_m Bool)
         (Sofar.ni_4._arrow._first_c Bool))
  (=> (and (= Sofar.__Sofar_2_m Sofar.__Sofar_2_c)
           (= Sofar.ni_4._arrow._first_m true))
      (Sofar_reset Sofar.__Sofar_2_c
                   Sofar.ni_4._arrow._first_c
                   Sofar.__Sofar_2_m
                   Sofar.ni_4._arrow._first_m))))
(assert (forall ((Sofar.ni_4._arrow._first_m Bool)
         (Sofar.ni_4._arrow._first_c Bool)
         (Sofar.__Sofar_1 Bool)
         (Sofar.ni_4._arrow._first_x Bool)
         (Sofar.Sofar Bool)
         (Sofar.X Bool)
         (Sofar.__Sofar_2_c Bool)
         (Sofar.__Sofar_2_x Bool))
  (let ((a!1 (and (= Sofar.ni_4._arrow._first_m Sofar.ni_4._arrow._first_c)
                  (= Sofar.__Sofar_1
                     (ite Sofar.ni_4._arrow._first_m true false))
                  (= Sofar.ni_4._arrow._first_x false)
                  (or (not (= Sofar.__Sofar_1 true)) (= Sofar.Sofar Sofar.X))
                  (or (not (= Sofar.__Sofar_1 false))
                      (= Sofar.Sofar (and Sofar.X Sofar.__Sofar_2_c)))
                  (= Sofar.__Sofar_2_x Sofar.Sofar))))
    (=> a!1
        (Sofar_step Sofar.X
                    Sofar.Sofar
                    Sofar.__Sofar_2_c
                    Sofar.ni_4._arrow._first_c
                    Sofar.__Sofar_2_x
                    Sofar.ni_4._arrow._first_x)))))
(assert (forall ((excludes2.excludes Bool) (excludes2.X1 Bool) (excludes2.X2 Bool))
  (=> (= excludes2.excludes (not (and excludes2.X1 excludes2.X2)))
      (excludes2_fun excludes2.X1 excludes2.X2 excludes2.excludes))))
(assert (forall ((voiture.__voiture_2_m Int)
         (voiture.__voiture_2_c Int)
         (voiture.__voiture_5_m Int)
         (voiture.__voiture_5_c Int)
         (voiture.__voiture_6_m Int)
         (voiture.__voiture_6_c Int)
         (voiture.__voiture_7_m Bool)
         (voiture.__voiture_7_c Bool)
         (voiture.ni_3._arrow._first_m Bool)
         (voiture.ni_3._arrow._first_c Bool))
  (=> (and (= voiture.__voiture_2_m voiture.__voiture_2_c)
           (= voiture.__voiture_5_m voiture.__voiture_5_c)
           (= voiture.__voiture_6_m voiture.__voiture_6_c)
           (= voiture.__voiture_7_m voiture.__voiture_7_c)
           (= voiture.ni_3._arrow._first_m true))
      (voiture_reset voiture.__voiture_2_c
                     voiture.__voiture_5_c
                     voiture.__voiture_6_c
                     voiture.__voiture_7_c
                     voiture.ni_3._arrow._first_c
                     voiture.__voiture_2_m
                     voiture.__voiture_5_m
                     voiture.__voiture_6_m
                     voiture.__voiture_7_m
                     voiture.ni_3._arrow._first_m))))
(assert (forall ((voiture.ni_3._arrow._first_m Bool)
         (voiture.ni_3._arrow._first_c Bool)
         (voiture.__voiture_1 Bool)
         (voiture.ni_3._arrow._first_x Bool)
         (voiture.second Bool)
         (voiture.s Bool)
         (voiture.move Bool)
         (voiture.__voiture_7_c Bool)
         (voiture.meter Bool)
         (voiture.m Bool)
         (voiture.__voiture_4 Bool)
         (voiture.speed Int)
         (voiture.__voiture_5_c Int)
         (voiture.toofast Bool)
         (voiture.time Int)
         (voiture.__voiture_2_c Int)
         (voiture.stop Bool)
         (voiture.dist Int)
         (voiture.__voiture_6_c Int)
         (voiture.bump Bool)
         (voiture.__voiture_7_x Bool)
         (voiture.__voiture_6_x Int)
         (voiture.__voiture_5_x Int)
         (voiture.__voiture_2_x Int))
  (let ((a!1 (and (= voiture.second voiture.s)
                  (= voiture.move voiture.__voiture_7_c)
                  (= voiture.meter (and voiture.m (not voiture.s)))))
        (a!2 (not (= (or (not voiture.move) voiture.second) true)))
        (a!3 (not (= (or (not voiture.move) voiture.second) false)))
        (a!4 (and (or (not (= voiture.__voiture_4 true))
                      (= voiture.speed (- voiture.__voiture_5_c 1)))
                  (or (not (= voiture.__voiture_4 false))
                      (= voiture.speed voiture.__voiture_5_c))))
        (a!6 (and (or (not (= voiture.second true))
                      (= voiture.time (- voiture.__voiture_2_c 1)))
                  (or (not (= voiture.second false))
                      (= voiture.time voiture.__voiture_2_c))))
        (a!7 (and (or (not (= voiture.__voiture_4 true))
                      (= voiture.dist (+ voiture.__voiture_6_c 1)))
                  (or (not (= voiture.__voiture_4 false))
                      (= voiture.dist voiture.__voiture_6_c)))))
  (let ((a!5 (or (not (= voiture.__voiture_1 false))
                 (and (or a!2 (= voiture.speed 0)) (or a!3 a!4)))))
  (let ((a!8 (and (= voiture.ni_3._arrow._first_m voiture.ni_3._arrow._first_c)
                  (= voiture.__voiture_1
                     (ite voiture.ni_3._arrow._first_m true false))
                  (= voiture.ni_3._arrow._first_x false)
                  (or (not (= voiture.__voiture_1 false)) a!1)
                  (or (not (= voiture.__voiture_1 true))
                      (and (= voiture.second false)
                           (= voiture.move true)
                           (= voiture.meter false)))
                  (= voiture.__voiture_4 (and voiture.move voiture.meter))
                  (or (not (= voiture.__voiture_1 true)) (= voiture.speed 0))
                  a!5
                  (= voiture.toofast (>= voiture.speed 3))
                  (or (not (= voiture.__voiture_1 true)) (= voiture.time 0))
                  (or (not (= voiture.__voiture_1 false)) a!6)
                  (= voiture.stop (>= voiture.time 4))
                  (or (not (= voiture.__voiture_1 true)) (= voiture.dist 0))
                  (or (not (= voiture.__voiture_1 false)) a!7)
                  (= voiture.bump (= voiture.dist 10))
                  (= voiture.__voiture_7_x
                     (and voiture.move
                          (not voiture.stop)
                          (not voiture.toofast)
                          (not voiture.bump)))
                  (= voiture.__voiture_6_x voiture.dist)
                  (= voiture.__voiture_5_x voiture.speed)
                  (= voiture.__voiture_2_x voiture.time))))
    (=> a!8
        (voiture_step voiture.m
                      voiture.s
                      voiture.toofast
                      voiture.stop
                      voiture.bump
                      voiture.dist
                      voiture.speed
                      voiture.time
                      voiture.move
                      voiture.second
                      voiture.meter
                      voiture.__voiture_2_c
                      voiture.__voiture_5_c
                      voiture.__voiture_6_c
                      voiture.__voiture_7_c
                      voiture.ni_3._arrow._first_c
                      voiture.__voiture_2_x
                      voiture.__voiture_5_x
                      voiture.__voiture_6_x
                      voiture.__voiture_7_x
                      voiture.ni_3._arrow._first_x)))))))
(assert (forall ((top.__top_2_m Bool)
         (top.__top_2_c Bool)
         (top.ni_2.Sofar.__Sofar_2_c Bool)
         (top.ni_2.Sofar.ni_4._arrow._first_c Bool)
         (top.ni_2.Sofar.__Sofar_2_m Bool)
         (top.ni_2.Sofar.ni_4._arrow._first_m Bool)
         (top.ni_1.voiture.__voiture_2_c Int)
         (top.ni_1.voiture.__voiture_5_c Int)
         (top.ni_1.voiture.__voiture_6_c Int)
         (top.ni_1.voiture.__voiture_7_c Bool)
         (top.ni_1.voiture.ni_3._arrow._first_c Bool)
         (top.ni_1.voiture.__voiture_2_m Int)
         (top.ni_1.voiture.__voiture_5_m Int)
         (top.ni_1.voiture.__voiture_6_m Int)
         (top.ni_1.voiture.__voiture_7_m Bool)
         (top.ni_1.voiture.ni_3._arrow._first_m Bool)
         (top.ni_0._arrow._first_m Bool)
         (top.ni_0._arrow._first_c Bool))
  (=> (and (= top.__top_2_m top.__top_2_c)
           (Sofar_reset top.ni_2.Sofar.__Sofar_2_c
                        top.ni_2.Sofar.ni_4._arrow._first_c
                        top.ni_2.Sofar.__Sofar_2_m
                        top.ni_2.Sofar.ni_4._arrow._first_m)
           (voiture_reset top.ni_1.voiture.__voiture_2_c
                          top.ni_1.voiture.__voiture_5_c
                          top.ni_1.voiture.__voiture_6_c
                          top.ni_1.voiture.__voiture_7_c
                          top.ni_1.voiture.ni_3._arrow._first_c
                          top.ni_1.voiture.__voiture_2_m
                          top.ni_1.voiture.__voiture_5_m
                          top.ni_1.voiture.__voiture_6_m
                          top.ni_1.voiture.__voiture_7_m
                          top.ni_1.voiture.ni_3._arrow._first_m)
           (= top.ni_0._arrow._first_m true))
      (top_reset top.__top_2_c
                 top.ni_0._arrow._first_c
                 top.ni_1.voiture.__voiture_2_c
                 top.ni_1.voiture.__voiture_5_c
                 top.ni_1.voiture.__voiture_6_c
                 top.ni_1.voiture.__voiture_7_c
                 top.ni_1.voiture.ni_3._arrow._first_c
                 top.ni_2.Sofar.__Sofar_2_c
                 top.ni_2.Sofar.ni_4._arrow._first_c
                 top.__top_2_m
                 top.ni_0._arrow._first_m
                 top.ni_1.voiture.__voiture_2_m
                 top.ni_1.voiture.__voiture_5_m
                 top.ni_1.voiture.__voiture_6_m
                 top.ni_1.voiture.__voiture_7_m
                 top.ni_1.voiture.ni_3._arrow._first_m
                 top.ni_2.Sofar.__Sofar_2_m
                 top.ni_2.Sofar.ni_4._arrow._first_m))))
(assert (forall ((top.m Bool)
         (top.s Bool)
         (top.__top_4 Bool)
         (top.ni_2.Sofar.__Sofar_2_m Bool)
         (top.ni_2.Sofar.__Sofar_2_c Bool)
         (top.ni_2.Sofar.ni_4._arrow._first_m Bool)
         (top.ni_2.Sofar.ni_4._arrow._first_c Bool)
         (top.env Bool)
         (top.ni_2.Sofar.__Sofar_2_x Bool)
         (top.ni_2.Sofar.ni_4._arrow._first_x Bool)
         (top.ni_1.voiture.__voiture_2_m Int)
         (top.ni_1.voiture.__voiture_2_c Int)
         (top.ni_1.voiture.__voiture_5_m Int)
         (top.ni_1.voiture.__voiture_5_c Int)
         (top.ni_1.voiture.__voiture_6_m Int)
         (top.ni_1.voiture.__voiture_6_c Int)
         (top.ni_1.voiture.__voiture_7_m Bool)
         (top.ni_1.voiture.__voiture_7_c Bool)
         (top.ni_1.voiture.ni_3._arrow._first_m Bool)
         (top.ni_1.voiture.ni_3._arrow._first_c Bool)
         (top.toofast Bool)
         (top.stop Bool)
         (top.bump Bool)
         (top.dist Int)
         (top.speed Int)
         (top.time Int)
         (top.move Bool)
         (top.second Bool)
         (top.meter Bool)
         (top.ni_1.voiture.__voiture_2_x Int)
         (top.ni_1.voiture.__voiture_5_x Int)
         (top.ni_1.voiture.__voiture_6_x Int)
         (top.ni_1.voiture.__voiture_7_x Bool)
         (top.ni_1.voiture.ni_3._arrow._first_x Bool)
         (top.ni_0._arrow._first_m Bool)
         (top.ni_0._arrow._first_c Bool)
         (top.__top_1 Bool)
         (top.ni_0._arrow._first_x Bool)
         (top.__top_3 Bool)
         (top.__top_2_c Bool)
         (top.__top_2_x Bool)
         (top.OK Bool))
  (let ((a!1 (and (excludes2_fun top.m top.s top.__top_4)
                  (= top.ni_2.Sofar.__Sofar_2_m top.ni_2.Sofar.__Sofar_2_c)
                  (= top.ni_2.Sofar.ni_4._arrow._first_m
                     top.ni_2.Sofar.ni_4._arrow._first_c)
                  (Sofar_step top.__top_4
                              top.env
                              top.ni_2.Sofar.__Sofar_2_m
                              top.ni_2.Sofar.ni_4._arrow._first_m
                              top.ni_2.Sofar.__Sofar_2_x
                              top.ni_2.Sofar.ni_4._arrow._first_x)
                  (= top.ni_1.voiture.__voiture_2_m
                     top.ni_1.voiture.__voiture_2_c)
                  (= top.ni_1.voiture.__voiture_5_m
                     top.ni_1.voiture.__voiture_5_c)
                  (= top.ni_1.voiture.__voiture_6_m
                     top.ni_1.voiture.__voiture_6_c)
                  (= top.ni_1.voiture.__voiture_7_m
                     top.ni_1.voiture.__voiture_7_c)
                  (= top.ni_1.voiture.ni_3._arrow._first_m
                     top.ni_1.voiture.ni_3._arrow._first_c)
                  (voiture_step top.m
                                top.s
                                top.toofast
                                top.stop
                                top.bump
                                top.dist
                                top.speed
                                top.time
                                top.move
                                top.second
                                top.meter
                                top.ni_1.voiture.__voiture_2_m
                                top.ni_1.voiture.__voiture_5_m
                                top.ni_1.voiture.__voiture_6_m
                                top.ni_1.voiture.__voiture_7_m
                                top.ni_1.voiture.ni_3._arrow._first_m
                                top.ni_1.voiture.__voiture_2_x
                                top.ni_1.voiture.__voiture_5_x
                                top.ni_1.voiture.__voiture_6_x
                                top.ni_1.voiture.__voiture_7_x
                                top.ni_1.voiture.ni_3._arrow._first_x)
                  (= top.ni_0._arrow._first_m top.ni_0._arrow._first_c)
                  (= top.__top_1 (ite top.ni_0._arrow._first_m true false))
                  (= top.ni_0._arrow._first_x false)
                  (or (not (= top.__top_1 true)) (= top.__top_3 true))
                  (or (not (= top.__top_1 false))
                      (= top.__top_3 (not top.__top_2_c)))
                  (= top.__top_2_x top.bump)
                  (= top.OK (=> top.env top.__top_3)))))
    (=> a!1
        (top_step top.m
                  top.s
                  top.OK
                  top.__top_2_c
                  top.ni_0._arrow._first_c
                  top.ni_1.voiture.__voiture_2_c
                  top.ni_1.voiture.__voiture_5_c
                  top.ni_1.voiture.__voiture_6_c
                  top.ni_1.voiture.__voiture_7_c
                  top.ni_1.voiture.ni_3._arrow._first_c
                  top.ni_2.Sofar.__Sofar_2_c
                  top.ni_2.Sofar.ni_4._arrow._first_c
                  top.__top_2_x
                  top.ni_0._arrow._first_x
                  top.ni_1.voiture.__voiture_2_x
                  top.ni_1.voiture.__voiture_5_x
                  top.ni_1.voiture.__voiture_6_x
                  top.ni_1.voiture.__voiture_7_x
                  top.ni_1.voiture.ni_3._arrow._first_x
                  top.ni_2.Sofar.__Sofar_2_x
                  top.ni_2.Sofar.ni_4._arrow._first_x)))))
(assert (=> true INIT_STATE))
(assert (forall ((top.__top_2_c Bool)
         (top.ni_0._arrow._first_c Bool)
         (top.ni_1.voiture.__voiture_2_c Int)
         (top.ni_1.voiture.__voiture_5_c Int)
         (top.ni_1.voiture.__voiture_6_c Int)
         (top.ni_1.voiture.__voiture_7_c Bool)
         (top.ni_1.voiture.ni_3._arrow._first_c Bool)
         (top.ni_2.Sofar.__Sofar_2_c Bool)
         (top.ni_2.Sofar.ni_4._arrow._first_c Bool)
         (top.__top_2_m Bool)
         (top.ni_0._arrow._first_m Bool)
         (top.ni_1.voiture.__voiture_2_m Int)
         (top.ni_1.voiture.__voiture_5_m Int)
         (top.ni_1.voiture.__voiture_6_m Int)
         (top.ni_1.voiture.__voiture_7_m Bool)
         (top.ni_1.voiture.ni_3._arrow._first_m Bool)
         (top.ni_2.Sofar.__Sofar_2_m Bool)
         (top.ni_2.Sofar.ni_4._arrow._first_m Bool)
         (top.m Bool)
         (top.s Bool)
         (top.OK Bool)
         (top.__top_2_x Bool)
         (top.ni_0._arrow._first_x Bool)
         (top.ni_1.voiture.__voiture_2_x Int)
         (top.ni_1.voiture.__voiture_5_x Int)
         (top.ni_1.voiture.__voiture_6_x Int)
         (top.ni_1.voiture.__voiture_7_x Bool)
         (top.ni_1.voiture.ni_3._arrow._first_x Bool)
         (top.ni_2.Sofar.__Sofar_2_x Bool)
         (top.ni_2.Sofar.ni_4._arrow._first_x Bool))
  (=> (and INIT_STATE
           (top_reset top.__top_2_c
                      top.ni_0._arrow._first_c
                      top.ni_1.voiture.__voiture_2_c
                      top.ni_1.voiture.__voiture_5_c
                      top.ni_1.voiture.__voiture_6_c
                      top.ni_1.voiture.__voiture_7_c
                      top.ni_1.voiture.ni_3._arrow._first_c
                      top.ni_2.Sofar.__Sofar_2_c
                      top.ni_2.Sofar.ni_4._arrow._first_c
                      top.__top_2_m
                      top.ni_0._arrow._first_m
                      top.ni_1.voiture.__voiture_2_m
                      top.ni_1.voiture.__voiture_5_m
                      top.ni_1.voiture.__voiture_6_m
                      top.ni_1.voiture.__voiture_7_m
                      top.ni_1.voiture.ni_3._arrow._first_m
                      top.ni_2.Sofar.__Sofar_2_m
                      top.ni_2.Sofar.ni_4._arrow._first_m)
           (top_step top.m
                     top.s
                     top.OK
                     top.__top_2_m
                     top.ni_0._arrow._first_m
                     top.ni_1.voiture.__voiture_2_m
                     top.ni_1.voiture.__voiture_5_m
                     top.ni_1.voiture.__voiture_6_m
                     top.ni_1.voiture.__voiture_7_m
                     top.ni_1.voiture.ni_3._arrow._first_m
                     top.ni_2.Sofar.__Sofar_2_m
                     top.ni_2.Sofar.ni_4._arrow._first_m
                     top.__top_2_x
                     top.ni_0._arrow._first_x
                     top.ni_1.voiture.__voiture_2_x
                     top.ni_1.voiture.__voiture_5_x
                     top.ni_1.voiture.__voiture_6_x
                     top.ni_1.voiture.__voiture_7_x
                     top.ni_1.voiture.ni_3._arrow._first_x
                     top.ni_2.Sofar.__Sofar_2_x
                     top.ni_2.Sofar.ni_4._arrow._first_x))
      (MAIN top.__top_2_x
            top.ni_0._arrow._first_x
            top.ni_1.voiture.__voiture_2_x
            top.ni_1.voiture.__voiture_5_x
            top.ni_1.voiture.__voiture_6_x
            top.ni_1.voiture.__voiture_7_x
            top.ni_1.voiture.ni_3._arrow._first_x
            top.ni_2.Sofar.__Sofar_2_x
            top.ni_2.Sofar.ni_4._arrow._first_x
            top.OK))))
(assert (forall ((top.__top_2_c Bool)
         (top.ni_0._arrow._first_c Bool)
         (top.ni_1.voiture.__voiture_2_c Int)
         (top.ni_1.voiture.__voiture_5_c Int)
         (top.ni_1.voiture.__voiture_6_c Int)
         (top.ni_1.voiture.__voiture_7_c Bool)
         (top.ni_1.voiture.ni_3._arrow._first_c Bool)
         (top.ni_2.Sofar.__Sofar_2_c Bool)
         (top.ni_2.Sofar.ni_4._arrow._first_c Bool)
         (dummytop.OK Bool)
         (top.m Bool)
         (top.s Bool)
         (top.OK Bool)
         (top.__top_2_x Bool)
         (top.ni_0._arrow._first_x Bool)
         (top.ni_1.voiture.__voiture_2_x Int)
         (top.ni_1.voiture.__voiture_5_x Int)
         (top.ni_1.voiture.__voiture_6_x Int)
         (top.ni_1.voiture.__voiture_7_x Bool)
         (top.ni_1.voiture.ni_3._arrow._first_x Bool)
         (top.ni_2.Sofar.__Sofar_2_x Bool)
         (top.ni_2.Sofar.ni_4._arrow._first_x Bool))
  (=> (and (MAIN top.__top_2_c
                 top.ni_0._arrow._first_c
                 top.ni_1.voiture.__voiture_2_c
                 top.ni_1.voiture.__voiture_5_c
                 top.ni_1.voiture.__voiture_6_c
                 top.ni_1.voiture.__voiture_7_c
                 top.ni_1.voiture.ni_3._arrow._first_c
                 top.ni_2.Sofar.__Sofar_2_c
                 top.ni_2.Sofar.ni_4._arrow._first_c
                 dummytop.OK)
           (top_step top.m
                     top.s
                     top.OK
                     top.__top_2_c
                     top.ni_0._arrow._first_c
                     top.ni_1.voiture.__voiture_2_c
                     top.ni_1.voiture.__voiture_5_c
                     top.ni_1.voiture.__voiture_6_c
                     top.ni_1.voiture.__voiture_7_c
                     top.ni_1.voiture.ni_3._arrow._first_c
                     top.ni_2.Sofar.__Sofar_2_c
                     top.ni_2.Sofar.ni_4._arrow._first_c
                     top.__top_2_x
                     top.ni_0._arrow._first_x
                     top.ni_1.voiture.__voiture_2_x
                     top.ni_1.voiture.__voiture_5_x
                     top.ni_1.voiture.__voiture_6_x
                     top.ni_1.voiture.__voiture_7_x
                     top.ni_1.voiture.ni_3._arrow._first_x
                     top.ni_2.Sofar.__Sofar_2_x
                     top.ni_2.Sofar.ni_4._arrow._first_x))
      (MAIN top.__top_2_x
            top.ni_0._arrow._first_x
            top.ni_1.voiture.__voiture_2_x
            top.ni_1.voiture.__voiture_5_x
            top.ni_1.voiture.__voiture_6_x
            top.ni_1.voiture.__voiture_7_x
            top.ni_1.voiture.ni_3._arrow._first_x
            top.ni_2.Sofar.__Sofar_2_x
            top.ni_2.Sofar.ni_4._arrow._first_x
            top.OK))))
(assert (forall ((top.OK Bool)
         (top.__top_2_x Bool)
         (top.ni_0._arrow._first_x Bool)
         (top.ni_1.voiture.__voiture_2_x Int)
         (top.ni_1.voiture.__voiture_5_x Int)
         (top.ni_1.voiture.__voiture_6_x Int)
         (top.ni_1.voiture.__voiture_7_x Bool)
         (top.ni_1.voiture.ni_3._arrow._first_x Bool)
         (top.ni_2.Sofar.__Sofar_2_x Bool)
         (top.ni_2.Sofar.ni_4._arrow._first_x Bool)
         (ERR Bool))
  (=> (and (not top.OK)
           (MAIN top.__top_2_x
                 top.ni_0._arrow._first_x
                 top.ni_1.voiture.__voiture_2_x
                 top.ni_1.voiture.__voiture_5_x
                 top.ni_1.voiture.__voiture_6_x
                 top.ni_1.voiture.__voiture_7_x
                 top.ni_1.voiture.ni_3._arrow._first_x
                 top.ni_2.Sofar.__Sofar_2_x
                 top.ni_2.Sofar.ni_4._arrow._first_x
                 top.OK))
      false)))
(check-sat)
