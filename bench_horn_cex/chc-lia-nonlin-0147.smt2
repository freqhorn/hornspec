;; Original file: kind_335.smt2
(set-logic HORN)
(declare-fun Sofar_reset (Bool Bool Bool Bool) Bool)
(declare-fun Sofar_step (Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun excludes4_fun (Bool Bool Bool Bool Bool) Bool)
(declare-fun mesi_reset (Int Int Int Int Bool Int Int Int Int Bool) Bool)
(declare-fun mesi_step
             (Bool
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Int
              Bool
              Int
              Int
              Int
              Int
              Bool)
             Bool)
(declare-fun top_reset
             (Int
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Int
              Bool
              Int
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Int
              Bool)
             Bool)
(declare-fun top_step
             (Bool
              Bool
              Bool
              Bool
              Bool
              Int
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Int
              Bool
              Int
              Bool
              Bool
              Bool
              Int
              Int
              Int
              Int
              Bool)
             Bool)
(declare-fun INIT_STATE () Bool)
(declare-fun MAIN (Int Bool Bool Bool Int Int Int Int Bool Bool) Bool)

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
(assert (forall ((excludes4.excludes Bool)
         (excludes4.X1 Bool)
         (excludes4.X2 Bool)
         (excludes4.X3 Bool)
         (excludes4.X4 Bool))
  (let ((a!1 (= excludes4.excludes
                (not (or (and excludes4.X1 excludes4.X2)
                         (and excludes4.X1 excludes4.X3)
                         (and excludes4.X1 excludes4.X4)
                         (and excludes4.X2 excludes4.X3)
                         (and excludes4.X2 excludes4.X4)
                         (and excludes4.X3 excludes4.X4))))))
    (=> a!1
        (excludes4_fun excludes4.X1
                       excludes4.X2
                       excludes4.X3
                       excludes4.X4
                       excludes4.excludes)))))
(assert (forall ((mesi.__mesi_2_m Int)
         (mesi.__mesi_2_c Int)
         (mesi.__mesi_3_m Int)
         (mesi.__mesi_3_c Int)
         (mesi.__mesi_4_m Int)
         (mesi.__mesi_4_c Int)
         (mesi.__mesi_5_m Int)
         (mesi.__mesi_5_c Int)
         (mesi.ni_3._arrow._first_m Bool)
         (mesi.ni_3._arrow._first_c Bool))
  (=> (and (= mesi.__mesi_2_m mesi.__mesi_2_c)
           (= mesi.__mesi_3_m mesi.__mesi_3_c)
           (= mesi.__mesi_4_m mesi.__mesi_4_c)
           (= mesi.__mesi_5_m mesi.__mesi_5_c)
           (= mesi.ni_3._arrow._first_m true))
      (mesi_reset mesi.__mesi_2_c
                  mesi.__mesi_3_c
                  mesi.__mesi_4_c
                  mesi.__mesi_5_c
                  mesi.ni_3._arrow._first_c
                  mesi.__mesi_2_m
                  mesi.__mesi_3_m
                  mesi.__mesi_4_m
                  mesi.__mesi_5_m
                  mesi.ni_3._arrow._first_m))))
(assert (forall ((mesi.garde_me4 Bool)
         (mesi.__mesi_2_c Int)
         (mesi.garde_me3 Bool)
         (mesi.__mesi_3_c Int)
         (mesi.garde_me2 Bool)
         (mesi.__mesi_4_c Int)
         (mesi.garde_me1 Bool)
         (mesi.ni_3._arrow._first_m Bool)
         (mesi.ni_3._arrow._first_c Bool)
         (mesi.__mesi_1 Bool)
         (mesi.ni_3._arrow._first_x Bool)
         (mesi.etat_me1 Bool)
         (mesi.etat_me2 Bool)
         (mesi.etat_me3 Bool)
         (mesi.etat_me4 Bool)
         (mesi.shared_me Int)
         (mesi.modified_me Int)
         (mesi.__mesi_5_c Int)
         (mesi.invalid_me Int)
         (mesi.exclusive_me Int)
         (mesi.__mesi_5_x Int)
         (mesi.__mesi_4_x Int)
         (mesi.__mesi_3_x Int)
         (mesi.__mesi_2_x Int))
  (let ((a!1 (and (= mesi.shared_me mesi.__mesi_3_c)
                  (= mesi.modified_me mesi.__mesi_5_c)
                  (= mesi.invalid_me mesi.__mesi_2_c)
                  (= mesi.exclusive_me mesi.__mesi_4_c)))
        (a!2 (and (= mesi.shared_me 0)
                  (= mesi.modified_me 0)
                  (= mesi.invalid_me
                     (- (+ mesi.__mesi_2_c
                           mesi.__mesi_5_c
                           mesi.__mesi_4_c
                           mesi.__mesi_3_c)
                        1))
                  (= mesi.exclusive_me 1)))
        (a!7 (or (not (= mesi.garde_me2 true))
                 (and (= mesi.shared_me mesi.__mesi_3_c)
                      (= mesi.modified_me (- mesi.__mesi_5_c 1))
                      (= mesi.invalid_me mesi.__mesi_2_c)
                      (= mesi.exclusive_me (- mesi.__mesi_4_c 1)))))
        (a!10 (- (+ (- (- mesi.__mesi_3_c mesi.__mesi_4_c) 1) mesi.__mesi_5_c)
                 1)))
  (let ((a!3 (and (or (not (= mesi.garde_me4 false)) a!1)
                  (or (not (= mesi.garde_me4 true)) a!2)))
        (a!5 (and (or (not (= mesi.garde_me3 false)) a!1)
                  (or (not (= mesi.garde_me3 true)) a!2)))
        (a!8 (and (or (not (= mesi.garde_me2 false)) a!1) a!7))
        (a!11 (or (not (= mesi.garde_me1 true))
                  (and (= mesi.shared_me a!10)
                       (= mesi.modified_me 0)
                       (= mesi.invalid_me (- mesi.__mesi_2_c 1))
                       (= mesi.exclusive_me 0)))))
  (let ((a!4 (and (or (not (= mesi.etat_me4 false)) a!1)
                  (or (not (= mesi.etat_me4 true)) a!3)))
        (a!12 (and (or (not (= mesi.garde_me1 false)) a!1) a!11)))
  (let ((a!6 (and (or (not (= mesi.etat_me3 false)) a!4)
                  (or (not (= mesi.etat_me3 true)) a!5))))
  (let ((a!9 (and (or (not (= mesi.etat_me2 false)) a!6)
                  (or (not (= mesi.etat_me2 true)) a!8))))
  (let ((a!13 (and (or (not (= mesi.etat_me1 false)) a!9)
                   (or (not (= mesi.etat_me1 true)) a!12))))
  (let ((a!14 (and (= mesi.garde_me4 (>= mesi.__mesi_2_c 1))
                   (= mesi.garde_me3 (>= mesi.__mesi_3_c 1))
                   (= mesi.garde_me2 (>= mesi.__mesi_4_c 1))
                   (= mesi.garde_me1 (>= mesi.__mesi_2_c 1))
                   (= mesi.ni_3._arrow._first_m mesi.ni_3._arrow._first_c)
                   (= mesi.__mesi_1 (ite mesi.ni_3._arrow._first_m true false))
                   (= mesi.ni_3._arrow._first_x false)
                   (or (not (= mesi.__mesi_1 false)) a!13)
                   (or (not (= mesi.__mesi_1 true))
                       (and (= mesi.shared_me 0)
                            (= mesi.modified_me 0)
                            (= mesi.invalid_me 3)
                            (= mesi.exclusive_me 0)))
                   (= mesi.__mesi_5_x mesi.modified_me)
                   (= mesi.__mesi_4_x mesi.exclusive_me)
                   (= mesi.__mesi_3_x mesi.shared_me)
                   (= mesi.__mesi_2_x mesi.invalid_me))))
    (=> a!14
        (mesi_step mesi.etat_me1
                   mesi.etat_me2
                   mesi.etat_me3
                   mesi.etat_me4
                   mesi.modified_me
                   mesi.exclusive_me
                   mesi.shared_me
                   mesi.invalid_me
                   mesi.__mesi_2_c
                   mesi.__mesi_3_c
                   mesi.__mesi_4_c
                   mesi.__mesi_5_c
                   mesi.ni_3._arrow._first_c
                   mesi.__mesi_2_x
                   mesi.__mesi_3_x
                   mesi.__mesi_4_x
                   mesi.__mesi_5_x
                   mesi.ni_3._arrow._first_x)))))))))))
(assert (forall ((top.__top_2_m Int)
         (top.__top_2_c Int)
         (top.ni_2.mesi.__mesi_2_c Int)
         (top.ni_2.mesi.__mesi_3_c Int)
         (top.ni_2.mesi.__mesi_4_c Int)
         (top.ni_2.mesi.__mesi_5_c Int)
         (top.ni_2.mesi.ni_3._arrow._first_c Bool)
         (top.ni_2.mesi.__mesi_2_m Int)
         (top.ni_2.mesi.__mesi_3_m Int)
         (top.ni_2.mesi.__mesi_4_m Int)
         (top.ni_2.mesi.__mesi_5_m Int)
         (top.ni_2.mesi.ni_3._arrow._first_m Bool)
         (top.ni_1.Sofar.__Sofar_2_c Bool)
         (top.ni_1.Sofar.ni_4._arrow._first_c Bool)
         (top.ni_1.Sofar.__Sofar_2_m Bool)
         (top.ni_1.Sofar.ni_4._arrow._first_m Bool)
         (top.ni_0._arrow._first_m Bool)
         (top.ni_0._arrow._first_c Bool))
  (=> (and (= top.__top_2_m top.__top_2_c)
           (mesi_reset top.ni_2.mesi.__mesi_2_c
                       top.ni_2.mesi.__mesi_3_c
                       top.ni_2.mesi.__mesi_4_c
                       top.ni_2.mesi.__mesi_5_c
                       top.ni_2.mesi.ni_3._arrow._first_c
                       top.ni_2.mesi.__mesi_2_m
                       top.ni_2.mesi.__mesi_3_m
                       top.ni_2.mesi.__mesi_4_m
                       top.ni_2.mesi.__mesi_5_m
                       top.ni_2.mesi.ni_3._arrow._first_m)
           (Sofar_reset top.ni_1.Sofar.__Sofar_2_c
                        top.ni_1.Sofar.ni_4._arrow._first_c
                        top.ni_1.Sofar.__Sofar_2_m
                        top.ni_1.Sofar.ni_4._arrow._first_m)
           (= top.ni_0._arrow._first_m true))
      (top_reset top.__top_2_c
                 top.ni_0._arrow._first_c
                 top.ni_1.Sofar.__Sofar_2_c
                 top.ni_1.Sofar.ni_4._arrow._first_c
                 top.ni_2.mesi.__mesi_2_c
                 top.ni_2.mesi.__mesi_3_c
                 top.ni_2.mesi.__mesi_4_c
                 top.ni_2.mesi.__mesi_5_c
                 top.ni_2.mesi.ni_3._arrow._first_c
                 top.__top_2_m
                 top.ni_0._arrow._first_m
                 top.ni_1.Sofar.__Sofar_2_m
                 top.ni_1.Sofar.ni_4._arrow._first_m
                 top.ni_2.mesi.__mesi_2_m
                 top.ni_2.mesi.__mesi_3_m
                 top.ni_2.mesi.__mesi_4_m
                 top.ni_2.mesi.__mesi_5_m
                 top.ni_2.mesi.ni_3._arrow._first_m))))
(assert (forall ((top.ni_2.mesi.__mesi_2_m Int)
         (top.ni_2.mesi.__mesi_2_c Int)
         (top.ni_2.mesi.__mesi_3_m Int)
         (top.ni_2.mesi.__mesi_3_c Int)
         (top.ni_2.mesi.__mesi_4_m Int)
         (top.ni_2.mesi.__mesi_4_c Int)
         (top.ni_2.mesi.__mesi_5_m Int)
         (top.ni_2.mesi.__mesi_5_c Int)
         (top.ni_2.mesi.ni_3._arrow._first_m Bool)
         (top.ni_2.mesi.ni_3._arrow._first_c Bool)
         (top.etat_me1 Bool)
         (top.etat_me2 Bool)
         (top.etat_me3 Bool)
         (top.etat_me4 Bool)
         (top.modified_me Int)
         (top.exclusive_me Int)
         (top.shared_me Int)
         (top.invalid_me Int)
         (top.ni_2.mesi.__mesi_2_x Int)
         (top.ni_2.mesi.__mesi_3_x Int)
         (top.ni_2.mesi.__mesi_4_x Int)
         (top.ni_2.mesi.__mesi_5_x Int)
         (top.ni_2.mesi.ni_3._arrow._first_x Bool)
         (top.__top_4 Bool)
         (top.ni_1.Sofar.__Sofar_2_m Bool)
         (top.ni_1.Sofar.__Sofar_2_c Bool)
         (top.ni_1.Sofar.ni_4._arrow._first_m Bool)
         (top.ni_1.Sofar.ni_4._arrow._first_c Bool)
         (top.env Bool)
         (top.ni_1.Sofar.__Sofar_2_x Bool)
         (top.ni_1.Sofar.ni_4._arrow._first_x Bool)
         (top.ni_0._arrow._first_m Bool)
         (top.ni_0._arrow._first_c Bool)
         (top.__top_1 Bool)
         (top.ni_0._arrow._first_x Bool)
         (top.__top_3 Bool)
         (top.__top_2_c Int)
         (top.__top_2_x Int)
         (top.OK Bool))
  (let ((a!1 (or (not (= top.__top_1 false))
                 (= top.__top_3
                    (= (+ top.modified_me
                          top.exclusive_me
                          top.shared_me
                          top.invalid_me)
                       top.__top_2_c)))))
  (let ((a!2 (and (= top.ni_2.mesi.__mesi_2_m top.ni_2.mesi.__mesi_2_c)
                  (= top.ni_2.mesi.__mesi_3_m top.ni_2.mesi.__mesi_3_c)
                  (= top.ni_2.mesi.__mesi_4_m top.ni_2.mesi.__mesi_4_c)
                  (= top.ni_2.mesi.__mesi_5_m top.ni_2.mesi.__mesi_5_c)
                  (= top.ni_2.mesi.ni_3._arrow._first_m
                     top.ni_2.mesi.ni_3._arrow._first_c)
                  (mesi_step top.etat_me1
                             top.etat_me2
                             top.etat_me3
                             top.etat_me4
                             top.modified_me
                             top.exclusive_me
                             top.shared_me
                             top.invalid_me
                             top.ni_2.mesi.__mesi_2_m
                             top.ni_2.mesi.__mesi_3_m
                             top.ni_2.mesi.__mesi_4_m
                             top.ni_2.mesi.__mesi_5_m
                             top.ni_2.mesi.ni_3._arrow._first_m
                             top.ni_2.mesi.__mesi_2_x
                             top.ni_2.mesi.__mesi_3_x
                             top.ni_2.mesi.__mesi_4_x
                             top.ni_2.mesi.__mesi_5_x
                             top.ni_2.mesi.ni_3._arrow._first_x)
                  (excludes4_fun top.etat_me1
                                 top.etat_me2
                                 top.etat_me3
                                 top.etat_me4
                                 top.__top_4)
                  (= top.ni_1.Sofar.__Sofar_2_m top.ni_1.Sofar.__Sofar_2_c)
                  (= top.ni_1.Sofar.ni_4._arrow._first_m
                     top.ni_1.Sofar.ni_4._arrow._first_c)
                  (Sofar_step top.__top_4
                              top.env
                              top.ni_1.Sofar.__Sofar_2_m
                              top.ni_1.Sofar.ni_4._arrow._first_m
                              top.ni_1.Sofar.__Sofar_2_x
                              top.ni_1.Sofar.ni_4._arrow._first_x)
                  (= top.ni_0._arrow._first_m top.ni_0._arrow._first_c)
                  (= top.__top_1 (ite top.ni_0._arrow._first_m true false))
                  (= top.ni_0._arrow._first_x false)
                  (or (not (= top.__top_1 true)) (= top.__top_3 true))
                  a!1
                  (= top.__top_2_x
                     (+ top.modified_me
                        top.exclusive_me
                        top.shared_me
                        top.invalid_me))
                  (= top.OK (=> top.env top.__top_3)))))
    (=> a!2
        (top_step top.etat_me1
                  top.etat_me2
                  top.etat_me3
                  top.etat_me4
                  top.OK
                  top.__top_2_c
                  top.ni_0._arrow._first_c
                  top.ni_1.Sofar.__Sofar_2_c
                  top.ni_1.Sofar.ni_4._arrow._first_c
                  top.ni_2.mesi.__mesi_2_c
                  top.ni_2.mesi.__mesi_3_c
                  top.ni_2.mesi.__mesi_4_c
                  top.ni_2.mesi.__mesi_5_c
                  top.ni_2.mesi.ni_3._arrow._first_c
                  top.__top_2_x
                  top.ni_0._arrow._first_x
                  top.ni_1.Sofar.__Sofar_2_x
                  top.ni_1.Sofar.ni_4._arrow._first_x
                  top.ni_2.mesi.__mesi_2_x
                  top.ni_2.mesi.__mesi_3_x
                  top.ni_2.mesi.__mesi_4_x
                  top.ni_2.mesi.__mesi_5_x
                  top.ni_2.mesi.ni_3._arrow._first_x))))))
(assert (=> true INIT_STATE))
(assert (forall ((top.__top_2_c Int)
         (top.ni_0._arrow._first_c Bool)
         (top.ni_1.Sofar.__Sofar_2_c Bool)
         (top.ni_1.Sofar.ni_4._arrow._first_c Bool)
         (top.ni_2.mesi.__mesi_2_c Int)
         (top.ni_2.mesi.__mesi_3_c Int)
         (top.ni_2.mesi.__mesi_4_c Int)
         (top.ni_2.mesi.__mesi_5_c Int)
         (top.ni_2.mesi.ni_3._arrow._first_c Bool)
         (top.__top_2_m Int)
         (top.ni_0._arrow._first_m Bool)
         (top.ni_1.Sofar.__Sofar_2_m Bool)
         (top.ni_1.Sofar.ni_4._arrow._first_m Bool)
         (top.ni_2.mesi.__mesi_2_m Int)
         (top.ni_2.mesi.__mesi_3_m Int)
         (top.ni_2.mesi.__mesi_4_m Int)
         (top.ni_2.mesi.__mesi_5_m Int)
         (top.ni_2.mesi.ni_3._arrow._first_m Bool)
         (top.etat_me1 Bool)
         (top.etat_me2 Bool)
         (top.etat_me3 Bool)
         (top.etat_me4 Bool)
         (top.OK Bool)
         (top.__top_2_x Int)
         (top.ni_0._arrow._first_x Bool)
         (top.ni_1.Sofar.__Sofar_2_x Bool)
         (top.ni_1.Sofar.ni_4._arrow._first_x Bool)
         (top.ni_2.mesi.__mesi_2_x Int)
         (top.ni_2.mesi.__mesi_3_x Int)
         (top.ni_2.mesi.__mesi_4_x Int)
         (top.ni_2.mesi.__mesi_5_x Int)
         (top.ni_2.mesi.ni_3._arrow._first_x Bool))
  (=> (and INIT_STATE
           (top_reset top.__top_2_c
                      top.ni_0._arrow._first_c
                      top.ni_1.Sofar.__Sofar_2_c
                      top.ni_1.Sofar.ni_4._arrow._first_c
                      top.ni_2.mesi.__mesi_2_c
                      top.ni_2.mesi.__mesi_3_c
                      top.ni_2.mesi.__mesi_4_c
                      top.ni_2.mesi.__mesi_5_c
                      top.ni_2.mesi.ni_3._arrow._first_c
                      top.__top_2_m
                      top.ni_0._arrow._first_m
                      top.ni_1.Sofar.__Sofar_2_m
                      top.ni_1.Sofar.ni_4._arrow._first_m
                      top.ni_2.mesi.__mesi_2_m
                      top.ni_2.mesi.__mesi_3_m
                      top.ni_2.mesi.__mesi_4_m
                      top.ni_2.mesi.__mesi_5_m
                      top.ni_2.mesi.ni_3._arrow._first_m)
           (top_step top.etat_me1
                     top.etat_me2
                     top.etat_me3
                     top.etat_me4
                     top.OK
                     top.__top_2_m
                     top.ni_0._arrow._first_m
                     top.ni_1.Sofar.__Sofar_2_m
                     top.ni_1.Sofar.ni_4._arrow._first_m
                     top.ni_2.mesi.__mesi_2_m
                     top.ni_2.mesi.__mesi_3_m
                     top.ni_2.mesi.__mesi_4_m
                     top.ni_2.mesi.__mesi_5_m
                     top.ni_2.mesi.ni_3._arrow._first_m
                     top.__top_2_x
                     top.ni_0._arrow._first_x
                     top.ni_1.Sofar.__Sofar_2_x
                     top.ni_1.Sofar.ni_4._arrow._first_x
                     top.ni_2.mesi.__mesi_2_x
                     top.ni_2.mesi.__mesi_3_x
                     top.ni_2.mesi.__mesi_4_x
                     top.ni_2.mesi.__mesi_5_x
                     top.ni_2.mesi.ni_3._arrow._first_x))
      (MAIN top.__top_2_x
            top.ni_0._arrow._first_x
            top.ni_1.Sofar.__Sofar_2_x
            top.ni_1.Sofar.ni_4._arrow._first_x
            top.ni_2.mesi.__mesi_2_x
            top.ni_2.mesi.__mesi_3_x
            top.ni_2.mesi.__mesi_4_x
            top.ni_2.mesi.__mesi_5_x
            top.ni_2.mesi.ni_3._arrow._first_x
            top.OK))))
(assert (forall ((top.__top_2_c Int)
         (top.ni_0._arrow._first_c Bool)
         (top.ni_1.Sofar.__Sofar_2_c Bool)
         (top.ni_1.Sofar.ni_4._arrow._first_c Bool)
         (top.ni_2.mesi.__mesi_2_c Int)
         (top.ni_2.mesi.__mesi_3_c Int)
         (top.ni_2.mesi.__mesi_4_c Int)
         (top.ni_2.mesi.__mesi_5_c Int)
         (top.ni_2.mesi.ni_3._arrow._first_c Bool)
         (dummytop.OK Bool)
         (top.etat_me1 Bool)
         (top.etat_me2 Bool)
         (top.etat_me3 Bool)
         (top.etat_me4 Bool)
         (top.OK Bool)
         (top.__top_2_x Int)
         (top.ni_0._arrow._first_x Bool)
         (top.ni_1.Sofar.__Sofar_2_x Bool)
         (top.ni_1.Sofar.ni_4._arrow._first_x Bool)
         (top.ni_2.mesi.__mesi_2_x Int)
         (top.ni_2.mesi.__mesi_3_x Int)
         (top.ni_2.mesi.__mesi_4_x Int)
         (top.ni_2.mesi.__mesi_5_x Int)
         (top.ni_2.mesi.ni_3._arrow._first_x Bool))
  (=> (and (MAIN top.__top_2_c
                 top.ni_0._arrow._first_c
                 top.ni_1.Sofar.__Sofar_2_c
                 top.ni_1.Sofar.ni_4._arrow._first_c
                 top.ni_2.mesi.__mesi_2_c
                 top.ni_2.mesi.__mesi_3_c
                 top.ni_2.mesi.__mesi_4_c
                 top.ni_2.mesi.__mesi_5_c
                 top.ni_2.mesi.ni_3._arrow._first_c
                 dummytop.OK)
           (top_step top.etat_me1
                     top.etat_me2
                     top.etat_me3
                     top.etat_me4
                     top.OK
                     top.__top_2_c
                     top.ni_0._arrow._first_c
                     top.ni_1.Sofar.__Sofar_2_c
                     top.ni_1.Sofar.ni_4._arrow._first_c
                     top.ni_2.mesi.__mesi_2_c
                     top.ni_2.mesi.__mesi_3_c
                     top.ni_2.mesi.__mesi_4_c
                     top.ni_2.mesi.__mesi_5_c
                     top.ni_2.mesi.ni_3._arrow._first_c
                     top.__top_2_x
                     top.ni_0._arrow._first_x
                     top.ni_1.Sofar.__Sofar_2_x
                     top.ni_1.Sofar.ni_4._arrow._first_x
                     top.ni_2.mesi.__mesi_2_x
                     top.ni_2.mesi.__mesi_3_x
                     top.ni_2.mesi.__mesi_4_x
                     top.ni_2.mesi.__mesi_5_x
                     top.ni_2.mesi.ni_3._arrow._first_x))
      (MAIN top.__top_2_x
            top.ni_0._arrow._first_x
            top.ni_1.Sofar.__Sofar_2_x
            top.ni_1.Sofar.ni_4._arrow._first_x
            top.ni_2.mesi.__mesi_2_x
            top.ni_2.mesi.__mesi_3_x
            top.ni_2.mesi.__mesi_4_x
            top.ni_2.mesi.__mesi_5_x
            top.ni_2.mesi.ni_3._arrow._first_x
            top.OK))))
(assert (forall ((top.OK Bool)
         (top.__top_2_x Int)
         (top.ni_0._arrow._first_x Bool)
         (top.ni_1.Sofar.__Sofar_2_x Bool)
         (top.ni_1.Sofar.ni_4._arrow._first_x Bool)
         (top.ni_2.mesi.__mesi_2_x Int)
         (top.ni_2.mesi.__mesi_3_x Int)
         (top.ni_2.mesi.__mesi_4_x Int)
         (top.ni_2.mesi.__mesi_5_x Int)
         (top.ni_2.mesi.ni_3._arrow._first_x Bool)
         (ERR Bool))
  (=> (and (not top.OK)
           (MAIN top.__top_2_x
                 top.ni_0._arrow._first_x
                 top.ni_1.Sofar.__Sofar_2_x
                 top.ni_1.Sofar.ni_4._arrow._first_x
                 top.ni_2.mesi.__mesi_2_x
                 top.ni_2.mesi.__mesi_3_x
                 top.ni_2.mesi.__mesi_4_x
                 top.ni_2.mesi.__mesi_5_x
                 top.ni_2.mesi.ni_3._arrow._first_x
                 top.OK))
      false)))
(check-sat)
