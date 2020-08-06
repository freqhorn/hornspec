;; Original file: kind_870.smt2
(set-logic HORN)
(declare-fun Sofar_reset (Bool Bool Bool Bool) Bool)
(declare-fun Sofar_step (Bool Bool Bool Bool Bool Bool) Bool)
(declare-fun Store_reset (Int Bool Int Bool) Bool)
(declare-fun Store_step (Int Int Int Bool Int Bool) Bool)
(declare-fun top_reset (Int Bool Bool Bool Int Bool Bool Bool) Bool)
(declare-fun top_step (Int Bool Int Bool Bool Bool Int Bool Bool Bool) Bool)
(declare-fun INIT_STATE () Bool)
(declare-fun MAIN (Int Bool Bool Bool Bool) Bool)

(assert (forall ((Sofar.__Sofar_2_m Bool)
         (Sofar.__Sofar_2_c Bool)
         (Sofar.ni_3._arrow._first_m Bool)
         (Sofar.ni_3._arrow._first_c Bool))
  (=> (and (= Sofar.__Sofar_2_m Sofar.__Sofar_2_c)
           (= Sofar.ni_3._arrow._first_m true))
      (Sofar_reset Sofar.__Sofar_2_c
                   Sofar.ni_3._arrow._first_c
                   Sofar.__Sofar_2_m
                   Sofar.ni_3._arrow._first_m))))
(assert (forall ((Sofar.ni_3._arrow._first_m Bool)
         (Sofar.ni_3._arrow._first_c Bool)
         (Sofar.__Sofar_1 Bool)
         (Sofar.ni_3._arrow._first_x Bool)
         (Sofar.__Sofar_3 Bool)
         (Sofar.__Sofar_2_c Bool)
         (Sofar.Y Bool)
         (Sofar.X Bool)
         (Sofar.__Sofar_2_x Bool))
  (let ((a!1 (and (= Sofar.ni_3._arrow._first_m Sofar.ni_3._arrow._first_c)
                  (= Sofar.__Sofar_1
                     (ite Sofar.ni_3._arrow._first_m true false))
                  (= Sofar.ni_3._arrow._first_x false)
                  (or (not (= Sofar.__Sofar_1 true)) (= Sofar.__Sofar_3 true))
                  (or (not (= Sofar.__Sofar_1 false))
                      (= Sofar.__Sofar_3 Sofar.__Sofar_2_c))
                  (= Sofar.Y (or Sofar.__Sofar_3 Sofar.X))
                  (= Sofar.__Sofar_2_x Sofar.Y))))
    (=> a!1
        (Sofar_step Sofar.X
                    Sofar.Y
                    Sofar.__Sofar_2_c
                    Sofar.ni_3._arrow._first_c
                    Sofar.__Sofar_2_x
                    Sofar.ni_3._arrow._first_x)))))
(assert (forall ((Store.__Store_4_m Int)
         (Store.__Store_4_c Int)
         (Store.ni_2._arrow._first_m Bool)
         (Store.ni_2._arrow._first_c Bool))
  (=> (and (= Store.__Store_4_m Store.__Store_4_c)
           (= Store.ni_2._arrow._first_m true))
      (Store_reset Store.__Store_4_c
                   Store.ni_2._arrow._first_c
                   Store.__Store_4_m
                   Store.ni_2._arrow._first_m))))
(assert (forall ((Store.ni_2._arrow._first_m Bool)
         (Store.ni_2._arrow._first_c Bool)
         (Store.__Store_3 Bool)
         (Store.ni_2._arrow._first_x Bool)
         (Store.Prev Int)
         (Store.__Store_4_c Int)
         (Store.Delta Int)
         (Store.Total Int)
         (Store.__Store_4_x Int))
  (let ((a!1 (not (= (and (< Store.Delta 0) (> Store.Prev 0)) true)))
        (a!2 (not (= (and (< Store.Delta 0) (> Store.Prev 0)) false)))
        (a!3 (not (= (and (> Store.Delta 0) (< Store.Prev 10)) true)))
        (a!4 (not (= (and (> Store.Delta 0) (< Store.Prev 10)) false))))
  (let ((a!5 (and (or a!3 (= Store.Total (+ Store.Prev Store.Delta)))
                  (or a!4 (= Store.Total Store.Prev)))))
  (let ((a!6 (and (= Store.ni_2._arrow._first_m Store.ni_2._arrow._first_c)
                  (= Store.__Store_3
                     (ite Store.ni_2._arrow._first_m true false))
                  (= Store.ni_2._arrow._first_x false)
                  (or (not (= Store.__Store_3 true)) (= Store.Prev 0))
                  (or (not (= Store.__Store_3 false))
                      (= Store.Prev Store.__Store_4_c))
                  (or a!1 (= Store.Total (+ Store.Prev Store.Delta)))
                  (or a!2 a!5)
                  (= Store.__Store_4_x Store.Total))))
    (=> a!6
        (Store_step Store.Delta
                    Store.Total
                    Store.__Store_4_c
                    Store.ni_2._arrow._first_c
                    Store.__Store_4_x
                    Store.ni_2._arrow._first_x)))))))
(assert (forall ((top.ni_1.Sofar.__Sofar_2_c Bool)
         (top.ni_1.Sofar.ni_3._arrow._first_c Bool)
         (top.ni_1.Sofar.__Sofar_2_m Bool)
         (top.ni_1.Sofar.ni_3._arrow._first_m Bool)
         (top.ni_0.Store.__Store_4_c Int)
         (top.ni_0.Store.ni_2._arrow._first_c Bool)
         (top.ni_0.Store.__Store_4_m Int)
         (top.ni_0.Store.ni_2._arrow._first_m Bool))
  (=> (and (Sofar_reset top.ni_1.Sofar.__Sofar_2_c
                        top.ni_1.Sofar.ni_3._arrow._first_c
                        top.ni_1.Sofar.__Sofar_2_m
                        top.ni_1.Sofar.ni_3._arrow._first_m)
           (Store_reset top.ni_0.Store.__Store_4_c
                        top.ni_0.Store.ni_2._arrow._first_c
                        top.ni_0.Store.__Store_4_m
                        top.ni_0.Store.ni_2._arrow._first_m))
      (top_reset top.ni_0.Store.__Store_4_c
                 top.ni_0.Store.ni_2._arrow._first_c
                 top.ni_1.Sofar.__Sofar_2_c
                 top.ni_1.Sofar.ni_3._arrow._first_c
                 top.ni_0.Store.__Store_4_m
                 top.ni_0.Store.ni_2._arrow._first_m
                 top.ni_1.Sofar.__Sofar_2_m
                 top.ni_1.Sofar.ni_3._arrow._first_m))))
(assert (forall ((top.ni_1.Sofar.__Sofar_2_m Bool)
         (top.ni_1.Sofar.__Sofar_2_c Bool)
         (top.ni_1.Sofar.ni_3._arrow._first_m Bool)
         (top.ni_1.Sofar.ni_3._arrow._first_c Bool)
         (top.Delta Int)
         (top.__top_1 Bool)
         (top.ni_1.Sofar.__Sofar_2_x Bool)
         (top.ni_1.Sofar.ni_3._arrow._first_x Bool)
         (top.ni_0.Store.__Store_4_m Int)
         (top.ni_0.Store.__Store_4_c Int)
         (top.ni_0.Store.ni_2._arrow._first_m Bool)
         (top.ni_0.Store.ni_2._arrow._first_c Bool)
         (top.Total Int)
         (top.ni_0.Store.__Store_4_x Int)
         (top.ni_0.Store.ni_2._arrow._first_x Bool)
         (top.OK Bool))
  (let ((a!1 (Sofar_step (and (<= (- 1) top.Delta) (<= top.Delta 1))
                         top.__top_1
                         top.ni_1.Sofar.__Sofar_2_m
                         top.ni_1.Sofar.ni_3._arrow._first_m
                         top.ni_1.Sofar.__Sofar_2_x
                         top.ni_1.Sofar.ni_3._arrow._first_x))
        (a!2 (= top.OK
                (=> top.__top_1 (and (<= 0 top.Total) (<= top.Total 20))))))
    (=> (and (= top.ni_1.Sofar.__Sofar_2_m top.ni_1.Sofar.__Sofar_2_c)
             (= top.ni_1.Sofar.ni_3._arrow._first_m
                top.ni_1.Sofar.ni_3._arrow._first_c)
             a!1
             (= top.ni_0.Store.__Store_4_m top.ni_0.Store.__Store_4_c)
             (= top.ni_0.Store.ni_2._arrow._first_m
                top.ni_0.Store.ni_2._arrow._first_c)
             (Store_step top.Delta
                         top.Total
                         top.ni_0.Store.__Store_4_m
                         top.ni_0.Store.ni_2._arrow._first_m
                         top.ni_0.Store.__Store_4_x
                         top.ni_0.Store.ni_2._arrow._first_x)
             a!2)
        (top_step top.Delta
                  top.OK
                  top.ni_0.Store.__Store_4_c
                  top.ni_0.Store.ni_2._arrow._first_c
                  top.ni_1.Sofar.__Sofar_2_c
                  top.ni_1.Sofar.ni_3._arrow._first_c
                  top.ni_0.Store.__Store_4_x
                  top.ni_0.Store.ni_2._arrow._first_x
                  top.ni_1.Sofar.__Sofar_2_x
                  top.ni_1.Sofar.ni_3._arrow._first_x)))))
(assert (=> true INIT_STATE))
(assert (forall ((top.ni_0.Store.__Store_4_c Int)
         (top.ni_0.Store.ni_2._arrow._first_c Bool)
         (top.ni_1.Sofar.__Sofar_2_c Bool)
         (top.ni_1.Sofar.ni_3._arrow._first_c Bool)
         (top.ni_0.Store.__Store_4_m Int)
         (top.ni_0.Store.ni_2._arrow._first_m Bool)
         (top.ni_1.Sofar.__Sofar_2_m Bool)
         (top.ni_1.Sofar.ni_3._arrow._first_m Bool)
         (top.Delta Int)
         (top.OK Bool)
         (top.ni_0.Store.__Store_4_x Int)
         (top.ni_0.Store.ni_2._arrow._first_x Bool)
         (top.ni_1.Sofar.__Sofar_2_x Bool)
         (top.ni_1.Sofar.ni_3._arrow._first_x Bool))
  (=> (and INIT_STATE
           (top_reset top.ni_0.Store.__Store_4_c
                      top.ni_0.Store.ni_2._arrow._first_c
                      top.ni_1.Sofar.__Sofar_2_c
                      top.ni_1.Sofar.ni_3._arrow._first_c
                      top.ni_0.Store.__Store_4_m
                      top.ni_0.Store.ni_2._arrow._first_m
                      top.ni_1.Sofar.__Sofar_2_m
                      top.ni_1.Sofar.ni_3._arrow._first_m)
           (top_step top.Delta
                     top.OK
                     top.ni_0.Store.__Store_4_m
                     top.ni_0.Store.ni_2._arrow._first_m
                     top.ni_1.Sofar.__Sofar_2_m
                     top.ni_1.Sofar.ni_3._arrow._first_m
                     top.ni_0.Store.__Store_4_x
                     top.ni_0.Store.ni_2._arrow._first_x
                     top.ni_1.Sofar.__Sofar_2_x
                     top.ni_1.Sofar.ni_3._arrow._first_x))
      (MAIN top.ni_0.Store.__Store_4_x
            top.ni_0.Store.ni_2._arrow._first_x
            top.ni_1.Sofar.__Sofar_2_x
            top.ni_1.Sofar.ni_3._arrow._first_x
            top.OK))))
(assert (forall ((top.ni_0.Store.__Store_4_c Int)
         (top.ni_0.Store.ni_2._arrow._first_c Bool)
         (top.ni_1.Sofar.__Sofar_2_c Bool)
         (top.ni_1.Sofar.ni_3._arrow._first_c Bool)
         (dummytop.OK Bool)
         (top.Delta Int)
         (top.OK Bool)
         (top.ni_0.Store.__Store_4_x Int)
         (top.ni_0.Store.ni_2._arrow._first_x Bool)
         (top.ni_1.Sofar.__Sofar_2_x Bool)
         (top.ni_1.Sofar.ni_3._arrow._first_x Bool))
  (=> (and (MAIN top.ni_0.Store.__Store_4_c
                 top.ni_0.Store.ni_2._arrow._first_c
                 top.ni_1.Sofar.__Sofar_2_c
                 top.ni_1.Sofar.ni_3._arrow._first_c
                 dummytop.OK)
           (top_step top.Delta
                     top.OK
                     top.ni_0.Store.__Store_4_c
                     top.ni_0.Store.ni_2._arrow._first_c
                     top.ni_1.Sofar.__Sofar_2_c
                     top.ni_1.Sofar.ni_3._arrow._first_c
                     top.ni_0.Store.__Store_4_x
                     top.ni_0.Store.ni_2._arrow._first_x
                     top.ni_1.Sofar.__Sofar_2_x
                     top.ni_1.Sofar.ni_3._arrow._first_x))
      (MAIN top.ni_0.Store.__Store_4_x
            top.ni_0.Store.ni_2._arrow._first_x
            top.ni_1.Sofar.__Sofar_2_x
            top.ni_1.Sofar.ni_3._arrow._first_x
            top.OK))))
(assert (forall ((top.OK Bool)
         (top.ni_0.Store.__Store_4_x Int)
         (top.ni_0.Store.ni_2._arrow._first_x Bool)
         (top.ni_1.Sofar.__Sofar_2_x Bool)
         (top.ni_1.Sofar.ni_3._arrow._first_x Bool)
         (ERR Bool))
  (=> (and (not top.OK)
           (MAIN top.ni_0.Store.__Store_4_x
                 top.ni_0.Store.ni_2._arrow._first_x
                 top.ni_1.Sofar.__Sofar_2_x
                 top.ni_1.Sofar.ni_3._arrow._first_x
                 top.OK))
      false)))
(check-sat)
