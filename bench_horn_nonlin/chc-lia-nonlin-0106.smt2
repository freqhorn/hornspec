;; Original file: adr_53.smt2
(set-logic HORN)
(declare-fun |bcopy_aux$unknown:6| (Int Int) Bool)
(declare-fun |bcopy_aux$unknown:3| (Int Int Int) Bool)
(declare-fun |bcopy_aux$unknown:2| (Int Int) Bool)
(declare-fun |bcopy_aux$unknown:4| (Int Int) Bool)
(declare-fun |bcopy_aux$unknown:5| (Int Int Int) Bool)
(declare-fun |update$unknown:11| (Int) Bool)
(declare-fun |update$unknown:12| (Int Int) Bool)
(declare-fun |bcopy_aux$unknown:7| (Int Int Int) Bool)
(declare-fun |make_array$unknown:9| (Int Int) Bool)
(declare-fun |make_array$unknown:10| (Int Int Int) Bool)
(declare-fun |update$unknown:15| (Int Int Int) Bool)
(declare-fun |update$unknown:16| (Int Int Int Int) Bool)


(assert (forall ((|$knormal:6| Int)
         (|$alpha-11:i| Int)
         (|$alpha-8:m| Int)
         (|$knormal:12| Int)
         (|$knormal:15| Int)
         (|$V-reftype:3| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:6|))
                     (>= |$alpha-11:i| |$alpha-8:m|))
                  (= |$knormal:12| (+ |$alpha-11:i| 1))
                  (not (not (= 0 |$knormal:6|)))
                  (|bcopy_aux$unknown:6| |$alpha-11:i| |$alpha-8:m|)
                  (|bcopy_aux$unknown:3|
                    |$knormal:15|
                    |$alpha-11:i|
                    |$alpha-8:m|)
                  (|bcopy_aux$unknown:2| |$V-reftype:3| |$alpha-8:m|)
                  true)))
    (=> a!1 (|bcopy_aux$unknown:2| |$V-reftype:3| |$alpha-8:m|)))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-11:i| Int)
         (|$alpha-8:m| Int)
         (|$knormal:12| Int)
         (|$knormal:15| Int)
         (|$V-reftype:5| Int)
         (|$alpha-9:src| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:6|))
                     (>= |$alpha-11:i| |$alpha-8:m|))
                  (= |$knormal:12| (+ |$alpha-11:i| 1))
                  (not (not (= 0 |$knormal:6|)))
                  (|bcopy_aux$unknown:6| |$alpha-11:i| |$alpha-8:m|)
                  (|bcopy_aux$unknown:3|
                    |$knormal:15|
                    |$alpha-11:i|
                    |$alpha-8:m|)
                  (|bcopy_aux$unknown:3|
                    |$V-reftype:5|
                    |$alpha-9:src|
                    |$alpha-8:m|)
                  (|bcopy_aux$unknown:2| |$alpha-9:src| |$alpha-8:m|)
                  true)))
    (=> a!1
        (|bcopy_aux$unknown:3|
          |$V-reftype:5|
          |$alpha-9:src|
          |$alpha-8:m|)))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-11:i| Int)
         (|$alpha-8:m| Int)
         (|$knormal:12| Int)
         (|$V-reftype:7| Int)
         (|$knormal:15| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:6|))
                     (>= |$alpha-11:i| |$alpha-8:m|))
                  (= |$knormal:12| (+ |$alpha-11:i| 1))
                  (not (not (= 0 |$knormal:6|)))
                  (|bcopy_aux$unknown:6| |$alpha-11:i| |$alpha-8:m|)
                  (|bcopy_aux$unknown:4| |$V-reftype:7| |$alpha-8:m|)
                  (|bcopy_aux$unknown:3|
                    |$knormal:15|
                    |$alpha-11:i|
                    |$alpha-8:m|)
                  true)))
    (=> a!1 (|bcopy_aux$unknown:4| |$V-reftype:7| |$alpha-8:m|)))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-11:i| Int)
         (|$alpha-8:m| Int)
         (|$knormal:12| Int)
         (|$V-reftype:9| Int)
         (|$alpha-10:des| Int)
         (|$knormal:15| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:6|))
                     (>= |$alpha-11:i| |$alpha-8:m|))
                  (= |$knormal:12| (+ |$alpha-11:i| 1))
                  (not (not (= 0 |$knormal:6|)))
                  (|bcopy_aux$unknown:6| |$alpha-11:i| |$alpha-8:m|)
                  (|bcopy_aux$unknown:5|
                    |$V-reftype:9|
                    |$alpha-10:des|
                    |$alpha-8:m|)
                  (|bcopy_aux$unknown:4| |$alpha-10:des| |$alpha-8:m|)
                  (|bcopy_aux$unknown:3|
                    |$knormal:15|
                    |$alpha-11:i|
                    |$alpha-8:m|)
                  true)))
    (=> a!1
        (|bcopy_aux$unknown:5|
          |$V-reftype:9|
          |$alpha-10:des|
          |$alpha-8:m|)))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-11:i| Int)
         (|$alpha-8:m| Int)
         (|$alpha-10:des| Int)
         (|$V-reftype:9| Int)
         (|$knormal:15| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:6|))
                     (>= |$alpha-11:i| |$alpha-8:m|))
                  (not (not (= 0 |$knormal:6|)))
                  (|update$unknown:11| |$alpha-10:des|)
                  (|bcopy_aux$unknown:6| |$alpha-11:i| |$alpha-8:m|)
                  (|bcopy_aux$unknown:5|
                    |$V-reftype:9|
                    |$alpha-10:des|
                    |$alpha-8:m|)
                  (|bcopy_aux$unknown:3|
                    |$knormal:15|
                    |$alpha-11:i|
                    |$alpha-8:m|)
                  true)))
    (=> a!1 (|update$unknown:12| |$V-reftype:9| |$alpha-10:des|)))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-11:i| Int)
         (|$alpha-8:m| Int)
         (|$knormal:12| Int)
         (|$V-reftype:46| Int)
         (|$knormal:14| Int)
         (|$knormal:15| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:6|))
                     (>= |$alpha-11:i| |$alpha-8:m|))
                  (= |$knormal:12| (+ |$alpha-11:i| 1))
                  (= |$V-reftype:46| |$knormal:14|)
                  (not (not (= 0 |$knormal:6|)))
                  (|bcopy_aux$unknown:7|
                    |$knormal:14|
                    |$knormal:12|
                    |$alpha-8:m|)
                  (|bcopy_aux$unknown:6| |$alpha-11:i| |$alpha-8:m|)
                  (|bcopy_aux$unknown:3|
                    |$knormal:15|
                    |$alpha-11:i|
                    |$alpha-8:m|)
                  true)))
    (=> a!1
        (|bcopy_aux$unknown:7|
          |$V-reftype:46|
          |$alpha-11:i|
          |$alpha-8:m|)))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-11:i| Int)
         (|$alpha-8:m| Int)
         (|$V-reftype:24| Int)
         (|$knormal:15| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:6|))
                     (>= |$alpha-11:i| |$alpha-8:m|))
                  (not (not (= 0 |$knormal:6|)))
                  (|update$unknown:11| |$V-reftype:24|)
                  (|bcopy_aux$unknown:6| |$alpha-11:i| |$alpha-8:m|)
                  (|bcopy_aux$unknown:3|
                    |$knormal:15|
                    |$alpha-11:i|
                    |$alpha-8:m|)
                  true)))
    (=> a!1 (|bcopy_aux$unknown:4| |$V-reftype:24| |$alpha-8:m|)))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-11:i| Int)
         (|$alpha-8:m| Int)
         (|$knormal:12| Int)
         (|$knormal:15| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:6|))
                     (>= |$alpha-11:i| |$alpha-8:m|))
                  (= |$knormal:12| (+ |$alpha-11:i| 1))
                  (not (not (= 0 |$knormal:6|)))
                  (|bcopy_aux$unknown:6| |$alpha-11:i| |$alpha-8:m|)
                  (|bcopy_aux$unknown:3|
                    |$knormal:15|
                    |$alpha-11:i|
                    |$alpha-8:m|)
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-11:i| Int)
         (|$alpha-8:m| Int)
         (|$knormal:12| Int)
         (|$knormal:15| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:6|))
                     (>= |$alpha-11:i| |$alpha-8:m|))
                  (= |$knormal:12| (+ |$alpha-11:i| 1))
                  (not (not (= 0 |$knormal:6|)))
                  (|bcopy_aux$unknown:6| |$alpha-11:i| |$alpha-8:m|)
                  (|bcopy_aux$unknown:3|
                    |$knormal:15|
                    |$alpha-11:i|
                    |$alpha-8:m|)
                  true)))
    (=> a!1 (|bcopy_aux$unknown:6| |$knormal:12| |$alpha-8:m|)))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-11:i| Int)
         (|$alpha-8:m| Int)
         (|$knormal:15| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:6|))
                     (>= |$alpha-11:i| |$alpha-8:m|))
                  (not (not (= 0 |$knormal:6|)))
                  (|bcopy_aux$unknown:6| |$alpha-11:i| |$alpha-8:m|)
                  (|bcopy_aux$unknown:3|
                    |$knormal:15|
                    |$alpha-11:i|
                    |$alpha-8:m|)
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-11:i| Int)
         (|$alpha-8:m| Int)
         (|$knormal:15| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:6|))
                     (>= |$alpha-11:i| |$alpha-8:m|))
                  (not (not (= 0 |$knormal:6|)))
                  (|bcopy_aux$unknown:6| |$alpha-11:i| |$alpha-8:m|)
                  (|bcopy_aux$unknown:3|
                    |$knormal:15|
                    |$alpha-11:i|
                    |$alpha-8:m|)
                  true
                  (not true))))
    (=> a!1 true))))
(assert (forall ((|$knormal:6| Int)
         (|$alpha-11:i| Int)
         (|$alpha-8:m| Int)
         (|$V-reftype:44| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:6|))
                     (>= |$alpha-11:i| |$alpha-8:m|))
                  (= |$V-reftype:44| 1)
                  (not (= 0 |$knormal:6|))
                  (|bcopy_aux$unknown:6| |$alpha-11:i| |$alpha-8:m|)
                  true)))
    (=> a!1
        (|bcopy_aux$unknown:7|
          |$V-reftype:44|
          |$alpha-11:i|
          |$alpha-8:m|)))))
(assert (forall ((|$knormal:6| Int) (|$alpha-11:i| Int) (|$alpha-8:m| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:6|))
                     (>= |$alpha-11:i| |$alpha-8:m|))
                  (not (not (= 0 |$knormal:6|)))
                  (|bcopy_aux$unknown:6| |$alpha-11:i| |$alpha-8:m|)
                  true)))
    (=> a!1 (|bcopy_aux$unknown:2| |$alpha-11:i| |$alpha-8:m|)))))
(assert (forall ((|$knormal:28| Int)
         (|$knormal:22| Int)
         (|$alpha-13:n| Int)
         (|$alpha-14:m| Int)
         (|$V-reftype:3| Int))
  (let ((a!1 (and (= |$knormal:28| 0)
                  (= (not (= 0 |$knormal:22|))
                     (<= |$alpha-13:n| |$alpha-14:m|))
                  (not (= 0 |$knormal:22|))
                  (|bcopy_aux$unknown:2| |$V-reftype:3| |$alpha-13:n|))))
    (=> a!1 (|make_array$unknown:9| |$V-reftype:3| |$alpha-13:n|)))))
(assert (forall ((|$knormal:28| Int)
         (|$knormal:22| Int)
         (|$alpha-13:n| Int)
         (|$alpha-14:m| Int)
         (|$V-reftype:23| Int)
         (|$knormal:32| Int))
  (let ((a!1 (and (= |$knormal:28| 0)
                  (= (not (= 0 |$knormal:22|))
                     (<= |$alpha-13:n| |$alpha-14:m|))
                  (not (= 0 |$knormal:22|))
                  (|make_array$unknown:10|
                    |$V-reftype:23|
                    |$knormal:32|
                    |$alpha-13:n|)
                  (|bcopy_aux$unknown:2| |$knormal:32| |$alpha-13:n|))))
    (=> a!1
        (|bcopy_aux$unknown:3|
          |$V-reftype:23|
          |$knormal:32|
          |$alpha-13:n|)))))
(assert (forall ((|$knormal:28| Int)
         (|$knormal:22| Int)
         (|$alpha-13:n| Int)
         (|$alpha-14:m| Int)
         (|$V-reftype:7| Int))
  (let ((a!1 (and (= |$knormal:28| 0)
                  (= (not (= 0 |$knormal:22|))
                     (<= |$alpha-13:n| |$alpha-14:m|))
                  (not (= 0 |$knormal:22|))
                  (|bcopy_aux$unknown:4| |$V-reftype:7| |$alpha-13:n|))))
    (=> a!1 (|make_array$unknown:9| |$V-reftype:7| |$alpha-14:m|)))))
(assert (forall ((|$knormal:28| Int)
         (|$knormal:22| Int)
         (|$alpha-13:n| Int)
         (|$alpha-14:m| Int)
         (|$V-reftype:23| Int)
         (|$knormal:31| Int))
  (let ((a!1 (and (= |$knormal:28| 0)
                  (= (not (= 0 |$knormal:22|))
                     (<= |$alpha-13:n| |$alpha-14:m|))
                  (not (= 0 |$knormal:22|))
                  (|make_array$unknown:10|
                    |$V-reftype:23|
                    |$knormal:31|
                    |$alpha-14:m|)
                  (|bcopy_aux$unknown:4| |$knormal:31| |$alpha-13:n|))))
    (=> a!1
        (|bcopy_aux$unknown:5|
          |$V-reftype:23|
          |$knormal:31|
          |$alpha-13:n|)))))
(assert (forall ((|$knormal:3| Int)
         (|$knormal:1| Int)
         (|$knormal:2| Int)
         (|$alpha-2:i| Int)
         (|$alpha-1:n| Int)
         (|$alpha-3:$$tmp::1| Int)
         (|$V-reftype:39| Int))
  (let ((a!1 (= (not (= 0 |$knormal:3|))
                (and (not (= 0 |$knormal:1|)) (not (= 0 |$knormal:2|))))))
  (let ((a!2 (and a!1
                  (= (not (= 0 |$knormal:2|))
                     (< |$alpha-2:i| |$alpha-1:n|))
                  (= (not (= 0 |$knormal:1|)) (<= 0 |$alpha-2:i|))
                  (= |$alpha-3:$$tmp::1| 1)
                  (= |$V-reftype:39| 0)
                  (not (= 0 |$knormal:3|))
                  (|make_array$unknown:9| |$alpha-2:i| |$alpha-1:n|)
                  true)))
    (=> a!2
        (|make_array$unknown:10|
          |$V-reftype:39|
          |$alpha-2:i|
          |$alpha-1:n|))))))
(assert (forall ((|$knormal:3| Int)
         (|$knormal:1| Int)
         (|$knormal:2| Int)
         (|$alpha-2:i| Int)
         (|$alpha-1:n| Int))
  (let ((a!1 (= (not (= 0 |$knormal:3|))
                (and (not (= 0 |$knormal:1|)) (not (= 0 |$knormal:2|))))))
  (let ((a!2 (and a!1
                  (= (not (= 0 |$knormal:2|))
                     (< |$alpha-2:i| |$alpha-1:n|))
                  (= (not (= 0 |$knormal:1|)) (<= 0 |$alpha-2:i|))
                  (not (not (= 0 |$knormal:3|)))
                  (|make_array$unknown:9| |$alpha-2:i| |$alpha-1:n|)
                  true)))
    (=> a!2 false)))))
(assert (forall ((|$knormal:4| Int)
         (|$alpha-5:i| Int)
         (|$alpha-7:j| Int)
         (|$V-reftype:42| Int)
         (|$knormal:5| Int)
         (|$alpha-6:x| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:4|))
                     (= |$alpha-5:i| |$alpha-7:j|))
                  (= |$V-reftype:42| |$knormal:5|)
                  (not (not (= 0 |$knormal:4|)))
                  (|update$unknown:15|
                    |$alpha-7:j|
                    |$alpha-6:x|
                    |$alpha-5:i|)
                  true
                  true
                  (|update$unknown:12| |$knormal:5| |$alpha-5:i|))))
    (=> a!1
        (|update$unknown:16|
          |$V-reftype:42|
          |$alpha-7:j|
          |$alpha-6:x|
          |$alpha-5:i|)))))
(assert (forall ((|$knormal:4| Int)
         (|$alpha-5:i| Int)
         (|$alpha-7:j| Int)
         (|$V-reftype:41| Int)
         (|$alpha-6:x| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:4|))
                     (= |$alpha-5:i| |$alpha-7:j|))
                  (= |$V-reftype:41| |$alpha-6:x|)
                  (not (= 0 |$knormal:4|))
                  (|update$unknown:15|
                    |$alpha-7:j|
                    |$alpha-6:x|
                    |$alpha-5:i|)
                  true
                  true)))
    (=> a!1
        (|update$unknown:16|
          |$V-reftype:41|
          |$alpha-7:j|
          |$alpha-6:x|
          |$alpha-5:i|)))))
(assert (forall ((|$knormal:4| Int)
         (|$alpha-5:i| Int)
         (|$alpha-7:j| Int)
         (|$alpha-6:x| Int))
  (let ((a!1 (and (= (not (= 0 |$knormal:4|))
                     (= |$alpha-5:i| |$alpha-7:j|))
                  (not (not (= 0 |$knormal:4|)))
                  (|update$unknown:15|
                    |$alpha-7:j|
                    |$alpha-6:x|
                    |$alpha-5:i|)
                  true
                  true)))
    (=> a!1 (|update$unknown:11| |$alpha-5:i|)))))
(assert (forall ((|$knormal:28| Int)
         (|$knormal:22| Int)
         (|$alpha-13:n| Int)
         (|$alpha-14:m| Int))
  (let ((a!1 (and (= |$knormal:28| 0)
                  (= (not (= 0 |$knormal:22|))
                     (<= |$alpha-13:n| |$alpha-14:m|))
                  (not (= 0 |$knormal:22|)))))
    (=> a!1 (|bcopy_aux$unknown:6| |$knormal:28| |$alpha-13:n|)))))
(check-sat)
