(declare-rel write ((Array Int Int) Int Int Int (Array Int Int) Int Int))
(declare-rel write_several ((Array Int Int) Int Int (Array Int Int) Int (Array Int Int) Int Int))
(declare-rel write_several_loop ((Array Int Int) (Array Int Int) Int Int Int (Array Int Int)))
(declare-rel rewrite ((Array Int Int) Int Int (Array Int Int) Int Int))
(declare-rel wipe ((Array Int Int) Int Int (Array Int Int) Int Int))
(declare-rel skip_write ((Array Int Int) Int Int Int (Array Int Int) Int Int))
(declare-rel skip_read ((Array Int Int) Int Int Int (Array Int Int) Int Int))
(declare-rel read ((Array Int Int) Int Int (Array Int Int) Int Int Int))
(declare-rel leak ((Array Int Int) (Array Int Int) Int Int))
(declare-rel count (Int Int Int))
(declare-rel fail ())

(declare-var a (Array Int Int))
(declare-var a0 (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var a2 (Array Int Int))
(declare-var a3 (Array Int Int))
(declare-var a4 (Array Int Int))
(declare-var a5 (Array Int Int))
(declare-var a6 (Array Int Int))
(declare-var a7 (Array Int Int))
(declare-var data (Array Int Int))
(declare-var data0 (Array Int Int))
(declare-var wp Int)
(declare-var wp0 Int)
(declare-var wp1 Int)
(declare-var wp2 Int)
(declare-var wp3 Int)
(declare-var wp4 Int)
(declare-var wp5 Int)
(declare-var wp6 Int)
(declare-var wp7 Int)
(declare-var rp Int)
(declare-var rp0 Int)
(declare-var rp1 Int)
(declare-var rp2 Int)
(declare-var rp3 Int)
(declare-var rp4 Int)
(declare-var rp5 Int)
(declare-var rp6 Int)
(declare-var rp7 Int)
(declare-var s Int)
(declare-var s0 Int)
(declare-var i Int)
(declare-var amt Int)
(declare-var out Int)
(declare-var out0 Int)

; write
(rule (=> (and (= (store a wp s) a0) (= wp0 (+ 1 wp))) (write a wp rp s a0 wp0 rp)))
; write several
(rule (=> (= amt i) (write_several_loop a data wp i amt a)))
(rule (=>
  (and
    (not (= amt i))
    (= (select data i) s)
    (write_several_loop (store a wp s) data (+ wp 1) (+ i 1) amt a0))
  (write_several_loop a data wp i amt a0)))
(rule (=>
  (and
    (>= amt 0)
    (skip_write a wp rp amt a0 wp0 rp0)
    (write_several_loop a0 data wp0 0 amt a1))
  (write_several a wp rp data amt a1 wp0 rp0)))
; rewrite (reset)
(rule (rewrite a wp rp a 0 0))
; wipe (up to write cursor)
(rule (wipe a 0 rp a 0 0))
(rule (=> (and (>= (- wp 1) 0) (= (store a (- wp 1) 0) a0) (wipe a0 (- wp 1) rp a1 wp0 rp0)) (wipe a wp rp a1 wp0 rp0)))
; skip_write
(rule (=> (= (+ amt wp) wp0) (skip_write a wp rp amt a wp0 rp)))
; skip_read (requires that read cursor stays behind write cursor)
(rule (=> (and (= (+ amt rp) rp0) (< rp0 wp)) (skip_read a wp rp amt a wp rp0)))
; read(_byte)
(rule (=> (and (= (select a rp) out) (= (+ rp 1) rp0)) (read a wp rp a wp rp0 out)))
; decide
(rule (=> (and (<= (+ s 1) 0) (count (+ s 1) (- i 1) out)) (count s i out)))
(rule (=> (and (>= (- s 1) 0) (count (- s 1) (+ i 1) out)) (count s i out)))
(rule (count 0 0 0))

(rule (=>
  (and 
    (= wp 0)
    (= rp 0)
    ; write public data
    (write_several a wp rp data0 s0 a0 wp0 rp0)
    ; write secrets
    (write_several a0 wp0 rp0 data 0 a2 wp2 rp2)
    ; "wipe"
    (wipe a2 wp2 rp2 a3 wp3 rp3)
    ; call rewrite
    (rewrite a3 wp3 rp3 a4 wp4 rp4)
    (skip_write a4 wp4 rp4 (+ s s0) a5 wp5 rp5)
    (skip_read a5 wp5 rp5 s0 a6 wp6 rp6)
    (read a6 wp6 rp6 a7 wp7 rp7 out0)
    ; make a decision based on out0
    (count out0 i out)
  )
  (leak a data s out)))

(rule (=>
  (and (leak a data s out) (leak a data0 s out0) (not (= out out0)))
  fail))

(query fail)
