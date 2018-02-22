// c/loop-new/half_true-unreach-call.c

procedure main() {
  var i,n,k,LARGE_INT: int;
  i := 0;
  n := 0;
  //int k = __VERIFIER_nondet_int();
  assume(k <= LARGE_INT && k >= -LARGE_INT);
  while (i < 2 * k)
  // invariant (i mod 2 == 0 ==> 2 * n == i) && (i mod 2 == 1 ==> 2 * n - 1 == i) && (k >= 0 ==> i <= 2 * k);
  {
    if (i mod 2 == 0) {
      n := n + 1;
    }
    i := i + 1;
  }
  assert(k < 0 || n == k);
}

