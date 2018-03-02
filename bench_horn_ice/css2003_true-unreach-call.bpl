// c/loop-lit/css2003_true-unreach-call.c

procedure main() {
  var LARGE_INT: int;
  var i,j,k: int;
  LARGE_INT := 1000;
  i := 1;
  j := 1;
  //k = __VERIFIER_nondet_int();
  assume(0 <= k && k <= 1);
  while (i < LARGE_INT)
  // invariant 1 <= i + k && i + k <= 2 && i >= 1;
  {
    i := i + 1;
    j := j + k;
    k := k - 1;
    assert(1 <= i + k && i + k <= 2 && i >= 1);
  }
}
