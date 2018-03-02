// c/loop-lit/bhmr2007_true-unreach-call.c

procedure main() {
  var i,n,a,b: int;
  i := 0;
  a := 0;
  b := 0;
  //n = __VERIFIER_nondet_int();
  assume(n >= 0);
  while (i < n) 
  // invariant a + b == 3*i && i <= n;
  {
    if (*) {
      a := a + 1;
      b := b + 2;
    } else {
      a := a + 2;
      b := b + 1;
    }
    i := i + 1;
  }
  assert(a + b == 3*n);

}
