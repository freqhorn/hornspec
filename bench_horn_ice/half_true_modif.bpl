procedure main() {
  var i, n, j, k, LARGE_INT: int;
  i := 0;
  n := 0;
  j := 0;
  assume(k <= LARGE_INT && k >= -LARGE_INT);
  while (i < 2 * k)
  // invariant (i mod 2 == 0 ==> 2 * n == i) && (i mod 2 == 1 ==> 2 * n - 1 == i) && (k >= 0 ==> i <= 2 * k);
  {
    if (j == 0) {
      n := n + 1;
      j := 1;
    } else {
      j := 0;
    }
    i := i + 1;
  }
  assert(k < 0 || n == k);
}

