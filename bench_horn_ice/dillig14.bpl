// dilig-benchmarks/single/14.c
/*
 * From "The Octagon Abstract Domain" HOSC 2006 by Mine.
 */

procedure main() {
  var a,j,m : int;
  
  a := 0;
  j := 1;
  
  assume(m>0);
  while (j <= m)
  // invariant a < j && a > -j && m > 0 && j <= m+1
  {
    if (*) {
      a := a + 1;
    } else {
      a := a - 1;
    }
    j := j + 1;
  }

  assert(a >= -m);
  assert(a <= m);
}
