// dilig-benchmarks/single/21.c
/*
 * Based on "larg_const.c" from InvGen test suite  
 */
procedure main() {
  var c1, c2, n, v, i, k, j : int;
  c1 := 4000;
  c2 := 2000;
  
  assume(n>0);
  assume(n<10);

  k := 0;
  i := 0;
  while( i < n )
  // invariant k >= 2000 * i && i <= n && c1 == 4000 && c2 == 2000 && i >= 0 && n > 0;
  {
    i := i + 1;
    if(*) {
      v := 0;
    } else {
      v := 1;
    }

    if( v == 0 ) {
      k := k + c1;
    } else {
      k := k + c2;
    }
  }

  assert(k>n);
}
