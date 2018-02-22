// dilig-benchmarks/single/07.c
/*
 * From "Path Invariants" PLDI 07 by Beyer et al.
 */

procedure main() {

  var i,n,a,b: int;
  assume( n >= 0 );
  i := 0; a := 0; b := 0;
  while( i < n ) 
  // invariant a+b==3*i && i <= n;
  {
    if(*) {
      a := a+1;
      b := b+2;
    } else {
      a := a+2;
      b := b+1;
    }
    i := i+1;
  }
  assert( a+b == 3*n );
}
