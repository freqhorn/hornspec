// dilig-benchmarks/single/04.c
/*
 * Taken from Gulwani PLDI'08:
 * Program Analysis as Constraint Solving
 */

procedure main() {
  var x,y: int;

  x := -50;

  while( x < 0 )
  // invariant (y<=0) ==> x<0 ;
  {
    x := x+y;
    y := y + 1;
  }
  assert(y>0);
}
