// ../dilig-benchmarks/single/16.c
/*
 * From "A Practical and Complete Approach to Predicate Refinement" by McMillan TACAS'06
 */

procedure main()
{
  var i,j, x,y: int;

  x  :=  i;
  y  :=  j;

  while(x!=0)
  // invariant x-y == i-j;
  {
    x := x - 1;
    y := y - 1;
  }
  assert((i==j) ==> y==0);
}

