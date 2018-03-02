// dilig-benchmarks/single/43.c
/*
 * Based on ex16 from NECLA Static Analysis Benchmarks
 */

procedure main()
{
  var x,y,i,t : int;
  
  i := 0;
  t := y;
   
  if (x==y) {
    return;
  }
  
  while (*)
  // invariant y >= t;
  {
    if (x > 0) {
      y := y + x;
    }
  }
  
  assert(y>=t);
}

