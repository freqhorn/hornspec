procedure run(flag: int)
{
  var x, y, i, j: int;
  x := 0;
  y := 0;
  j := 0;
  i := 0;
  
  while(*)
  // invariant x == y && ((flag != 0) ==> j == i) && ((flag == 0) ==> j == x+i);
  {
    x := x + 1;
    y := y + 1;
    i := i + x;
    j := j + y;
  
    if(flag == 0) {
      j := j + 1;
    }
  }
  assert(j>=i);
}
