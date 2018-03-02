procedure run()
{
  var x, y, t1, t2, count, n: int;
  x := 1;
  y := 1;
  
  while (*)
  // invariant x == y && x >= 1;
  {
    t1 := x;
    t2 := y;
    x := t1 + t2;
    y := t1 + t2;
  }
  assert (y>=1);
}
