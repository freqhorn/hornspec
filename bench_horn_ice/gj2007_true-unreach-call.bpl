// c/loop-lit/gj2007_true-unreach-call.c

procedure main()
{
  var x,y: int;
  x := 0;
  y := 50;
  
  while (x < 100)
  // invariant (x < 50 ==> y == 50) && (x >= 50 ==> x == y) && x <= 100;
  {
    if (x < 50) {
      x := x + 1;
    } else {
      x := x + 1;
      y := y + 1;
    }
  }
  
  assert (y == 100);
}
