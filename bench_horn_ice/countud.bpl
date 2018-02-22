procedure main()
{
  var n, x, y: int;
  assume (n >= 0) && (x >= 0) && (y >= 0);
  
  x := n;
  y := 0;

  while(x > 0)
  // invariant (x + y == n) && x >= 0;
  {
    x := x - 1;
    y := y + 1;
  }
  assert(y==n);
}
