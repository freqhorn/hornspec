procedure main()
{
  var x, y, x0, y0: int;

  assume (0 <= x0 && x0 <= 2 && 0 <= y0 && y0 <= 2);
  
  x := x0;
  y := y0;

  while (*)
  // invariant (x - y <= 2 && y - x <= 2);
  {
	  x := x + 2;
	  y := y + 2;
  }
  assert(!((x == 4) && (y == 0)));
}
