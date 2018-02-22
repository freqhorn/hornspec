procedure main()
{
  var x1,x2,x3,x4,x5: int;
  var x1p,x2p,x3p,x4p,x5p: int;

  x1 := 0;
  x2 := 0;
  x3 := 0;
  x4 := 0;
  x5 := 0;

  while(*)
  // invariant (0 <= x1 && x1 <= x4 + 1 && x2 == x3 && (x2 <= -1 || x4 <= x2 + 2) && x5 == 0);
  {
    havoc x1p;
    havoc x2p;
    havoc x3p;
    havoc x4p;
    havoc x5p;

    if (0 <= x1p && x1p <= x4p + 1 && x2p == x3p && (x2p <= -1 || x4p <= x2p + 2) && x5p == 0)
    {
      x1 := x1p;
      x2 := x2p;
      x3 := x3p;
      x4 := x4p;
      x5 := x5p;
    }
  }
  assert(0 <= x1 && x1 <= x4 + 1 && x2 == x3 && (x2 <= -1 || x4 <= x2 + 2) && x5 == 0);
}
