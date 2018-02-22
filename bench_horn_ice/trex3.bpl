procedure main()
{
  var d1, d2, d3, x1, x2, x3: int;
  var c1, c2: int;
  
  assume (x1 >= 0) && (x2 >= 0) && (x3 >= 0);

  d1 := 1;
  d2 := 1;
  d3 := 1;
  
  while(x1 > 0 && x2 > 0 && x3 > 0)
  // invariant x1 >= 0 && x2 >= 0 && x3 >= 0 && d1 == 1 && d2 == 1 && d3 == 1;
  {
    if (c1 != 0)
    {
      x1 := x1 - d1;
    }
    else if (c2 != 0)
    {
      x2 := x2 - d2;
    }
    else
    {
      x3 := x3 - d3;
    }
  }
  assert(x1 == 0 || x2 == 0 || x3 == 0);
}
