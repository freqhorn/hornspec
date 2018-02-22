procedure run(k0: int)
{
  var i, j, z, x, y, w, k: int;
  
  i := 1;
  j := 0;
  z := i - j;
  x := 0;
  y := 0;
  w := 0;
  k := k0;

  while(k > 0) 
  // invariant z - (z div 2)*2 == 1 && w - (w div 2)*2 == 0 && x == y;
  {
    z := z + x + y + w;
    y := y + 1;
    
    if(z - (z div 2) * 2 == 1) 
    {
      x := x + 1;
    }
    w := w + 2;
    k := k - 1;
  }

  assert(x==y);
}
