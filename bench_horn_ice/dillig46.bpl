// dilig-benchmarks/single/46.c
procedure main()
{
  var w,z,x,y : int;

  w  :=  1;
  z  :=  0;
  x :=  0;
  y := 0;

  while(*)
  // invariant x != 0 ==> (x == 1 && w mod 2 == 0);
  {
    if(w mod 2 == 1) {
      x := x + 1;
      w := w + 1;
    }
    if(z mod 2== 0) {
      y := y + 1;
      z := z + 1;
    }
  }
  
  assert(x<=1);
}


