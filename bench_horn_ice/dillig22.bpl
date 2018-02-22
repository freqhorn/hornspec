// dilig-benchmarks/single/22.bpl
procedure main()
{
  var x,y,z,k : int;
  x  :=  0;
  y  :=  0;
  z  :=  0;
  k  :=  0;

  while(*)
  // invariant x == y && y == z && (k mod 3 == 0);
  {
     if(k mod 3 == 0) {
       x := x + 1;
     }
     y := y + 1;
     z := z + 1;
     k := x+y+z;
  }

  assert(x==y);
  assert(y==z);
}
