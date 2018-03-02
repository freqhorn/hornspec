procedure run(n: int, m: int)
{
  var x,y: int; 
  assume n>=0;
  assume m>=0;
  assume m<n;
  x := 0; 
  y := m;
  while (x<n)
    // invariant (x <= n) && (x <= m ==> y == m) && (x > m ==> x == y) && n >= 0 && m >= 0 && m < n && x <= n;
  {
    x := x+1;
    if(x>m) {
      y := y+1;
    }
  }
  assert y==n;
}
