// c/loop-lit/hhk2008_true-unreach-call.c

procedure main()
{
  var a,b: int;
  var res,cnt: int;
  
  assume (a <= 10000);
  assume (0 <= b && b <= 10000);
  
  res := a;
  cnt := b;
  
  while (cnt > 0)
  // invariant res == a + b - cnt && cnt >= 0;
  {
    cnt := cnt - 1;
    res := res + 1;
  }
  
  assert (res == a + b);
}
