// ../ice-benchmarks/single/n_c11.c

procedure main()
{
  var len, i: int;
  var a: [int]int;
  len := 0;

  while ( * )
  // invariant len <= 4 && len >= 0;
  {
    if (len == 4)
    {
      len := 0;
    }
    if (len < 0 || len > 5)
    {
      assert false;
    }
    len := len + 1;
  }
}

