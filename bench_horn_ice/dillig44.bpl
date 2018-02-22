// dilig-benchmarks/single/44.c
/*
 * Adapted from ex20 from NECLA Static Analysis Benchmarks
 */
procedure main()
{
  var k, flag, i, j, n : int;

  i := 0;
  j := 0;

  /*
  if (flag == 1){
     n := 1;
  } else {
     n := 2;
  }
  */
  // Encoding if as assumes to avoid loop duplication due to desugaring
  assume(flag == 1 ==> n == 1);
  assume(flag != 1 ==> n == 2);

  i := 0;

  while (i <= k)
  // invariant (flag == 1 ==> i == j) && (flag == 1 ==> n == 1);
  {
    i := i + 1;
    j :=  j +n;
  }

  assert(flag == 1 ==> j == i);
} 

