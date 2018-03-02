procedure main()
{
	var x, y : int;
	x := 0;
	y := 0;

	while(y >= 0)
  // invariant y == 0 && x == 0;
	{
		y := y + x;	
	}

	assert(0 == 1);
}
