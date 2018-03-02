procedure main()
{
	var x, n : int;

	assume n >= 0;

	x := 0;

 	while (x < n)
 	// invariant x <= n;
 	{
		x := x + 1;
	}

	assert(x == n);

}
