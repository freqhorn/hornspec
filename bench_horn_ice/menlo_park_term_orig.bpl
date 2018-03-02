procedure main()
{
    var x, y, z, i: int;
    y := 100;
    z := 1;
    assume x > 0;
    assume i >= x;

    while (x > 0) {
        assert (i >= 0);
        x := x - y;
        y := y - z;
        z := -1 * z;
        i := i - 1;
    }
}