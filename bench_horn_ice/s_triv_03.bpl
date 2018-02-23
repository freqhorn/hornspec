procedure main()
{
    var x, y: int;
    assume x < 2452;
    assume x == y;

    while (*) {
        x := x + y;
        y := x;
    }

    assert (x == y);
}