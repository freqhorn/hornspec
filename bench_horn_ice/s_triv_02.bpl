procedure main()
{
    var x, y: int;
    assume x == y;

    while (*) {
        x := x + y;
        y := x;
    }

    assert (x == y);
}