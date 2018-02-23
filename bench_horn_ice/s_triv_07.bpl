procedure main()
{
    var x, y: int;
    x := 0;
    y := 1;

    while (*) {
        x := x + 1;
        y := 0;
        if (x == 1) {
            assert (y == 0);
        }
    }
}