procedure main()
{
    var x1, x3, x5, x9: int;
    x1 := 0;
    x3 := 0;
    x5 := 2 * x9;

    while (*) {
        assert (x5 != 77);

        if (*) {
            x1 := x1 + 1;
            x3 := x3 + 1;
        } else {
            x1 := x1 - 1;
            x3 := x3 - 1;
        }
        x5 := x5 + x1 + x3;
    }
}