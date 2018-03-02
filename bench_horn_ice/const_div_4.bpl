procedure main()
{
    var x, y, i: int;
    i := 100;

    while((x div 100) == y) {
        assert (i >= 0);
        x := x + 101;
        y := y + 1;
        i := i - 1;
    }
}