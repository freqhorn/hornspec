procedure main()
{
    var x, y, i: int;
    i := 50;

    while((x div 50) == y) {
        assert (i >= 0);
        x := x + 51;
        y := y + 1;
        i := i - 1;
    }
}