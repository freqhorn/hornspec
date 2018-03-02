procedure main()
{
    var x, y: bool;
    y := (!x);

    while (*) {
        x := (!x);
        y := (!y);
    }

    if (x) {
        assert (!y);
    }
}