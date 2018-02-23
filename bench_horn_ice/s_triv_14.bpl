procedure main()
{
    var x: bool;
    var y: int;
    y := 0;

    while (*) {
        x := (0 == (y mod 2));
        if (x) {
            y := y + 2;
        } else {
            y := y - 1;
        }
    }

    assert (y != 13621);
}