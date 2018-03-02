procedure main()
{
    var x: bool;
    var y: int;

    x := true;
    assume x == (y == 0);

    while (*) {
        y := y + 1;
    }

    assert (y >= 0);
}