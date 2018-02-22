procedure main()
{
    var x, a, b, len: int;

    x := 0;
    a := 0;
    b := 0;
    assume len >= 0;

    while (*) {
        x := x + 1;
        if (*) {
            a := a + 1;
            b := b + 2;
        } else {
            a := a + 2;
            b := b + 1;
        }
    }

    assert((a + b) == (x * 3));
}