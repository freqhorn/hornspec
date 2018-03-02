procedure main()
{
    var i, j: int;
    i := 0;
    j := 0;

    while (*) {
        i := i + 1;
        if (j == 0) {
            j := 1;
        } else {
            j := 0;
        }
    }

    if (j == 1) {
        assert ((i mod 2) == 1);
    } else {
        assert ((i mod 2) == 0);
    }
}