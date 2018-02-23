procedure main()
{
    var c1, c3, c5, z: int;

    c1 := 0;
    c3 := 0;
    c5 := 0;
    z := 0;

    while (*) {
        if (*) {
            c1 := c1 + 1;
            z := z + 1;
        } else if (*) {
            c3 := c3 + 1;
            z := z - 1;
        } else {
            c5 := c5 + 1;
            z := z + 1;
        }
    }

    assert(c1 != c3 || c1 != c5 || c1 == z);
}