procedure main()
{
    var N1, N2, i2: int;
    assume N1 == N2;
    assume i1 == N1;
    assume i2 == 0;

    while (1) {
        assert((i2 == N1) == (i1 == 0));
        if (!(i1 > 0 && i2 < N1)) {
            break;
        }
        i1 := i1 - 1;
        i2 := i2 + 1;
    }
}