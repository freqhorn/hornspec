procedure main()
{
    var m, i: int;
    m := 2;
    i := 1;

    while (*) {
        assert (i <= 80 || m > 81);
        if (m <= i) {
            break;
        }
        m := m + 1;
        i := i + 1;
    }
}