procedure main()
{
    var x, y, i, len: int;
    assume x >= 0;
    assume y >= 0;
    assume y < x;
    assume len == x;
    assume i == 0;

    while (i < y) {
        assert(!(i < 0 || i >= len));
        i := i + 1;
    }
}