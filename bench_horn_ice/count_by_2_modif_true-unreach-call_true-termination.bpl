procedure main()
{
    var i, c, LRG: int;
    i := 0;
    c := 0;
    LRG := 256;

    while (i < LRG) {
        i := i + 2;
        c := c + 1;
    }

    assert (i == LRG);
}