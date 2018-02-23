procedure main()
{
    var i, LRG: int;
    i := 0;
    LRG := 265;

    while (i < LRG) {
        i := i + 2;
    }

    assert (i == LRG);
}