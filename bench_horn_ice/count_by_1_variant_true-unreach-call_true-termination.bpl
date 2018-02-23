procedure main()
{
    var i, LRG: int;
    i := 0;
    assume i < LRG;

    while ((i + 1) < LRG) {
        i := i + 1;
    }

    assert (i <= LRG || LRG <= 10000);
}