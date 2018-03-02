procedure main()
{
    var i, k, LRG: int;
    i := 0;
    assume 0 <= k;
    assume k <= 10;
    assume LRG >= 0;

    while (i < (LRG * k)) {
        i := i + k;
    }

    assert i == (LRG * k);
}