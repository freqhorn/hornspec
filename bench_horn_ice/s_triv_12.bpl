procedure main()
{
    var x, y, z, v: bool;
    x := !y;
    z := !v;

    while (*) {
        x := !x;
        y := !y;
        z := !z;
        v := !v;
    }

    assert((y != z) || (x == v));
}