procedure main()
{
    var x, y, temp: bool;
    y := !x;

    while (*) {
        temp := x;
        x := !y;
        y := !temp;
    }

    assert(!x || !y);
}