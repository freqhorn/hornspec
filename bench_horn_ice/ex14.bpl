procedure main()
{
    var x, y, n: int;
    x := 1;

    while (x <= n) {
        y := n - x;
        assert(!((y < 0) || (y >= n)))
        x := x + 1;
    }
}