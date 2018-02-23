procedure main()
{
    var x1, x3, y: int;
    x1 := 0;
    assume y > 0 && y < 5;
    assume x3 == y * 3;

    while (1) {
        assert x3 >= 3;
        assert x3 <= 212;
        if (x1 >= 200) {
            break;
        }
        x1 := x1 + 1;
        x3 := x3 + 1;
    }
}