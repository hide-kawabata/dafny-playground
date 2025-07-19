method QM''() {
    var x, y := 0, 191;
    while 7 <= y
        invariant 0 <= y && 7 * x + y == 191
    {
        assert 0 <= y && 7 * x + y == 191 && 7 <= y;
        if 14 <= y {
            assert 0 <= y && 7 * x + y == 191 && 14 <= y;
            y := y - 14;
            x := x + 2;
            assert 0 <= y && 7 * x + y == 191;
        } else {
            assert 0 <= y && 7 * x + y == 191 && 7 <= y;
            y := y - 7;
            x := x + 1;
            assert 0 <= y && 7 * x + y == 191;
        }
        assert 0 <= y && 7 * x + y == 191;
    }
    assert 0 <= y && 7 * x + y == 191 && 7 > y;
    assert x == 191 / 7 && y == 191 % 7;
}
