// Exercise 1.7
method MaxSum(x: int, y: int) returns (s: int, m: int)
    ensures s == x + y
    ensures m >= x && m >= y && (m == x || m == y)
{
    s := x + y;
    if x >= y {
        m := x;
    } else {
        m := y;
    }
}

// Exercise 1.8
method ReconstructFromMaxSum(s: int, m: int) returns (x: int, y: int)
    requires 2*m >= s
//    requires 2*m >= s >= m
    ensures s == x + y
    ensures (m == x || m == y) && x <= m && y <= m
{
    x := m;
    y := s - x;
    if x >= y {
        assert x <= m;
        assert y <= m;
        assert x + y == s;
    } else {
        var t := x;
        x := y;
        y := t;
        assert x + y == s;
        assert y <= m;
        assert x <= m;
    }
    assert x <= m;
}

method TestMaxSum(x: int, y: int) {
    var s, m := MaxSum(x, y);
    var xx, yy := ReconstructFromMaxSum(s, m);
    assert (xx == x && yy == y) || (xx == y && yy == x);
}
