// 11.1 Loop Implementations

// 11.1.0 Quotient modulus

method QM() {
    var x, y := 0, 191;
    while 7 <= y
        invariant 0 <= y && 7 * x + y == 191
    {
        y := y - 7;
        x := x + 1;
    }
    assert x == 191 / 7 && y == 191 % 7;
}

method QM'() {
    var x, y := 0, 191;
    while 7 <= y
        invariant 0 <= y && 7 * x + y == 191
    {
        x, y := 27, 2;
    }
    assert x == 191 / 7 && y == 191 % 7;
}

// 11.1.1 Being formal about maintaining the loop invariant

// 11.1.2 Computing sums

method sum() {
    var n := 0;
    var s := 0;
    while n != 33
        invariant s == n * (n - 1) / 2
    {
        assert s == n * (n - 1) / 2 && n != 33;
        s := s + n;
        n := n + 1;
        assert s == n * (n - 1) / 2;
    }
    assert s == n * (n - 1) / 2 && n == 33;
}

// 11.1.3 Loop frames inferred

method LoopFrameExample(X: int, Y: int)
    requires 0 <= X <= Y
{
    var i, a, b := 0, X, Y;
    while i < 100 
        invariant b >= Y // this is required because b is not a constant
    {
        i, b := i + 1, b + X;
    }
    assert a == X;
    assert Y <= b;
}
