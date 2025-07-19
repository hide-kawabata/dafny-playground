method a() {
    var x := 0;
    assert x % 2 == 0;
    while x < 300
        invariant x % 2 == 0
    {
//        x := 300;
        x := x + 2;
    }
    assert x % 2 == 0 && x >= 300;
}

method b() {
//    var x := 3;
    var x := 4; // this initial value does not let the control get in to the loop body
    assert 0 <= x <= 100;
    while x % 2 == 1
        invariant 0 <= x <= 100
    {
        assert 0 <= x <= 100 && x % 2 == 1;
//        x := x - 1; // this is not enough
//        x := 4; // this is not enough
        assert 0 <= x <= 100;
    }
    assert 0 <= x <= 100 && x % 2 != 1;
}

method b'() {
    var x := 3;
//    var x := 4; // this initial value does not let the control get in to the loop body
    assert 0 <= x <= 100;
    while x % 2 == 1
        invariant 0 <= x <= 100
        decreases if x % 2 >= 1 then -((x % 2) - 1) else -(1 - (x % 2)) // see Section 11.2
    {
        assert 0 <= x <= 100 && x % 2 == 1;
        x := x - 1; // notice the termination metric
//        x := 3; // NG
//        x := 4; // this is also OK if the termination metric is appropriate
        assert 0 <= x <= 100;
    }
    assert 0 <= x <= 100 && x % 2 != 1;
}