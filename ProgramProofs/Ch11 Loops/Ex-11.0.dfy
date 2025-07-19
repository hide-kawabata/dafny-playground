method a() {
    var x:= 0;
    while x != 100
        invariant true
    assert x == 100;
}
method b() {
    var x := 20;
    while 10 < x
        invariant x % 2 == 0
    assert x <= 10;
}
method c() {
    var x := 20;
    while x < 20
        invariant x % 2 == 0
    assert x == 20; // Even though the loop guard does not hold at the entrance of the loop, that is, you know that the loop body will not executed at all, the value of x is not guaranteed to be unchanged.
}
method d() {
    var x := 3;
    while x < 2
        invariant x % 2 == 0 // Loop invariant must be hold even though the loop body will never be executed.
    assert x % 2 == 0; // continuation is checked under the assumption of the specified invariant.
}
method e(x: int) {
    if 50 < x < 100 {
        while x < 85
            invariant x % 2 == 0
//        assert x < 85 && x % 2 == 1;
        assert x % 2 == 0 && x >= 85;
    }
}
method f(x: int) {
    if 0 <= x {
        while x % 2 == 0
            invariant x < 100
//        assert 0 <= x;
        assert x % 2 != 0 && x < 100;
    }
}
method g() {
    var x := 0;
//    assert 0 <= x < 100;
    while x < 100
        invariant 0 <= x < 100
//    assert 0 <= x < 100 && x >= 100;
    assert false;
    assert x == 25; // the control will never reach here so anything can be asserted
}