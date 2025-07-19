predicate f(x: int) {
    if x % 3 == 0 && x <= 102
    then true else false
}

method ex() {
    var x := 0;
    while x < 100
        invariant f(x)
    {
        assert f(x) && x < 100; // x % 3 == 0 && x <= 102 && x < 100; // x <= 99
        assert f(x+3) && x < 100; // x % 3 == 0 && x <= 99 && x < 100; // x <= 99
        assert f(x+3) && x < 100; // x+3 % 3 == 0 && x+3 <= 102 && x < 100; // x <= 99
        x := x + 3;
        assert f(x); // x % 3 == 0 && x <= 102; // x <= 102
    }
    assert f(x) && x >= 100; // x % 3 == 0 && x <= 102 && x >= 100
    assert x == 102;
}