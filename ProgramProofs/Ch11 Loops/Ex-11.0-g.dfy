method g() {
    var x := 0;
//    assert 0 <= x < 100;
    while x < 100
        invariant 0 <= x < 100
//    assert 0 <= x < 100 && x >= 100;
    assert x == 25;
}
