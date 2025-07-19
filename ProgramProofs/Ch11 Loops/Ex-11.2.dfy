method a() {
    var i := 0;
    while i < 100
//        invariant 0 <= i
        invariant 100 >= i
    assert i == 100;
//    assert 100 >= i >= 100;
}

method b() {
    var i := 100;
    while 0 < i
//        invariant true
        invariant i >= 0
    assert i == 0;
//    assert i >= 0 && 0 >= i;
}

method c() {
    var i := 0;
    while i < 97
//        invariant 0 <= i <= 99
        invariant i < 97 || i == 99
    assert i == 99;
//    assert (i < 97 || i == 99) && i >= 97;
}

method d() {
    var i := 22;
    while i % 5 != 0
//        invariant 10 <= i <= 100
        invariant i == 22 || i == 55
    assert i == 55;
//    assert (i == 22 || i == 55) && i % 5 == 0;
}
