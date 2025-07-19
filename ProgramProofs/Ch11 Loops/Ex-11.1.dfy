method a() {
    var i := 0;
    while i < 100
        invariant 0 <= i
//    assert i == 100;
    assert 0 <= i && i >= 100;
    assert i >= 100;
}

method b() {
    var i := 100;
    while 0 < i
        invariant true
//    assert i == 0;
    assert true && 0 >= i;
    assert 0 >= i;
}

method c() {
    var i := 0;
    while i < 97
        invariant 0 <= i <= 99
//    assert i == 99;
    assert 0 <= i <= 99 && i >= 97;
    assert 97 <= i <= 99; // strongest post condition
//    assert -100 <= i <= 10000; // you can put any weaker condition here
}

method d() {
    var i := 22;
    while i % 5 != 0
        invariant 10 <= i <= 100
//    assert i == 55;
    assert 10 <= i <= 100 && i % 5 == 0;
}
