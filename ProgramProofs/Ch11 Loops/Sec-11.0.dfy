// 11.0 Loop Specifications

// you need to get on the train
// (perhaps you are not in Seattle)
// ---
// {{ on the train }}
// ---
// while not in Seattle
//   invariant on the train
// ---
// {{ on the train && in Seattle }}
// ---
// you might need to get off the train

// while homework is not done
//   invariant awake

method example() {
    var x := 2;
    assert 2 % 2 == 0; // invariant
    while x < 50
        invariant x % 2 == 0
    assert 50 <= x && x % 2 == 0; // invariant && not guard
}


// 11.0.4 Variable relations

method example2() {
    var x, y := 0, 0;
    assert 2 * 0 == 3 * 0; // invariant
    while x < 300
        invariant 2 * x == 3 * y
    assert 2*x == 3*y && x >= 300; // invariant && not guard
    calc {
        2*x == 3*y && x >= 300;
        600 <= 2*x == 3*y;
    ==>
        600 <= 3*y;
        200 <= y;
    }
    assert 200 <= y;
}

method example3() {
    var x, y := 0, 191;
    assert 7 * 0 + 191 == 191; // invariant
    while !(0 <= y < 7)
        invariant 7 * x + y == 191
    assert 7*x+y == 191 && 0 <= y < 7; // invariant && not guard
    assert 7*x <= 191 < 7*x+7;
    assert x == 27 && y == 2;
    assert x == 191 / 7 && y == 191 % 7;
}

method example3'() {
    var x, y := 0, 191;
    assert 0 <= 0 && 0 + 191 == 191; // invariant
    while y >= 7
        invariant 0 <= y && 7 * x + y == 191
    assert 0 <= y && 7*x + y == 191 && y < 7; // invariant && not guard
}

method sum() {
    var n, s := 0, 0;
    assert s == 0*(-1)/2; // invariant
    while n != 33
        invariant s == n * (n - 1) / 2
    assert s == n * (n - 1) / 2 && n == 33; // invariant && not guard
    assert s == 33*32/2 && n == 33;
}


// 11.0.5 Loop frames

method sqrt() {
    var r, N := 0, 104;
    while (r+1)*(r+1) <= N
        invariant 0 <= r && r*r <= N
    assert 0 <= r && r*r <= N < (r+1)*(r+1);
}