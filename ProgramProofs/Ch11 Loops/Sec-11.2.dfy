// 11.2 Loop Termination

// 11.2.0 Termination of quotient modulus

method QM() {
    var x, y := 0, 191;
    while 7 <= y
        invariant 0 <= y && 7 * x + y == 191
        decreases y - 7
    {
        y := y - 7;
        x := x + 1;
    }
}

method QM'() {
    var x, y := 0, 191;
    while 7 <= y
        invariant 0 <= y && 7 * x + y == 191
        invariant 7 <= y // <===== guard is implied by the invariant! this loop never terminates.
    {
        x, y := x - 1, y + 7;
    }
}

