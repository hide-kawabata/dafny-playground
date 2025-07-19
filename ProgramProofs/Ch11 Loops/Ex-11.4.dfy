
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

// Exercise: Write a different (but still correct) initializing assignment for the loop above.

method sum'() {
    var n := -1;
    var s := 1;
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


