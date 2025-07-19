// 11.4 Integer Square Root

method SquareRoot(N: nat) returns (r: nat)
    ensures r * r <= N < (r + 1) * (r + 1)
{
    r := 0;
    while (r + 1) * (r + 1) <= N
        invariant r * r <= N
        decreases N - r
    {
        r := r + 1;
    }
}

method SquareRoot'(N: nat) returns (r: nat)
    ensures r * r <= N < (r + 1) * (r + 1)
{
    r := 0;
    var s := 1;
    while s <= N
        invariant s == (r + 1) * (r + 1)
        invariant r * r <= N
        decreases N - r
    {
        assert s == (r + 1) * (r + 1) && s <= N;
        assert s + 2*r + 3 == (r + 2) * (r + 2);
        s := s + 2*r + 3;
        assert s == (r + 2) * (r + 2);
        r := r + 1;
        assert s == (r + 1) * (r + 1);
    }
    assert s == (r + 1) * (r + 1) && s > N && r * r <= N;
}