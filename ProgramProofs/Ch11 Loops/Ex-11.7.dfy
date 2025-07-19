method UpWhileLess(N: int) returns (i: int)
    requires 0 <= N
    ensures i == N
{
    i := 0;
    while i < N 
        invariant 0 <= i <= N
        decreases N - i
    {
        assert 0 <= i <= N && i < N;
        assert 0 <= i+1 <= N && i < N;
        i := i + 1;
        assert 0 <= i <= N;
    }
    assert 0 <= i <= N && i >= N;
    assert i == N;
}

method UpWhileNotEqual(N: int) returns (i: int)
    requires 0 <= N
    ensures i == N
{
    i := 0;
    while i != N
        invariant i <= i <= N
        decreases N - i
    {
        i := i + 1;
    }
    assert 0 <= i <= N && i == N;
}

method DownWhileNotEqual(N: int) returns (i: int)
    requires 0 <= N
    ensures i == 0
{
    i := N;
    while i != 0
        invariant 0 <= i <= N
        decreases i
    {
        i := i - 1;
    }
    assert 0 <= i <= N && i == 0;
}

method DownWhileGreater(N: int) returns (i: int)
    requires 0 <= N
    ensures i == 0
{
    i := N;
    while 0 < i
        invariant 0 <= i <= N
        decreases i
    {
        i := i - 1;
    }
    assert 0 <= i <= N && 0 >= i;
    assert i == 0;
}
