function F(): int {
    29
}

method M() returns (r: int)
    ensures r > 0
{
    r := 29;
}

method Caller() {
    var a := F();
    var b := M();
    assert a > 0;
    assert b > 0;
}