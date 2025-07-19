method Triple(x: int) returns (r: int)
    ensures r == 3*x
{
    r := 3 * x;
}

ghost function Average(a: int, b: int): int {
    (a + b) / 2
}

method Triple'(x: int) returns (r: int)
    ensures Average(r, 3*x) == 3*x
    ensures r%3==0
{
    r := 3*x;
}

method Caller(a: int)
{
    var b := Triple(a);
    var b' := Triple'(a);
    assert b == b';
    //....
}
