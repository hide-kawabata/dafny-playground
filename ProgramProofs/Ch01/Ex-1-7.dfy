// Exercise 1.7
method MaxSum(x: int, y: int) returns (s: int, m: int)
    ensures s == x + y
    ensures m >= x && m >= y
{
    s := x + y;
    if x >= y {
        m := x;
    } else {
        m := y;
    }
}
