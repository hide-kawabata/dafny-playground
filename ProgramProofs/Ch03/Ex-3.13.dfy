// Outer -> RequiredStudyTime : not a recursive call
// Outer -> Innter : a > a, b
// Inner -> Outer : a, b > a - 1
// Inner -> Inner : a, b > a, b - 1

method Outer(a: nat)
//    decreases a
{
    if a != 0 {
        var b := RequiredStudyTime(a - 1);
        Inner(a, b);
    }
}

method Inner(a: nat, b: nat)
    requires 1 <= a
//    decreases a, b
{
    if b == 0 {
        Outer(a - 1);
    } else {
        Inner(a, b - 1);
    }
}

method RequiredStudyTime(c: nat) returns (hours: nat)
{
//    hours := RequiredStudyTime(c);
    hours := c+1000;
}
