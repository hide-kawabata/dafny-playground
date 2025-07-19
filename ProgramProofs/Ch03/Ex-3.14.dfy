method Outer(a: nat) 
    decreases a
{
    if a != 0 {
        var b := RequiredStudyTime(a - 1);
        Inner(a - 1, b);
    }
}

method Inner(a: nat, b: nat)
    decreases a+1, b
//    decreases a, b
{
    if b == 0 {
        Outer(a);
    } else {
        Inner(a, b - 1);
    }
}

method RequiredStudyTime(c: nat) returns (hours: nat)

// Outer -> Inner : a > a, b
// Inner -> Outer : a+1, b > a
// Inner -> Inner : a+1, b > a, b - 1



