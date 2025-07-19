method Study(n: nat, h: nat)
//    decreases n, h
//    decreases n * 200 + h
    decreases n * 201 + h
{
    if h != 0 {
        Study(n, h - 1);
    } else if n == 0 {
        // you just finished
    } else {
        var hours := RequiredStudyTime(n - 1);
        Study(n - 1, hours);
    }
}

method RequiredStudyTime(c: nat) returns (hours: nat)
    ensures hours <= 200
{
    hours := 200;
}
