function J(x: nat, y: nat): int
//    decreases y
//    decreases x
//    decreases y
    decreases x, y
//    decreases y, x
//    decreases x + y
{
    if x == 0 then
        y
    else if y == 0 then
        J(x - 1, 3)
    else
        J(x, y - 1)
}
// J(0, m) --> m
// J(n, 0) --> J(n - 1, 3) ; n ==> n + 2
// J(n, m) --> J(n, m - 1)