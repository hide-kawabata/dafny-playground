function I(x: nat, y: nat): int
//    decreases x + y - 3
//    decreases x + y
//    decreases x + y - 2
    decreases y, x
//    decreases x * y * 5
{
    if x == 0 || y == 0 then
        12
    else if x % 2 == y % 2 then
        I(x - 1, y)
    else
        I(x, y - 1)
}