// (a)
// x - 1 > x - 20
// (b)
// x - 1 > x - 20 && x - 1 > 0

function G(x: int): int
//    requires x >= -2
    decreases x - 1
//    decreases x - 2
{
    if 1 <= x then G(x - 20) else x
}
