function F(n: nat): nat
    decreases n, 2
{
    if n == 0 then 1 else n - M(F(n - 1))
}

function M(n: nat): nat
    decreases n, 1
{
    if n == 0 then 0 else n - F(M(n - 1))
}
/*
method Check(n: nat) returns (x: nat, y: nat)
    ensures x == y
{
    x := F(n);
    y := M(n);
}
*/
// F -> F : n, 2 > n - 1, 2
// F -> M : n, 2 > ?, 1
// M -> M : n, 1 > n - 1, 1
// M -> F : n, 1 > ?, 2

// F(1) = 1 - M(F(0))
//      = 1 - M(1)
//      = 1 - (1 - F(M(0)))
//      = 1 - (1 - F(0))
//      = 1 - (1 - 1)
//      = 1
// F(2) = 2 - M(F(1))
//      = 2 - M(1)
//      = 2 - (1 - 1)
//      = 2
// F(3) = 3 - M(F(2))
//      = 3 - M(2)
//      = 3 - (2 - F(M(1)))
//      = 3 - (2 - F(0))
//      = 3 - (2 - 1)
//      = 2
