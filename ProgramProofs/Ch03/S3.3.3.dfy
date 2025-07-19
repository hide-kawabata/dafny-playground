function ExpLess1(n: nat): nat 
//    decreases n, 2
    decreases n
{
    if n == 0 then 0 else ExpLess2(n) + 1
}

function ExpLess2(n: nat): nat
    requires 1 <= n
//    decreases n, 1
    decreases n, "asdf"
//    decreases n, true
{
    2 * ExpLess1(n - 1)
}

// ExpLess1 -> ExpLess2 : n > n, 1
// ExpLess2 -> ExpLess1 : n, 1 > n - 1