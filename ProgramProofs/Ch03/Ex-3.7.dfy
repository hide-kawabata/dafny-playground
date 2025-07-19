function G(n: nat): nat
//    decreases n
    decreases n - 1
{
    if n == 0 then 0 else n - G(G(n - 1))
}

// function G'(n: nat): nat
// {
//     if n == 0 then 0 else n - G'(G''(n - 1))
// }

// function G''(n: nat): nat
// {
//     if n == 0 then 0 else n - G''(G'(n - 1))
// }

method G2(n: nat) returns (r: nat)
//    decreases n
    ensures 0 <= r <= n
{
    if n == 0  {
        r := 0;
    } else {
        var tmp := G2(n - 1); // 0 <= tmp = G2(n - 1) <= n - 1
        var tmp2 := G2(tmp); // 0 <= G2(tmp) <= n - 1
        r := n - tmp2;
    }
}

// method X() returns (r: nat)
//     ensures r > 0
// {
//     if true > 19 {
// //    if true,5 > false {
//         r := 1;
//     } else {
//         r := 0;
//     }

// }