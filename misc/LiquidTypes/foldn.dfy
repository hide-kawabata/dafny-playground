// P.M. London, M. Kawaguchi, and R. Jahla, Liquid Types, PLDI 2008.
// Example 3

// The original OCaml program in Figure 1.
// let foldn n b f =
//   let rec loop i c =
//     if i < n then loop (i+1) (f i c) else c in
//   loop 0 b

function f0<R>(i: int, c: R, n: int): R
    requires 0 <= i < n // this is what we need to guarantee

// How can we require the initial value of i to be 0 ?
function loop<R>(n: int, i: int, c: R): R
    requires i >= 0 // we try to put the requirement of i >= 0
                    // since i increases
    decreases n - i
{
    if i < n then
        loop(n, i+1, f0(i, c, n))
    else
        c
}

function foldn<R>(n: int, b: R): R
{
    loop(n, 0, b)
}
