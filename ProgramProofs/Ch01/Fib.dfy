method M(n: nat) returns (r: nat) {
    if {
        case true => r := n;
        case true => r := M(n + 1);
    }
}

function F(n: nat) : nat {
    if n > 2 then n - 1 else n
}


function Fib(n: nat): nat 
    decreases n*2+1
{
   if n < 2 then n else
    Fib(n - 2) + Fib(n - 1)
}
