function Fib(n: int): int
//    decreases n
    requires 0 <= n 
    decreases (n-3)
//    decreases (n-2) //  なぜこれでいいのか？
/*
    n=3のとき：
    Fib(3-2)が呼ばれる．呼ぶ瞬間には termination metircは正．OK．
    Fib(3-1)が呼ばれる．呼ぶ瞬間には termination metircは正．OK．
    n=2のとき：
    Fib(2-2)が呼ばれる．呼ぶ瞬間には termination metircは0．OK．
    Fib(2-1)が呼ばれる．呼ぶ瞬間には termination metircは0．OK．
    n=1のとき：
    再帰呼び出しなし．
    n=0のとき：
    再帰呼び出しなし．
*/
//    decreases (n-3) // なぜこれがダメなのか？
/*
    n=3のとき：
    Fib(3-2)が呼ばれる．呼ぶ瞬間には termination metircは0．OK．
    Fib(3-1)が呼ばれる．呼ぶ瞬間には termination metircは0．OK．
    n=2のとき：
    Fib(2-2)が呼ばれる．呼ぶ瞬間には termination metircは-1．NG．
    Fib(2-1)が呼ばれる．呼ぶ瞬間には termination metircは-1．NG．
*/
//    decreases (n - 100)
{
    if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}