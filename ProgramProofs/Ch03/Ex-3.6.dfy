function L(x: int): int 
    decreases 99 - x
//    decreases 98 - x // NG
// 99-xをゼロにする値（x=99）だと，1回再帰するがその向こうでは再帰はない．
{
    if x < 100 then L(x + 1) + 10 else x
}
