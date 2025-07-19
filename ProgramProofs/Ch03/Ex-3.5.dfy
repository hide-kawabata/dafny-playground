function K(x: nat, y: nat, z: nat): int
//    decreases x, y, z // OK
//    decreases x, z, y // OK
//    decreases y, x, z // OK
//    decreases y, z, x // NG
//    decreases z, x, y // NG
//    decreases z, y, z // NG
// 増えるものを高い優先順位にしてはならない
// 減りにくいものを優先すべし
    decreases x, z
// y はどうでもよい！？
{
    if x < 10 || y < 5 then
        x + y
    else if z == 0 then
        K(x - 1, y+10000, 1000)
    else
        K(x, y - 1, z - 1)
}
