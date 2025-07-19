function F(x: int) : int
//    decreases x-10
//    decreases x-11
{
    if x < 10 then x else F(x - 1)
}