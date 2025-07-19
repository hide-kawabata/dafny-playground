function H(x: int): int 
//  decreases x + 59
    decreases x + 60
//    decreases x + 61
{
    if x < -60 then x else H(x - 1)
}