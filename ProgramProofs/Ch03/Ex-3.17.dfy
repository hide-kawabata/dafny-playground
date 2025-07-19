// F -> F : false, 998-x > false, 998-(x+2)
// F -> F : true, x > false, 2*y
// F -> F : true, x > true, x - 4

function F(x: nat, y: nat): nat
//    decreases 999 - x, 999 - y
//    decreases x%2==0, 999 - y, false, 999 - x
//    decreases !(1000<=x), !(x%2==0), !(x<6), 999 - x
//    decreases !(1000<=x), (1000<=x)&&!(x%2==0), 999-x, (1000<=x)&&(x%2==0)&&!(x<6), 999-y

//    decreases if (x%2==0) then 998-x else x, !(x%2==0)
    decreases !(x%2==0), if (x%2==0) then 998-x else x
//    decreases !(x%2==0), if (x%2==0) then 997-x else x
{
    if 1000 <= x then
        x + y
    else if x % 2 == 0 then
        F(x + 2, y + 1) // when x is even, x increases
    else if x < 6 then
        F(2 * y, y) // x might change from odd to even
    else
        F(x - 4, y + 3) // when x is odd, x decreases
//        F(x - 8, y + 3) // when x is odd, x decreases
}

/*function f(x: nat):nat 
{
    f(x - 1)
}*/