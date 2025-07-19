datatype myNat = Z | S(myNat)

function myAdd(x: myNat, y: myNat): myNat 
//    ensures myAdd(x, y) == myAdd(y, x)
{
    match x
    case Z => y
    case S(n) => S(myAdd(n, y))
}

lemma myAddComm(x: myNat, y: myNat)
    ensures myAdd(x, y) == myAdd(y, x)
{
    match x
    case Z =>
    case S(n) => calc {
        myAdd(S(n), y);
        S(myAdd(n, y));
        { myAddComm(n, y); }
        myAdd(y, S(n));
    }
}

function myAdd'(x: myNat, y: myNat): myNat 
    ensures myAdd'(x, y) == myAdd'(y, x)
{
    match x
    case Z => y
    case S(n) => S(myAdd'(n, y))
}
