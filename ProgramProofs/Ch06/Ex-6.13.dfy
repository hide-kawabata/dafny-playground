// 6.5 Find

datatype List<T> = Nil | Cons(head: T, tail: List <T>)

function Length<T>(l: List<T>): nat
{
    match l
    case Nil => 0
    case Cons(h, t) => 1 + Length(t)
}

function At<T>(xs: List<T>, i: nat): T
    requires i < Length(xs)
{
    if i == 0 then xs.head else At(xs.tail, i - 1)
}

function Drop<T>(l: List<T>, i: nat): List<T>
//    requires i < Length(l)
{
    match l
    case Nil => Nil
    case Cons(h, t) => if i == 0 then l else Drop(t, i - 1)

//    if i == 0 then l else Drop(l.tail , i - 1)
}

function Append<T>(xs: List<T>, ys: List<T>): List <T>
{
    match xs
    case Nil => ys
    case Cons(h, t) => Cons(h, Append(t, ys))
}

//function Find<T(==)>(xs: List<T>, y: T): nat
function Find<T>(xs: List<T>, y: T): nat // This causes an error
    ensures Find(xs, y) <= Length(xs)
{
    match xs
    case Nil => 0
    case Cons(x, tail) => if x == y then 0 else 1 + Find(tail, y)
}

