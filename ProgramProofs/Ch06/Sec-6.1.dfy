// 6.1 Length
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
    match xs
    case Nil => 0
    case Cons(_, tail) => 1 + Length(tail)
}

function Length'<T>(xs: List<T>): nat {
    if xs == Nil then 0 else 1 + Length'(xs.tail)
}

function Snoc<T>(xs: List<T>, y: T): List<T> {
    match xs
    case Nil => Cons(y, Nil)
    case Cons(x, tail) => Cons(x, Snoc(tail, y))
}

lemma LengthSnoc<T>(xs: List<T>, x: T)
    ensures Length(Snoc(xs, x)) == Length(xs) + 1
{
    
}