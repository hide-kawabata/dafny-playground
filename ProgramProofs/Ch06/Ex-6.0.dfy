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

lemma {:induction false} LengthEq<T>(xs: List<T>)
    ensures Length(xs) == Length'(xs)
{
    match xs
    case Nil =>
    case Cons(h, t) => calc {
        Length(Cons(h, t));
        1 + Length(t);
        { LengthEq(t); }
        1 + Length'(t);
        Length'(Cons(h, t));
    }
}

lemma LengthEq'<T>(xs: List<T>)
    ensures Length(xs) == Length'(xs)
{}
