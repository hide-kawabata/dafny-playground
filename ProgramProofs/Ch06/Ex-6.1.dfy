datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
    match xs
    case Nil => 0
    case Cons(_, tail) => 1 + Length(tail)
}

function Snoc<T>(xs: List<T>, y: T): List<T> {
    match xs
    case Nil => Cons(y, Nil)
    case Cons(x, tail) => Cons(x, Snoc(tail, y))
}

lemma {:induction false} LengthSnoc<T>(xs: List<T>, x: T)
    ensures Length(Snoc(xs, x)) == Length(xs) + 1
{
    match xs
    case Nil =>
    case Cons(h, t) => calc {
        Length(Snoc(Cons(h, t), x));
        Length(Cons(h, Snoc(t, x)));
        1 + Length(Snoc(t, x));
        { LengthSnoc(t, x); }
        1 + Length(t) + 1;
        Length(Cons(h, t)) + 1;
    }
}