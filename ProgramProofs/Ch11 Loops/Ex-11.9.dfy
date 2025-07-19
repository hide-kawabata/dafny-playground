datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
    match xs
    case Nil => 0
    case Cons(h, t) => 1 + Length(t)
}

method Dubplicate<T>(xs: List<T>) returns(l: List<T>)
    ensures Length(xs) * 2 == Length(l)
{
    l := Nil;
    var len := Length(xs);
    var o := xs;
    while o != Nil
        invariant (len - Length(o)) * 2 == Length(l)
        decreases Length(o)
    {
        var Cons(h, t) := o;
        l := Cons(h, Cons(h, l));
        o := t;
    }
    assert (len - Length(o)) * 2 == Length(l) && o == Nil;
    assert len * 2 == Length(l);
}
