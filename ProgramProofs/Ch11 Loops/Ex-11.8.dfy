datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
    match xs
    case Nil => 0
    case Cons(h, t) => 1 + Length(t)
}

method Repeat<T>(d: T, n: nat) returns (l: List<T>)
    ensures Length(l) == n
{
    l := Nil;
    var i := 0;
    assert Length(l) == i;
    while i < n
        invariant Length(l) == i
        invariant 0 <= i <= n // needed
        decreases n - i
    {
        assert Length(l) == i && 0 <= i <= n && i < n;
        l := Cons(d, l);
        i := i + 1;
        assert Length(l) == i && 0 <= i <= n;
    }
    assert Length(l) == i && 0 <= i <= n && i == n;
}