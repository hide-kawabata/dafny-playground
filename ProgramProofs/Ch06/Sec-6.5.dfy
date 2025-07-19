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

function Find<T(==)>(xs: List<T>, y: T): nat
    ensures Find(xs, y) <= Length(xs)
{
    match xs
    case Nil => 0
    case Cons(x, tail) => if x == y then 0 else 1 + Find(tail, y)
}

lemma {:induction false} AtFind<T>(xs: List<T>, y: T)
    ensures Find(xs, y) == Length(xs) || At(xs, Find(xs, y)) == y
//     ensures At(xs, Find(xs, y)) == y || Find(xs, y) == Length(xs) // not allowed
{
    var l := Find(xs, y);
    assert l <= Length(xs);
    if l == Length(xs) {
        assert l == Length(xs);
        assert Find(xs, y) == Length(xs);
    } else {
        assert l < Length(xs);
        assert Find(xs, y) < Length(xs);
        assert xs != Nil;
        assert l == Find(xs, y);
        if l == 0 {
            assert xs.head == y;
            calc {
                At(xs, Find(xs, y));
                At(xs, 0);
                At(Cons(xs.head, xs.tail), 0);
                xs.head;
                y;
            }
        } else {
            assert l > 0;
            assert xs.tail != Nil;
            assert xs.head != y;
            calc {
                At(xs, Find(xs, y));
                At(Cons(xs.head, xs.tail), Find(Cons(xs.head, xs.tail), y));
                At(Cons(xs.head, xs.tail), 1+Find(xs.tail, y));
                At(xs.tail, Find(xs.tail, y));
                { AtFind(xs.tail, y); }
                y;
            }
        }
    }
}

predicate Member<T(==)>(xs: List<T>, e: T) {
    match xs
    case Nil => false
    case Cons(h, t) => if h == e then true else Member(t, e)
}

lemma {:induction false} BeforeFind'<T>(xs: List<T>, y: T)
    ensures Find(xs, y) == Length(xs) ==> !Member(xs, y)
{
    if Find(xs, y) == Length(xs) {
        match xs
        case Nil =>
            assert xs == Nil;
            assert Find(xs, y) == 0;
            assert !Member(xs, y);
        case Cons(h, t) =>
            assert xs == Cons(h, t);
            assert h != y;
            BeforeFind'(t, y);
            assert !Member(t, y);
    }
}

lemma {:induction false} BeforeFind<T>(xs: List<T>, y: T, i: nat)
//lemma BeforeFind<T>(xs: List<T>, y: T, i: nat)
    ensures i < Find(xs, y) ==> At(xs, i) != y
//    ensures At(xs, i) == y ==> i >= Find(xs, y) // contrapositive; NG
{
    if i < Find(xs, y) {
        match xs
        case Nil =>
            assert false;
        case Cons(h, t) =>
            if i == 0 {
                calc {
                    At(xs, i);
                    At(Cons(h, t), i);
                    h;
                }
                assert h != y;
            } else {
                assert i < Find(xs, y);
                assert i > 0;
                assert At(xs, i) == At(t, i-1);
                BeforeFind(t, y, i-1);
                assert At(xs, i) != y;
            }
    }
}


lemma {:induction false} FindAppend<T>(xs: List<T>, ys: List<T>, y: T)
    ensures Find(xs, y) == Length(xs)
        || Find(Append(xs, ys), y) == Find(xs, y)
{
    if Find(xs, y) == Length(xs) { // y is not in xs
    } else { // y is in xs; appending something to xs does not change the Find value.
        match xs
        case Nil =>
            assert false;
        case Cons(h, t) =>
            if h == y {
                calc {
                    Find(Append(xs, ys), y);
                    Find(Append(Cons(h, t), ys), y);
                    Find(Cons(h, Append(t, ys)), y);
                    0;
                    Find(xs, y);
                }
            } else {
                calc {
                    Find(Append(xs, ys), y);
                    Find(Append(Cons(h, t), ys), y);
                    Find(Cons(h, Append(t, ys)), y);
                    1 + Find(Append(t, ys), y);
                    { FindAppend(t, ys, y); }
                    1 + Find(t, y);
                    Find(xs, y);
                }
            }
    }
}

lemma {:induction false} FindDrop<T>(xs: List<T>, y: T, i: nat)
    ensures i <= Find(xs, y) ==> Find(xs, y) == Find(Drop(xs, i), y) + i
{
    if i <= Find(xs, y) {
        match xs
        case Nil =>
            assert i == 0;
            assert Find(xs, y) == 0;
            assert Drop(xs, i) == Nil;
            assert Find(Drop(xs, i), y) + i == 0;
        case Cons(h, t) =>
            if i == 0 {
                calc {
                    Find(Drop(xs, i), y) + i;
                    Find(xs, y);
                }
            } else {
                assert i > 0;
                assert Find(t, y) + 1 == Find(xs, y);
                calc {
                    Find(Drop(xs, i), y) + i;
                    Find(Drop(Cons(h, t), i), y) + i;
                    Find(Drop(t, i-1), y) + i;
                }
                FindDrop(t, y, i-1);
                assert Find(t, y) == Find(Drop(t, i-1), y) + (i-1);
                assert Find(t, y) + 1 == Find(Drop(t, i-1), y) + i;
                assert Find(xs, y) == Find(Drop(xs, i), y) + i;
            }
    }
}
