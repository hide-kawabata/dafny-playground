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

lemma {:induction false} BeforeFind<T>(xs: List<T>, y: T, i: nat)
    ensures i < Find(xs, y) ==> At(xs, i) != y

lemma FindAppend<T>(xs: List<T>, ys: List<T>, y: T)
    ensures Find(xs, y) == Length(xs)
        || Find(Append(xs, ys), y) == Find(xs, y)

lemma FindDrop<T>(xs: List<T>, y: T, i: nat)
    ensures i <= Find(xs, y) ==> Find(xs, y) == Find(Drop(xs, i), y) + i

