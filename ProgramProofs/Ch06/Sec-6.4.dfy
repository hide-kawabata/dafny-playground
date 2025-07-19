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

method TestLengthAtDrop()
{
    var l1 := Cons(1, Cons(2, Nil));
    assert Length(l1) == 2;
    assert At(l1, 0) == 1;
    assert At(l1, 1) == 2;
    assert Drop(l1, 0).Cons?;
    assert Drop(l1, 1).Cons?;
    assert Length<nat>(Nil) == 0;
}

lemma {:induction false} L0<T>(xs: List<T>, i: nat)
    requires i < Length(xs)
    ensures xs.Cons?
{
    assert i < Length(xs);
    match xs
    case Nil =>
        assert false; // this path can be ignored!
    case Cons(h, t) =>
        assert xs == Cons(h, t);
        assert xs.Cons?;
}

lemma {:induction false} LengthDropHead<T>(xs: List<T>, i: nat)
//lemma LengthDropHead<T>(xs: List<T>, i: nat)
    requires i < Length(xs)
    ensures Drop(xs, i).Cons?
{
    assert i < Length(xs);
    assert xs != Nil;
    if i == 0 {
        assert xs.Cons?; // because Length(xs) > 0
        assert Drop(xs, i) == xs; // because Drop(xs, 0) == xs
        assert Drop(xs, i).Cons?; // because xs.Cons? is true
    } else {
//        LengthDropHead(xs.tail, i-1); // this is essential
        assert i >= 1; // because i is a nat and i > 0
        assert Length(xs) >= 2; // because i < Length(xs) and i > 0
        assert xs.Cons?;
        var h0 := xs.head;
        var t0 := xs.tail;
        assert t0 != Nil; // because Length(xs) >= 2;
        assert t0.Cons?;
        LengthDropHead(t0, i-1); // IH
        assert Drop(t0, i-1).Cons?; // the information obtained by IH
        assert Drop(t0, i-1) == Drop(xs, i);
        assert Drop(xs, i).Cons?; // because Drop(xs, i) == Drop(t0, i-1)
/*
        // the following is essentially the same as above
        match xs
//        case Nil => // you can skip this part because we know xs != Nil
//            assert false;
        case Cons(h, t) =>
            assert xs == Cons(h, t);
            assert t != Nil;
            assert t.Cons?;
            assert i > 0;
            LengthDropHead(t, i-1);
            assert Drop(t, i-1).Cons?;
            assert Drop(xs, i).Cons?;
*/
    }
}

lemma {:induction false} AtDropHead'<T>(xs: List<T>, i: nat)
//lemma AtDropHead'<T>(xs: List<T>, i: nat)
    requires i < Length(xs)
    requires Drop(xs, i).Cons? // added requirement which is implied from i < Length(xs)
    ensures At(xs, i) == Drop(xs, i).head
//    ensures Drop(xs, i).Cons? && At(xs, i) == Drop(xs, i).head
{
    assert xs.Cons?;
    if i == 0 {
        assert Drop(xs, i) == xs;
        assert At(xs, i) == xs.head;
    } else {
        assert i >= 1;
        assert Length(xs) >= 2;
        assert Drop(xs, i) == Drop(xs.tail, i-1);
        assert At(xs, i) == At(xs.tail, i-1);
        AtDropHead'(xs.tail, i-1); // IH
    }
}

// Omitting Drop(xs, i).Cons? (or equivalents) as a requirement is not allowed
// even though the condition i < Length(xs) implies Drop(xs, i).Cons?.
// Why?????
// (Maybe invocations of methods/functions are not allowed before making sure that they are actually invocable)
// (in other words, the expression Drop(xs, i).head is not well-defined)
lemma {:induction false} AtDropHead<T>(xs: List<T>, i: nat)
//lemma AtDropHead<T>(xs: List<T>, i: nat)
    requires i < Length(xs)
//    ensures At(xs, i) == Drop(xs, i).head // NG
    ensures Drop(xs, i).Cons? && At(xs, i) == Drop(xs, i).head // OK: use after check ?
//    ensures At(xs, i) == Drop(xs, i).head && Drop(xs, i).Cons? // this is not allowed!!
//     ensures Drop(xs, i).Cons? ==> At(xs, i) == Drop(xs, i).head // this is OK but the meaning is different
{
    LengthDropHead(xs, i);
    assert Drop(xs, i).Cons?; // because LengthDropHead(xs, i) holds
    if i == 0 {
        assert At(xs, i) == xs.head;
        assert Drop(xs, i) == xs;
    } else {
        assert At(xs, i) == At(xs.tail, i-1);
        assert Drop(xs, i) == Drop(xs.tail, i-1);
        AtDropHead(xs.tail, i-1);
    }
}


method TestAtDropHead'<T>(xs: List<T>, e: T, i: nat)
    requires i < Length(xs)
{
//    LengthDropHead(xs, i);
//    assert Drop(xs, i).Cons?;
//    AtDropHead'(xs, i);
    AtDropHead(xs, i); // this can be used without "calling" LengthDropHead because AtDropHead calls it itself
    // It seems that LengthDropHead (or an equivalent) must be shown anyway.
    // You may say that AtDropHead is better than AtDropHead' because the formar requires less to use it.

//    var xs2 := Cons(e, xs);
//    AtDropHead'(xs2, 0);
//    AtDropHead(xs2, 0);
}

lemma AppLen<T>(xs: List<T>, ys: List<T>) 
    ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
{
}

lemma {:induction false} AtAppend<T>(xs: List<T>, ys: List<T>, i: nat)
//lemma AtAppend<T>(xs: List<T>, ys: List<T>, i: nat)
    requires i < Length(Append(xs, ys))
//    ensures i - Length(xs) < Length(ys) // this might be required (*)
    ensures Length(Append(xs, ys)) == Length(xs) + Length(ys) // or, this (**)
    ensures At(Append(xs, ys), i)
        == if i < Length(xs) then At(xs, i)
            else At(ys, i - Length(xs))
{
    AppLen(xs, ys); // this one line is enough to show (*) and (**)
/*    match xs
    case Nil =>
        calc {
            Length(Append(xs, ys));
            Length(xs) + Length(ys);
        }
    case Cons(h, t) =>
        calc {
            Length(Append(xs, ys));
            Length(Append(Cons(h, t), ys));
            Length(Cons(h, Append(t, ys)));
            1 + Length(Append(t, ys));
            { AppLen(t, ys); }
            Length(xs) + Length(ys);
        }
*/
    match xs
    case Nil =>
        assert Append(xs, ys) == ys;
        assert At(Append(xs, ys), i) == At(ys, i);
        assert i - Length(xs) == i;
        assert At(Append(xs, ys), i) == At(ys, i - Length(xs));
    case Cons(h, t) =>
        if i == 0 {
            assert Length(xs) > 0;
            calc {
                At(Append(xs, ys), 0);
                At(Append(Cons(h, t), ys), 0);
                At(Cons(h, Append(t, ys)), 0);
                h;
                At(xs, 0);
            }
        } else if i < Length(xs) {
            calc {
                At(Append(xs, ys), i);
                At(Append(Cons(h, t), ys), i);
                At(Cons(h, Append(t, ys)), i);
                At(Append(t, ys), i-1);
                { AtAppend(t, ys, i-1); }
                if i-1 < Length(t) then At(t, i-1) else At(ys, i-1-Length(t));
                At(t, i-1);
                At(xs, i);
            }
        } else {
            assert i >= Length(xs);
            calc {
                At(Append(xs, ys), i);
                At(Append(Cons(h, t), ys), i);
                At(Cons(h, Append(t, ys)), i);
                At(Append(t, ys), i-1);
                { AtAppend(t, ys, i-1); }
                if i-1 < Length(t) then At(t, i-1) else At(ys, i-1-Length(t));
                At(ys, i-1-Length(t));
                At(ys, i-Length(xs));
            }
        }
}

// this proof can be refactored a lot (see Ex-6.12.dfy)
