// 6.6 List Reversal

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

function Snoc<T>(xs: List<T>, y: T): List<T> {
    match xs
    case Nil => Cons(y, Nil)
    case Cons(x, tail) => Cons(x, Snoc(tail, y))
}

function SlowReverse<T>(xs: List<T>): List<T> {
    match xs
    case Nil => Nil
    case Cons(x, tail) => Snoc(SlowReverse(tail), x)
}

lemma {:induction false} LengthSnoc<T>(xs: List<T>, y: T)
    ensures Length(Snoc(xs, y)) == Length(Cons(y, xs))
{
    match xs
    case Nil =>
    case Cons(h, t) =>
        calc {
            Length(Snoc(xs, y));
            Length(Snoc(Cons(h, t), y));
            Length(Cons(h, Snoc(t, y)));
            1 + Length(Snoc(t, y));
            { LengthSnoc(t, y); }
            1 + Length(Cons(y, t));
            Length(Cons(y, xs));
        }
}
lemma {:induction false} LengthSlowReverse<T>(xs: List<T>)
    ensures Length(SlowReverse(xs)) == Length(xs)
{
    match xs
    case Nil =>
    case Cons(h, t) =>
        calc {
            Length(SlowReverse(xs));
            Length(SlowReverse(Cons(h, t)));
            Length(Snoc(SlowReverse(t), h));
            { LengthSnoc(SlowReverse(t), h); }
            Length(SlowReverse(t)) + 1;
            { LengthSlowReverse(t); }
            Length(t) + 1;
            Length(xs);
        }
}

function ReverseAux<T>(xs: List<T>, acc: List<T>) : List<T>
{
    match xs
    case Nil => acc
    case Cons(x, tail) => ReverseAux(tail, Cons(x, acc))
}

lemma {:induction false} AppendSnoc<T>(xs: List<T>, ys: List<T>, z: T)
    ensures Append(Snoc(xs, z), ys) == Append(xs, Cons(z, ys))
{
    match xs
    case Nil =>
    case Cons(h, t) =>
        calc {
            Append(Snoc(xs, z), ys);
            Append(Snoc(Cons(h, t), z), ys);
            Append(Cons(h, Snoc(t, z)), ys);
            Cons(h, Append(Snoc(t, z), ys));
            { AppendSnoc(t, ys, z); }
            Cons(h, Append(t, Cons(z, ys)));
            Append(Cons(h, t), Cons(z, ys));
            Append(xs, Cons(z, ys));
        }
}


lemma {:induction false} ReverseAuxSlowCorrect<T>(xs: List<T>, acc: List<T>)
    ensures ReverseAux(xs, acc) == Append(SlowReverse(xs), acc)
{
    match xs
    case Nil =>
    case Cons(x, tail) =>
        calc { // LHS
            Append(SlowReverse(xs), acc);
            Append(SlowReverse(Cons(x, tail)), acc);
            Append(Snoc(SlowReverse(tail), x), acc);
            { AppendSnoc(SlowReverse(tail), acc, x); }
            Append(SlowReverse(tail), Cons(x, acc));
        }
        calc { // RHS
            ReverseAux(xs, acc);
            ReverseAux(Cons(x, tail), acc);
            ReverseAux(tail, Cons(x, acc));
        }
        ReverseAuxSlowCorrect(tail, Cons(x, acc));
        assert Append(SlowReverse(tail), Cons(x, acc)) == ReverseAux(tail, Cons(x, acc));
}

function Reverse<T>(xs: List<T>): List<T> {
    ReverseAux(xs, Nil)
}

lemma AppNil<T>(xs: List<T>)
    ensures Append(xs, Nil) == xs
{}

lemma Hoge<T>(ys: List<T>, ts: List<T>, x: T)
    ensures Snoc(Append(ys, ts), x) == Append(ys, Snoc(ts, x))
{}

lemma AppRev<T>(xs: List<T>, ys: List<T>)
    ensures SlowReverse(Append(xs, ys)) == Append(SlowReverse(ys), SlowReverse(xs))
{
    match xs
    case Nil => calc {
        SlowReverse(Append(xs, ys));
        SlowReverse(ys);
        { AppNil(SlowReverse(ys)); }
        Append(SlowReverse(ys), Nil);
    }
    case Cons(h, t) => calc {
        SlowReverse(Append(xs, ys));
        SlowReverse(Append(Cons(h, t), ys));
        SlowReverse(Cons(h, Append(t, ys)));
        Snoc(SlowReverse(Append(t, ys)), h);
        { AppRev(t, ys); }
        Snoc(Append(SlowReverse(ys), SlowReverse(t)), h);
        { Hoge(SlowReverse(ys), SlowReverse(t), h); }
        Append(SlowReverse(ys), Snoc(SlowReverse(t), h));
        Append(SlowReverse(ys), SlowReverse(Cons(h, t)));
        Append(SlowReverse(ys), SlowReverse(xs));        
    }

}

lemma {:induction false} ReverseCorrect<T>(xs: List<T>)
    ensures Reverse(xs) == SlowReverse(xs)
{
    calc {
        Reverse(xs);
        ReverseAux(xs, Nil);
        { ReverseAuxSlowCorrect(xs, Nil); }
        Append(SlowReverse(xs), Nil);
        { AppNil(SlowReverse(xs)); }    
        SlowReverse(xs);
    }
/*
    match xs
    case Nil =>
    case Cons(h, t) =>
        calc {
            Reverse(xs);
            ReverseAux(xs, Nil);
            { ReverseAuxSlowCorrect(xs, Nil); }
            Append(SlowReverse(xs), Nil);
            Append(SlowReverse(Cons(h, t)), Nil);
            Append(Snoc(SlowReverse(t), h), Nil);
            { ReverseCorrect(t); }
            Append(Snoc(Reverse(t), h), Nil);
            { AppendSnoc(Reverse(t), Nil, h); }
            Append(Reverse(t), Cons(h, Nil));
            { ReverseCorrect(t); }
            Append(SlowReverse(t), Cons(h, Nil));
            { AppRev(Cons(h, Nil), t); }
            SlowReverse(Append(Cons(h, Nil), t));
            SlowReverse(Cons(h, t));
            SlowReverse(xs);
        }
*/
}

lemma ReverseAuxCorrect<T>(xs: List<T>, acc: List<T>)
    ensures ReverseAux(xs, acc) == Append(Reverse(xs), acc)
{
    ReverseCorrect(xs);
    ReverseAuxSlowCorrect(xs, acc);
}

lemma LengthReverse<T>(xs: List<T>)
    ensures Length(Reverse(xs)) == Length(xs)
{
    ReverseCorrect(xs);
    LengthSlowReverse(xs);
}
