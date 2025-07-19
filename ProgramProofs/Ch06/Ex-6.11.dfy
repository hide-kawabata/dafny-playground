// 6.3 Take and Drop
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

lemma LengthSnoc<T>(xs: List<T>, x: T)
    ensures Length(Snoc(xs, x)) == Length(xs) + 1
{   
}

function Append<T>(xs: List<T>, ys: List<T>): List<T> {
    match xs
    case Nil => ys
    case Cons(x, tail) => Cons(x, Append(tail, ys))
}

lemma {:induction false} LengthAppend<T>(xs: List<T>, ys: List<T>)
    ensures Length(Append(xs, ys)) == Length(xs) + Length(ys)
{
    match xs
    case Nil =>
    case Cons(h, t) => calc {
        Length(Append(Cons(h, t), ys));
        Length(Cons(h, Append(t, ys)));
        1 + Length(Append(t, ys));
        { LengthAppend(t, ys); }
        Length(Cons(h, t)) + Length(ys);
    }
}

function {:induction false} Append'<T>(xs: List<T>, ys: List<T>): List<T> 
    ensures Length(Append'(xs, ys)) == Length(xs) + Length(ys)
{
    match xs
    case Nil => ys
    case Cons(x, tail) => Cons(x, Append'(tail, ys))
}

// 6.2.0 
lemma AppendNil<T>(xs: List<T>)
    ensures Append(xs, Nil) == xs
{
}

lemma AppendAssociative<T>(xs: List<T>, ys: List<T>, zs: List<T>)
    ensures Append(Append(xs, ys), zs) == Append(xs, Append(ys, zs))
{
}

function Take<T>(xs: List<T>, n: nat): List<T>
    requires n <= Length(xs)
{
    if n == 0 then Nil else Cons(xs.head, Take(xs.tail, n - 1))
}

function Drop<T>(xs: List<T>, n: nat): List<T>
    requires n <= Length(xs)
{
    if n == 0 then xs else Drop(xs.tail, n - 1)
}

lemma AppendTakeDrop<T>(xs: List<T>, n: nat)
    requires n <= Length(xs)
    ensures Append(Take(xs, n), Drop(xs, n)) == xs
{
}

lemma {:induction false} TakeDropAppend<T>(xs: List<T>, ys: List<T>)
    ensures Take(Append'(xs, ys), Length(xs)) == xs
    ensures Drop(Append'(xs, ys), Length(xs)) == ys
{
    match xs
    case Nil =>
    case Cons(h, t) => {
//        calc {
//            Take(Append'(Cons(h, t), ys), Length(Cons(h, t)));
//            Take(Cons(h, Append'(t, ys)), 1 + Length(t));
//            Cons(h, Take(Append'(t, ys), Length(t)));
            { TakeDropAppend(t, ys); }
//            xs;
//        }
//        calc {
//            Drop(Append'(Cons(h, t), ys), Length(Cons(h, t)));
//            Drop(Cons(h, Append'(t, ys)), 1 + Length(t));
//            Drop(Append'(t, ys), Length(t));
//            { TakeDropAppend(t, ys); }
//            ys;
//        }
    }
}

function Take'<T>(xs: List<T>, n: nat): List<T>
//    requires n <= Length(xs)
{
    if n == 0 then Nil 
    else if n > Length(xs) then xs
    else Cons(xs.head, Take'(xs.tail, n - 1))
}

// Append does not ensure some property held for the returned values.
// If you use Append instead of Append', you need to ensure that the precondition for calling Take, i.e n <= Length(xs). 
// Or else, you need to use a liberal version of Take (Take').
lemma TakeDropAppend'<T>(xs: List<T>, ys: List<T>)
    ensures Take'(Append(xs, ys), Length(xs)) == xs
    ensures Drop(Append(xs, ys), Length(xs)) == ys
{
}