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

lemma {:induction false} AppendTakeDrop<T>(xs: List<T>, n: nat)
    requires n <= Length(xs)
    ensures Append(Take(xs, n), Drop(xs, n)) == xs
{   
    match xs
    case Nil =>
    case Cons(h, t) =>
        if n == 0 {
        } else {
            calc {
                Append(Take(Cons(h, t), n), Drop(Cons(h, t), n));
                Append(Cons(h, Take(t, n - 1)), Drop(t, n - 1));
                Cons(h, Append(Take(t, n - 1), Drop(t, n - 1)));
                { AppendTakeDrop(t, n - 1); }
                xs;
            }
        }
}

lemma TakeDropAppend<T>(xs: List<T>, ys: List<T>)
    ensures Take(Append'(xs, ys), Length(xs)) == xs
    ensures Drop(Append'(xs, ys), Length(xs)) == ys
{
}