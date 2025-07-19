datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Length<T>(xs: List<T>): nat {
    match xs
    case Nil => 0
    case Cons(_, tail) => 1 + Length(tail)
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

function Take'<T>(xs: List<T>, n: nat): List<T>
//    requires n <= Length(xs)
{
    if n == 0 then Nil 
    else if n > Length(xs) then xs
    else Cons(xs.head, Take'(xs.tail, n - 1))
}

function Drop'<T>(xs: List<T>, n: nat): List<T>
//    requires n <= Length(xs)
{
    if n == 0 then xs
    else if n > Length(xs) then Nil
    else Drop'(xs.tail, n - 1)
}

lemma TakeTake'Equal<T>(xs: List<T>, n: nat) 
    requires n <= Length(xs)
    ensures Take(xs, n) == Take'(xs, n)
{
/*
    match xs
    case Nil =>
    case Cons(h, t) =>
        if n == 0 {
        } else {
            calc {
                Take(Cons(h, t), n);
                Cons(h, Take(t, n - 1));
                { TakeTake'Equal(t, n - 1); }
                Take'(Cons(h, t), n);
            }
        }
*/
}