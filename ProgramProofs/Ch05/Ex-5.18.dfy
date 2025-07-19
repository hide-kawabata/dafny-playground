datatype List<T> = Nil | Cons(head: T, Tail: List<T>)
datatype Op = Add | Mul
datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)

function Eval(e: Expr, env: map<string, nat>): nat {
    match e
    case Const(c) => c
    case Var(s) => if s in env.Keys then env[s] else 0
    case Node(op, args) => EvalList(args, op, env)
}

function EvalList(args: List<Expr>, op: Op, env: map<string, nat>): nat
{
    match args
    case Nil =>
        (match op case Add => 0 case Mul => 1)
    case Cons(e, tail) =>
        var v0, v1 := Eval(e, env), EvalList(tail, op, env);
        match op
        case Add => v0 + v1
        case Mul => v0 * v1
}


function Substitute(e: Expr, n: string, c: nat): Expr
{
    match e
    case Const(_) => e
    case Var(s) => if s == n then Const(c) else e
    case Node(op, args) => Node(op, SubstituteList(args, n, c))
}

function SubstituteList(es: List<Expr>, n: string, c: nat): List<Expr>
{
    match es
    case Nil => Nil
    case Cons(e, tail) =>
        Cons(Substitute(e, n, c), SubstituteList(tail, n, c))
}

lemma SubstituteIdempotent(e: Expr, n: string, c: nat)
    ensures Substitute(Substitute(e, n, c), n, c)
         == Substitute(e, n, c)
{
    match e
    case Const(_) =>
    case Var(_) =>
    case Node(op, args) =>
        calc {
            Substitute(Substitute(e, n, c), n, c);
            Substitute(Substitute(Node(op, args), n, c), n, c);
            Substitute(Node(op, SubstituteList(args, n, c)), n, c);
            Node(op, SubstituteList(SubstituteList(args, n, c), n, c));
            { SubstituteIdempotentList(args, n, c); }
            Node(op, SubstituteList(args, n, c));
            Substitute(Node(op, args), n, c);
            Substitute(e, n, c);            
        }
}

lemma {:induction false} SubstituteIdempotentList(args: List<Expr>, n: string, c: nat)
    ensures SubstituteList(SubstituteList(args, n, c), n, c)
        == SubstituteList(args, n, c)
{
    match args
    case Nil =>
    case Cons(e, tail) =>
        calc {
            SubstituteList(SubstituteList(args, n, c), n, c);
            SubstituteList(SubstituteList(Cons(e, tail), n, c), n, c);
            SubstituteList(Cons(Substitute(e, n, c), SubstituteList(tail, n, c)), n, c);
            Cons(Substitute(Substitute(e, n, c), n, c), SubstituteList(SubstituteList(tail, n, c), n, c));
            { SubstituteIdempotent(e, n, c); }
            { SubstituteIdempotentList(tail, n, c); }
            Cons(Substitute(e, n, c), SubstituteList(tail, n, c));
            SubstituteList(Cons(e, tail), n, c);
            SubstituteList(args, n, c);
        }
}