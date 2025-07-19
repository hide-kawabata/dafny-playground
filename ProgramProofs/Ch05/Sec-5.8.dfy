datatype List<T> = Nil | Cons(head: T, tail: List<T>)
datatype Op = Add | Mul
datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)


function Eval(e: Expr, env: map<string, nat>): nat 
//    requires GoodEnv(e, env)
//    ensures GoodEnv(e, env)
    decreases 1, true, 1, e
{
    match e
    case Const(c) => c
    case Var(s) => if s in env.Keys then env[s] else 0
//    case Var(s) => env[s]
    case Node(op, args) => EvalList(args, op, env)
}

function EvalList(args: List<Expr>, op: Op, env: map<string, nat>): nat
//    requires GoodEnvList(args, env)
    decreases 1, true, 1, args
//    decreases args
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
lemma EvalSubstitute(e: Expr, n: string, c: nat, env: map<string, nat>)
    ensures Eval(Substitute(e, n, c), env) == Eval(e, env[n := c])
{
    match e
    case Const(_) =>
    case Var(_) =>
    case Node(op, args) =>
        EvalSubstituteList(args, op, n, c, env);
}

lemma {:induction false} EvalSubstituteList(
    args: List<Expr>, op: Op, n: string, c: nat, env: map<string, nat>)
    ensures EvalList(SubstituteList(args, n, c), op, env)
        == EvalList(args, op, env[n := c])
{
    match args
    case Nil =>
    case Cons(e, tail) =>
        EvalSubstitute(e, n, c, env);
        EvalSubstituteList(tail, op, n, c, env);
}

// 5.8.1 O@timization

function Unit(op: Op): nat {
    match op case Add => 0 case Mul => 1
}

function Optimize(e: Expr): Expr {
    if e.Node? then
        var args := OptimizeAndFilter(e.args, Unit(e.op));
        Shorten(e.op, args)
    else
        e // no change
}

function Shorten(op: Op, args: List<Expr>): Expr {
    match args
    case Nil => Const(Unit(op))
    case Cons(e, Nil) => e
    case _ => Node(op, args)
}

function OptimizeAndFilter(es: List<Expr>, unit: nat): List<Expr>
{
    match es
    case Nil => Nil
    case Cons(e, tail) =>
        var e', tail' := Optimize(e), OptimizeAndFilter(tail, unit);
        if e' == Const(unit) then tail' else Cons(e', tail')
}

// termination masures
// Optimize --> OptimizeAndFilter: Node(op, args) --> args
// OptimizeAndFilter --> Optimize: Cons(e, tail) --> e
// OptimizeAndFilter --> OptimizeAndFilter: Cons(e, tail) --> tail

lemma ShortenCorrect(op: Op, args: List<Expr>, env: map<string, nat>)
    ensures Eval(Shorten(op, args), env) == Eval(Node(op, args), env)
//    decreases args
{
    match args
    case Nil => 
    case Cons(h, Nil) =>

    calc {
        Eval(Node(op, Cons(h, Nil)), env);
        EvalList(Cons(h, Nil), op, env);
    }
    // Dafny's verifier can not prove this automatically!!?
/*
     calc {
        Eval(Node(op, Cons(h, Nil)), env); // RHS
    ==  EvalList(Cons(h, Nil), op, env); // def of Eval
    == // def of EvalList
        var v0, v1 := Eval(h, env), EvalList(Nil, op, env);
        match op
        case Add => v0 + v1
        case Mul => v0 * v1;
    ==  // def of EvalList
        var v0, v1 := Eval(h, env), Unit(op);
        match op
        case Add => v0 + v1
        case Mul => v0 * v1;
    ==  // substitute for v0, v1
        match op
        case Add => Eval(h, env) + Unit(op)
        case Mul => Eval(h, env) * Unit(op);
    == // def of Unit in each case
        Eval(h, env);
    == // def of Shorten
        Eval(Shorten(op, Cons(h, Nil)), env); // LHS
    }
*/
    // case Cons(h, t) =>
    case _ =>
}

lemma OptimizeAndFilterCorrect(args: List<Expr>, op: Op, env: map<string, nat>)
    ensures Eval(Node(op, OptimizeAndFilter(args, Unit(op))), env)
        == Eval(Node(op, args), env)
{
    match args
    case Nil =>
    case Cons(h, t) =>
        OptimizeCorrect(h, env);
        OptimizeAndFilterCorrect(t, op, env);
}


lemma OptimizeCorrect(e: Expr, env: map<string, nat>)
    ensures Eval(Optimize(e), env) == Eval(e, env)
{
    match e
    case Const(c) =>
    case Var(n) =>
    case Node(op, args) => 
    calc {
        Eval(Optimize(Node(op, args)), env); // LHS
    ==  Eval(Shorten(op, OptimizeAndFilter(args, Unit(op))), env);
    ==  { ShortenCorrect(op, OptimizeAndFilter(args, Unit(op)), env); }
        Eval(Node(op, OptimizeAndFilter(args, Unit(op))), env);
    ==  { OptimizeAndFilterCorrect(args, op, env); }
        Eval(Node(op, args), env); // RHS
    }
}