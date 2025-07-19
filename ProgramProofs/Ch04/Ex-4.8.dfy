// Exercises 4.8, 4.9

datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)

datatype Op = Add | Mul

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Eval(e: Expr, env: map<string, nat>): nat 
    decreases 1, true, 1, e
{
    match e
    case Const(c) => c
    case Var(s) => if s in env.Keys then env[s] else 0
//    case Node(op, args) => EvalList(args, op, env)
    case Node(op, args) => EvalList(op, args, env)
}

//function EvalList(args: List<Expr>, op: Op, env: map<string, nat>): nat
function EvalList(op: Op, args: List<Expr>, env: map<string, nat>): nat
    decreases 1, true, 1, args
//    decreases args
{
    match args
    case Nil =>
      (match op case Add => 0 case Mul => 1)
    case Cons(e, tail) =>
//        var v0, v1 := Eval(e, env), EvalList(tail, op, env);
        var v0, v1 := Eval(e, env), EvalList(op, tail, env);
        match op
        case Add => v0 + v1
        case Mul => v0 * v1
}

// Exercise 4.9
predicate GoodEnv(e: Expr, env: map<string, nat>) 
{
    match e
    case Const(c) => true
    case Var(s) => s in env.Keys
    case Node(op, args) => GoodEnvList(args, op, env)
}

predicate GoodEnvList(args: List<Expr>, op: Op, env: map<string, nat>)
{
    match args
    case Nil => true
    case Cons(e, tail) =>
        GoodEnv(e, env) && GoodEnvList(tail, op, env)
}


