// Exercises 4.10

datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)

datatype Op = Add | Mul

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Eval(e: Expr, env: map<string, nat>): nat 
    requires GoodEnv(e, env)
//    ensures GoodEnv(e, env)
    decreases 1, true, 1, e
{
    match e
    case Const(c) => c
//    case Var(s) => if s in env.Keys then env[s] else 0
    case Var(s) => env[s]
//    case Node(op, args) => EvalList(args, op, env)
    case Node(op, args) => EvalList(op, args, env)
}

//function EvalList(args: List<Expr>, op: Op, env: map<string, nat>): nat
function EvalList(op: Op, args: List<Expr>, env: map<string, nat>): nat
    requires GoodEnvList(args, env)
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
ghost predicate GoodEnv(e: Expr, env: map<string, nat>) 
{
    match e
    case Const(c) => true
//    case Var(s) => if s in env.Keys then true else false
    case Var(s) => s in env.Keys
    case Node(op, args) => GoodEnvList(args, env)
}

ghost predicate GoodEnvList(args: List<Expr>, env: map<string, nat>)
{
    match args 
   case Nil => true
    case Cons(e, tail) =>
        GoodEnv(e, env) && GoodEnvList(tail, env)
}

method TestEval() {
    var m0: map<string, nat> := map[];
    var m: map<string, nat> := map["x" := 3, "y" := 4];
    var e := Const(3);
    var n := Eval(e, m);
    var n0 := Eval(e, m0);
    var ev := Var("v");
//    var nv := Eval(ev, m);
    var nv := Eval(ev, m["v" := 8]);
//    var mv: map<string, nat> := map["v" := 8];
//    var nv := Eval(ev, mv);
//    m := m["v" := 8];
//    var nv := Eval(ev, m);
}

/*
method TestEval2(m: map<string, nat>)
    reads m
{
    var e := Var("v");
    var v := Eval(e, m);
}
*/

// Can't we generate predicates like GoodEnv and GoodEnvLIst ?
