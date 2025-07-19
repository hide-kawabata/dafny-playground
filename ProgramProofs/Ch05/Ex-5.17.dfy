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

lemma EvalEnv(e: Expr, n: string, env: map<string, nat>)
    requires n in env.Keys
    ensures Eval(e, env) == Eval(Substitute(e, n, env[n]), env)
{
    match e
    case Const(_) =>
    case Var(_) =>
    case Node(op, args) =>
        // EvalEnvList(args, op, n, env);
        calc {
            Eval(Substitute(e, n, env[n]), env);
            Eval(Substitute(Node(op, args), n, env[n]), env);
            Eval(Node(op, SubstituteList(args, n, env[n])), env);
            EvalList(SubstituteList(args, n, env[n]), op, env);
            { EvalEnvList(args, op, n, env); }
            EvalList(args, op, env);
        }
}

lemma {:induction false} EvalEnvList(
    args: List<Expr>, op: Op, n: string, env: map<string, nat>)
    requires n in env.Keys
    ensures EvalList(args, op, env) == EvalList(SubstituteList(args, n, env[n]), op, env)
{
    // assert env == env[n := env[n]];
    match args
    case Nil =>
    case Cons(e, tail) =>
        // EvalEnv(e, n, env);
        // EvalEnvList(tail, op, n, env);
        match op
        case Add =>
            calc {
                EvalList(SubstituteList(args, n, env[n]), op, env);
                EvalList(Cons(Substitute(e, n, env[n]), SubstituteList(tail, n, env[n])), op, env);
                Eval(Substitute(e, n, env[n]), env) + EvalList(SubstituteList(tail, n, env[n]), op, env);
                { EvalEnv(e, n, env); }
                { EvalEnvList(tail, op, n, env); }
                Eval(e, env) + EvalList(tail, op, env);
                EvalList(Cons(e, tail), op, env);
                EvalList(args, op, env);
        }
        case Mul =>
            calc {
                EvalList(SubstituteList(args, n, env[n]), op, env);
                EvalList(Cons(Substitute(e, n, env[n]), SubstituteList(tail, n, env[n])), op, env);
                Eval(Substitute(e, n, env[n]), env) * EvalList(SubstituteList(tail, n, env[n]), op, env);
                { EvalEnv(e, n, env); }
                { EvalEnvList(tail, op, n, env); }
                Eval(e, env) * EvalList(tail, op, env);
                EvalList(Cons(e, tail), op, env);
                EvalList(args, op, env);
            }
}


lemma EvalEnvDefault(e: Expr, n: string, env: map<string, nat>)
    requires n !in env.Keys
    ensures Eval(e, env) == Eval(Substitute(e, n, 0), env)
{
    match e
    case Const(c) => 
    case Var(s) =>
    case Node(op, args) =>
        EvalEnvDefaultList(args, op, n, env);
}

lemma EvalEnvDefaultList(es: List<Expr>, op: Op, n: string, env: map<string, nat>)
    requires n !in env.Keys
    ensures EvalList(es, op, env) == EvalList(SubstituteList(es, n, 0), op, env)
{
    match es
    case Nil =>
    case Cons(e, tail) =>
        match op
        case Add =>
            calc {
                EvalList(SubstituteList(es, n, 0), op, env);
                EvalList(SubstituteList(Cons(e, tail), n, 0), op, env);
                EvalList(Cons(Substitute(e, n, 0), SubstituteList(tail, n, 0)), op, env);
                Eval(Substitute(e, n, 0), env) + EvalList(SubstituteList(tail, n, 0), op, env);
                { EvalEnvDefault(e, n, env); }
                { EvalEnvDefaultList(tail, op, n, env); }
                Eval(e, env) + EvalList(tail, op, env);
                EvalList(Cons(e, tail), op, env);
                EvalList(es, op, env);
            }
        case Mul =>
            calc {
                EvalList(SubstituteList(es, n, 0), op, env);
                EvalList(SubstituteList(Cons(e, tail), n, 0), op, env);
                EvalList(Cons(Substitute(e, n, 0), SubstituteList(tail, n, 0)), op, env);
                Eval(Substitute(e, n, 0), env) * EvalList(SubstituteList(tail, n, 0), op, env);
                { EvalEnvDefault(e, n, env); }
                { EvalEnvDefaultList(tail, op, n, env); }
                Eval(e, env) * EvalList(tail, op, env);
                EvalList(Cons(e, tail), op, env);
                EvalList(es, op, env);
            }
}



lemma EvalEnvDefault'(e: Expr, n: string, env: map<string, nat>)
    requires n !in env.Keys
    ensures Eval(e, env) == Eval(Substitute(e, n, 0), env)
{
    match e
    case Const(c) => 
    case Var(s) =>
    case Node(op, args) =>
        EvalEnvDefaultList'(args, op, n, env);
}

lemma EvalEnvDefaultList'(es: List<Expr>, op: Op, n: string, env: map<string, nat>)
    requires n !in env.Keys
    ensures EvalList(es, op, env) == EvalList(SubstituteList(es, n, 0), op, env)
{
    match es
    case Nil =>
    case Cons(e, tail) =>
        calc {
            EvalList(SubstituteList(es, n, 0), op, env);
            EvalList(SubstituteList(Cons(e, tail), n, 0), op, env);
            EvalList(Cons(Substitute(e, n, 0), SubstituteList(tail, n, 0)), op, env);
            
            match op 
            case Add =>
                Eval(Substitute(e, n, 0), env) + EvalList(SubstituteList(tail, n, 0), op, env)
            case Mul =>
                Eval(Substitute(e, n, 0), env) * EvalList(SubstituteList(tail, n, 0), op, env);
                
            { EvalEnvDefault'(e, n, env); }
            { EvalEnvDefaultList'(tail, op, n, env); }
            
            match op
            case Add => Eval(e, env) + EvalList(tail, op, env)
            case Mul => Eval(e, env) * EvalList(tail, op, env);
            
            EvalList(Cons(e, tail), op, env);
            EvalList(es, op, env);
        }
}
