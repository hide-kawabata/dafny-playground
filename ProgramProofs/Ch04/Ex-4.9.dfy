datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)
datatype Op = Add | Mul
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

predicate GoodEnv(e: Expr, env: map<string, nat>)
{
    match e
    case Const(n) => true
    case Var(s) => if s in env.Keys then true else false
    case Node(op, args) => GoodEnvList(args, env)
}

predicate GoodEnvList(args: List<Expr>, env: map<string, nat>)
{
    match args
    case Nil => true
    case Cons(e, tail) => GoodEnv(e, env) && GoodEnvList(tail, env)
}