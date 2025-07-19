datatype List<T> = Nil | Cons(head: T, Tail: List<T>)

function append<T>(e: T, l: List<T>): List<T>
{
    match l
    case Nil => Cons(e, Nil)
    case Cons(h, t) => Cons(h, append(e, t))
}

method testList()
{
    var l123 := Cons(1, Cons(2, Cons(3, Nil)));
    var l12 := Cons(1, Cons(2, Nil));
    assert append(3, l12) == l123;
}

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

method testEval()
{
    var e1 := Node(Add, Nil);
    var e2 := Node(Add, Cons(Const(3), Nil));
    assert Eval(e1, map[]) == 0;
    assert Eval(e1, map["v" := 5]) == 0;
    assert Eval(e2, map[]) == 3;
}

function PartiallyEvaluate(e: Expr): Expr 
{
    match e
    case Const(_) => e // eg. 3 --> 3
    case Var(_) => e // eg. v --> v
    case Node(op, args) => // eg. (+ [1 2 v 3]) --> (+ [6 v])
        var args' := PartiallyEvaluateList(op, args);
/*
        match args' {
        case Nil => // [] --> 0 or 1
            match op {case Add => Const(0) case Mul => Const(1)}
        case Cons(h, Nil) => h // [v] --> v, [3] --> 3
        case Cons(h, t) => Node(op, args') // [6 v] --> (+ [6 v])
        }
*/
        Node(op, args')
}

// (+ [1 2 v 3]) --> [6 v]
// (+ [1 2 v (* [4 y 3])]) --> [3 v (* [12 y])]
function PartiallyEvaluateList(op: Op, args: List<Expr>): List<Expr> 
    decreases args, 1
{
    var u := match op case Add => 0 case Mul => 1;
    var (c, l) := PEL(op, args, u, Nil);
    Cons(Const(c), l)
}

// PEL(+, [1 2 v 3], 0, []) --> (6, [v])
// PEL(+, [1 2 v (* [4 y 3])], 0 []) --> (3, [v (* [12 y])])
function PEL(op: Op, args: List<Expr>, v: nat, res: List<Expr>): (nat, List<Expr>)
    decreases args, 0
{
    match args
    case Nil => (v, res)
    case Cons(h, t) => 
        match h {
        case Const(n) => 
            match op {
            case Add => PEL(op, t, n+v, res)
            case Mul => PEL(op, t, n*v, res)
            }
        case Var(n) => PEL(op, t, v, append(h, res))
        case Node(op', args') =>
            var h' := PartiallyEvaluate(h);
            PEL(op, t, v, append(h', res))
        }
}


method test()
{
    var p := (1, "abc");
    assert p.0 == 1;
    assert p.1 == "abc";
    var e := Node(Add, Cons(Const(1),
                       Cons(Const(2),
                       Cons(Var("v"),
                       Cons(Node(Mul, Cons(Const(4),
                                      Cons(Var("y"),
                                      Cons(Const(3),
                                      Nil)))),
                       Nil)))));
    var e' := Node(Add, Cons(Const(3),
                        Cons(Var("v"),
                        Cons(Node(Mul, Cons(Const(12),
                                       Cons(Var("y"),
                                       Nil))),
                        Nil))));
    assert e' == PartiallyEvaluate(e);
    var e01 := Node(Mul, Cons(Const(4),
                         Cons(Var("y"),
                         Cons(Var("z"),
                         Cons(Const(3),
                         Nil)))));
    var e02 := Node(Mul, Cons(Var("y"),
                         Cons(Const(3),
                         Cons(Const(4),
                         Cons(Var("z"),
                         Nil)))));
    var e01' := Node(Mul, Cons(Const(12),
                          Cons(Var("y"),
                          Cons(Var("z"),
                          Nil))));
    assert e01' == PartiallyEvaluate(e01);
    assert e01' == PartiallyEvaluate(e02);
}

/*
lemma PartiallyEvaluateListCorrectAdd(
        args: List<Expr>, env: map<string, nat>)
    ensures EvalList(args, Add, env)
         == Eval(Node(Add, PartiallyEvaluateList(Add, args)), env)
{
    match args
    case Nil =>
    case Cons(h, t) =>
        calc {
            Eval(Node(Add, PartiallyEvaluateList(Add, Cons(h, t))),
                 env);
            EvalList(PartiallyEvaluateList(Add, Cons(h, t)), Add, env);
            // var (c, l) := PEL(Add, Cons(h, t), 0, Nil);
            // Cons(Const(c), l);
        }
}
*/

lemma PELCorrect(op: Op, args: List<Expr>, v: nat, res: List<Expr>, env: map<string, nat>)
    var (c, l) := PEL(op: Op, args: List<Expr>, v: nat, res: List<Expr>);
    Eval(Node(op, args), env)
     == Eval(Node(op, Cons(Const(c), l)), env)


lemma PartiallyEvaluateListCorrect(op: Op, args: List<Expr>, env: map<string, nat>)
    ensures EvalList(PartiallyEvaluateList(op, args), op, env)
    == EvalList(args, op, env)
{
    match args
    case Nil =>
    case Cons(h, t) =>
        calc {
            EvalList(PartiallyEvaluateList(op, args), op, env);
            EvalList(PartiallyEvaluateList(op, Cons(h, t)), op, env);
            match op
            case Add =>
                var (c, l) := PEL(Add, args, 0, Nil);
                Cons(Const(c), l)
            case Mul =>
                var (c, l) := PEL(Mul, args, 1, Nil);
                Cons(Const(c), l)
        }
}

lemma PartiallyEvaluateCorrect(e: Expr, env: map<string, nat>)
    ensures Eval(e, env) == Eval(PartiallyEvaluate(e), env)
{
    match e
    case Const(_) =>
    case Var(_) =>
    case Node(op, args) =>
        calc {
            Eval(PartiallyEvaluate(e), env);
            Eval(PartiallyEvaluate(Node(op, args)), env);
            Eval(Node(op, PartiallyEvaluateList(op, args)), env);
            EvalList(PartiallyEvaluateList(op, args), op, env);
            { PartiallyEvaluateListCorrect(op, args, env); }
            EvalList(args, op, env); 
            Eval(Node(op, args), env);
        }
}
