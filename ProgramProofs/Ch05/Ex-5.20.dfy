-- OptimizeCorrect(e: Expr, env: map<string, nat>)
--   ---> ShortenCirrect(e.op, args, env)
-- e, env > e.op, args, env
--   ---> OptimizeAndFilterCorrect(e.args, e.op, env)
-- e, env > e.args, e.op, env