// termination masures
// Optimize --> OptimizeAndFilter: Node(op, args) --> args
// OptimizeAndFilter --> Optimize: Cons(e, tail) --> e
// OptimizeAndFilter --> OptimizeAndFilter: Cons(e, tail) --> tail

// see Sec-5.8.dfy