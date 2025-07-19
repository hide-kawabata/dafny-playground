datatype Tree<T> = Leaf(data: T)
                | Node(left: Tree<T>, right: Tree<T>)

function Mirror<T>(t: Tree<T>): Tree<T> {
    match t
    case Leaf(_) => t
    case Node(left, right) => Node(Mirror(right), Mirror(left))
}

lemma {:induction false} MirrorMirror<T>(t: Tree<T>)
    ensures Mirror(Mirror(t)) == t
{
    match t
    case Leaf(_) =>
    case Node(l, r) =>
        calc {
            Mirror(Mirror(Node(l,r))); // LHS
        ==  Mirror(Node(Mirror(r), Mirror(l)));
        ==  Node(Mirror(Mirror(l)), Mirror(Mirror(r)));
        ==  { MirrorMirror(l); MirrorMirror(r); }
            Node(l, r);
        }
}

function Size<T>(t: Tree<T>): nat {
    match t
    case Leaf(_) => 1
    case Node(l, r) => Size(l) + Size(r)
}

lemma {:induction false} MirrorSize<T>(t: Tree<T>)
    ensures Size(Mirror(t)) == Size(t)
{
    match t
    case Leaf(_) => 
    case Node(l, r) => calc {
        Size(Mirror(Node(l, r))); // LHS
 //   ==  Size(Node(Mirror(r), Mirror(l)));
 //   ==  Size(Mirror(r)) + Size(Mirror(l));
    ==  { MirrorSize(r); MirrorSize(l); } // IH
 //       Size(r) + Size(l);
        Size(Node(r, l)); // RHS
    }
}