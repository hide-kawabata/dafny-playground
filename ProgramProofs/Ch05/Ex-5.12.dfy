datatype BYTree = BlueLeaf |
                  YellowLeaf |
                  Node(BYTree, BYTree)

function ReverseColors(t: BYTree): BYTree {
    match t
    case BlueLeaf => YellowLeaf
    case YellowLeaf => BlueLeaf
    case Node(a, b) =>
      Node(ReverseColors(a), ReverseColors(b))
}

function LeafCount(t: BYTree): nat {
    match t
    case BlueLeaf => 1
    case YellowLeaf => 1
    case Node(left, right) => LeafCount(left) + LeafCount(right)
}

lemma {:induction false} PreserveLeafCount(t: BYTree)
    ensures LeafCount(ReverseColors(t)) == LeafCount(t)
{
    match t
    case BlueLeaf =>
    case YellowLeaf =>
    case Node(l, r) =>
        calc {
            LeafCount(ReverseColors(Node(l, r)));
            LeafCount(Node(ReverseColors(l), ReverseColors(r)));
            LeafCount(ReverseColors(l)) + LeafCount(ReverseColors(r));
            { PreserveLeafCount(l); }
            { PreserveLeafCount(r); }
            LeafCount(l) + LeafCount(r);
        }
}