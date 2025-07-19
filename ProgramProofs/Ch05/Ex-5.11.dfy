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

lemma {:induction false} ReverseColorsInvolution(t: BYTree)
    ensures ReverseColors(ReverseColors(t)) == t
{
    match t
    case BlueLeaf =>
    case YellowLeaf =>
    case Node(left, right) =>
        calc {
            ReverseColors(ReverseColors(Node(left, right)));
            ReverseColors(Node(ReverseColors(left), ReverseColors(right)));
            Node(ReverseColors(ReverseColors(left)), ReverseColors(ReverseColors(right)));
            { ReverseColorsInvolution(left); ReverseColorsInvolution(right); }
            Node(left, right);
        }
}
