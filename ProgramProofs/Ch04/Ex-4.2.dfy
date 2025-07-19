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

method TestReverseColors() {
  var a := Node(BlueLeaf, Node(BlueLeaf, YellowLeaf));
  var b := Node(YellowLeaf, Node(YellowLeaf, BlueLeaf));
  assert ReverseColors(a) == b;
  assert ReverseColors(b) == a;
  var c := Node(a, b);
  assert ReverseColors(c) == Node(ReverseColors(a), ReverseColors(b));
  assert ReverseColors(ReverseColors(a)) == a;
  assert !(ReverseColors(ReverseColors(a)) == ReverseColors(a));
}
