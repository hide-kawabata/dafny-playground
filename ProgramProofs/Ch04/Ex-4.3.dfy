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

function Oceanize(t: BYTree): BYTree {
  match t
  case Node(a,b) => Node(Oceanize(a), Oceanize(b))
  case _ => BlueLeaf
}

predicate IsNode(t: BYTree) {
  match t
  case BlueLeaf => false
  case YellowLeaf => false
  case Node(_, _) => true
}

function GetLeft(t: BYTree): BYTree
//  requires t.Node?
  requires IsNode(t)
{
  match t
  case Node(left, _) => left
}
