datatype BYTree = BlueLeaf |
                  YellowLeaf |
                  Node(left: BYTree, right: BYTree)

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

function LeftDepth0(t: BYTree): nat {
  match t
  case BlueLeaf => 0
  case YellowLeaf => 0
  case Node(a,_) => 1 + LeftDepth0(a)
}
function LeftDepth(t: BYTree): nat {
  if t.BlueLeaf? then 0
  else if t.YellowLeaf? then 0
  else 1 + LeftDepth(t.left)
}
method check(t: BYTree) {
//  assert LeftDepth0(t) == LeftDepth(t);
  assert LeftDepth0(BlueLeaf) == LeftDepth(BlueLeaf);
}

