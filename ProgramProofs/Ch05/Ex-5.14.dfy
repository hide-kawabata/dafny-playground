datatype BYTree = BlueLeaf |
                  YellowLeaf |
                  Node(BYTree, BYTree)

function Oceanize(t: BYTree): BYTree {
  match t
  case Node(a,b) => Node(Oceanize(a), Oceanize(b))
  case _ => BlueLeaf
}

function BlueCount(t: BYTree): nat {
    match t
    case BlueLeaf => 1
    case YellowLeaf => 0
    case Node(left, right) => 
        BlueCount(left) + BlueCount(right)
}

lemma {:induction false} BlueCountOceanize(t: BYTree)
// lemma BlueCountOceanize(t: BYTree)
    ensures BlueCount(t) <= BlueCount(Oceanize(t))
{
    match t
    case BlueLeaf =>
    case YellowLeaf =>
    case Node(l, r) =>
        calc {
            BlueCount(Oceanize(Node(l, r)));
            BlueCount(Node(Oceanize(l), Oceanize(r)));
            BlueCount(Oceanize(l)) + BlueCount(Oceanize(r));
            >= 
            { BlueCountOceanize(l); BlueCountOceanize(r); }
            BlueCount(l) + BlueCount(r);
            BlueCount(Node(l, r));
        }
}
