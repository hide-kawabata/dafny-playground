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

lemma {:induction false} OceanizeIdempotent(t: BYTree)
    ensures Oceanize(Oceanize(t)) == Oceanize(t)
{
    match t
    case BlueLeaf =>
    case YellowLeaf =>
    case Node(l, r) =>
        calc {
            Oceanize(Oceanize(Node(l, r)));
            Oceanize(Node(Oceanize(l), Oceanize(r)));
            Node(Oceanize(Oceanize(l)), Oceanize(Oceanize(r)));
            { OceanizeIdempotent(l); }
            { OceanizeIdempotent(r); }
            Node(Oceanize(l), Oceanize(r));
        }
}
