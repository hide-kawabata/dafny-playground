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

predicate HasLeftTree(t: BYTree, u: BYTree)
//  requires t.Node?
{
/*  if t.YellowLeaf? then false  
  else if t.BlueLeaf? then false
  else t.left == u
*/
  if t.Node? then t.left == u
  else false
//  t.left == u
}
predicate HasLeftTree0(t: BYTree, u: BYTree)
{
  match t
  case Node(l, _) => l == u
  case _ => false
}
method checkHasLeftTree() {
  var a := Node(Node(BlueLeaf, YellowLeaf), YellowLeaf);
  var a2 := BlueLeaf;
  var b := Node(BlueLeaf, YellowLeaf);
  var b2 := Node(YellowLeaf, YellowLeaf);
  assert HasLeftTree(a, b);
  assert HasLeftTree0(a, b);
  assert !HasLeftTree(a, b2);
  assert !HasLeftTree0(a, b2);
  assert !HasLeftTree(a2, b);
  assert !HasLeftTree0(a2, b);
}


predicate Equal0(t: BYTree, u: BYTree)
{
  t == u
}

predicate Equal(t: BYTree, u: BYTree)
{
  match t
  case BlueLeaf => u.BlueLeaf?
  case YellowLeaf => u.YellowLeaf?
  case Node(l, r) => 
    if u.Node? then Equal(l, u.left) && Equal(r, u.right)
    else false
}

method TestEqual()
{
  var a := Node(BlueLeaf, YellowLeaf);
  var b := Node(BlueLeaf, YellowLeaf);
  assert Equal(a, b);
  assert Equal0(a, b);
}

lemma EqualEqual(u: BYTree, t: BYTree)
  ensures Equal(u, t) == Equal0(u, t)
{
}