datatype ColoredTree = LeafC(Color)
                     | NodeC(ColoredTree, ColoredTree)

datatype Color = Blue | Yellow | Green | Red


datatype Tree<T> = Leaf(data: T)
                 | Node(left: Tree<T>, right: Tree<T>)

//predicate AllBlue(t: Tree) {
//predicate AllBlue(t) {
predicate AllBlue(t: Tree<Color>) {
    match t
    case Leaf(c) => c == Blue
    case Node(l, r) => AllBlue(l) && AllBlue(r)
}

function Mirror<T>(t: Tree<T>): Tree<T> {
    match t
    case Leaf(c) => Leaf(c)
    case Node(l,r) => Node(Mirror(r), Mirror(l))
}

// 同じコンストラクタが複数箇所のdatatypeで出てきてはいけないようだ．・・・改良できないか？

