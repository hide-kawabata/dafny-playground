datatype ColoredTree = Leaf(Color)
                     | Node(ColoredTree, ColoredTree)

datatype Color = Blue | Yellow | Green | Red

predicate IsSwedishFlagColor(c: Color) {
    c.Blue? || c.Yellow?
}

predicate IsSwedishColoredTree(t: ColoredTree) 
{
    match t
    case Leaf(c) => IsSwedishFlagColor(c)
    case Node(l,r) => IsSwedishColoredTree(l) && IsSwedishColoredTree(r)
}

