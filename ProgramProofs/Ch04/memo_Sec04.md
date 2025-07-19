# 4 Inductive Datatypes

## 4.0 Blue-Yellow Trees
```
datatype BYTree = BlueLeaf |
                  YellowLeaf |
                  Node(BYTree, BYTree)
```

## 4.1 Matching on Datatypes

```
function BlueCount(t: BYTree): nat {
    match t
    case BlueLeaf => 1
    case YellowLeaf => 0
    case Node(left, right) => 
        BlueCount(left) + BlueCount(right)
}
```
