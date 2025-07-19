function max(x: int, y: int): int
{
    if x > y then x else y
}

method maxtest(x: int, y: int)
{
    assert max(x, y) >= x && max(x, y) >= y;
}

lemma maxprop(x: int, y: int)
    ensures max(x, y) >= x && max(x, y) >= y
{
}
