function M(x: int, b: bool): int
  decreases !b
{
    if b then x else M(x + 25, true)
}
