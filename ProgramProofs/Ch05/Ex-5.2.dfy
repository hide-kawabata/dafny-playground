function More(x: int): int {
    if x <= 0 then 1 else More(x - 2) + 3
}

lemma Increasing0(x: int)
  ensures x < More(x)
{
}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{
  if x <= 0 {
    // the proposition becomes: x<=0 ==> x<1, which is valid.
  } else {
    // the proposition becomes: x>0 ==> x<More(x-2)+3, i.e., x>0 ==> x-3<More(x-2)
    Increasing(x-2); // this call gives us: x-2 < More(x-2)
    // Thus, the remaining thing to prove is:
    //   x>0 ==> x-2<More(x-2) ==> x-2-1<More(x-2), which is valid.
  }
}

lemma {:induction false} Increasing1(x: int)
  ensures x < More(x)
{
  if 0 < x  {
    var y := x - 2;
    Increasing(y);
  }
}
