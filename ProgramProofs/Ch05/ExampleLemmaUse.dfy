function More(x: int): int {
    if x <= 0 then 1 else More(x - 2) + 3
}

lemma Increasing(x: int)
  ensures x < More(x)
{}

method ExampleLemmaUse(a: int)
{
    var b := More(a);
    Increasing(a); // a < More(a)
    Increasing(b); // b < More(b), i.e., a < More(a) < More(More(a))
    var c := More(b); // More(b) == c, i.e., a < More(a) < More(More(a)) == c
    assert 2 <= c - a;
}

// 5.3.1 Proof assertions
lemma {:induction false} Increasing2(x: int)
  ensures x < More(x)
{
  assert true;
  if x <= 0 {
    assert x <= 0;
    assert x <= 0 && More(x) == 1; // def
    assert x < More(x);
  } else {
    assert 0 < x;
    assert 0 < x && More(x) == More(x - 2) + 3; // def
    Increasing2(x - 2); // IH
    assert 0 < x && More(x) == More(x - 2) + 3 && x - 2 < More(x - 2);
    assert More(x) == More(x - 2) + 3 && x + 1 < More(x - 2) + 3;
    assert x + 1 < More(x);
    assert x < More(x);
  }
  assert x < More(x);
}

lemma {:induction false} Increasing3(x: int)
  ensures x < More(x)
{
  if x > 0 {
    assert More(x) == More(x-2) + 3;
    Increasing3(x-2);
    assert More(x) == More(x-2) + 3 && x-2 < More(x-2);
    assert More(x) == More(x-2) + 3 && x+1 < More(x-2)+3;
    assert x+1 < More(x);
  }
}


// 5.4.0
lemma {:induction false} Increasing4(x: int)
  ensures x < More(x)
{
  if x > 0 {
    calc {
      More(x); // RHS
      More(x-2)+3;
    > { Increasing4(x-2); }
      (x-2)+3;
      x+1;
    > x; // LHS
    }
  }
}

