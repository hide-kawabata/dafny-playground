function More(x: int): int {
    if x <= 0 then 1 else More(x - 2) + 3
}

lemma Increasing(x: int)
  ensures x < More(x)

method ExampleLemmaUse(a: int)
{
    Increasing(a); // a < More(a)
    var b := More(a); // b == More(a)
    var c := More(b); // c == More(b) == More(More(a))
    if a < 1000 {
        Increasing(More(a)); // More(a) < More(More(a))
        assert 2 <= c - a;
    }
//    assert 2 <= c - a;
    assert 2 <= c - a || 200 <= a;
}

