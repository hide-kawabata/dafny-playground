function More(x: int): int {
    if x <= 0 then 1 else More(x - 2) + 3
}

lemma Increasing(x: int)
  ensures x < More(x)

method ExampleLemmaUse1(a: int)
{
    var b := More(a);
    b := More(b);
    assert 2 <= b - a;
}

method ExampleLemmaUse2(a: int)
{
    var b := More(a);
    Increasing(a); // a < More(a)
    Increasing(b); // b < More(b), i.e., a < More(a) < More(More(a))
    b := More(b);
    assert 2 <= b - a;
}

method ExampleLemmaUse3(a: int)
{
    var b := More(a);
    Increasing(a); // a < More(a)
    b := More(b); // b is now More(More(a))
    Increasing(b); // b < More(b), i.e., More(More(a)) < More(More(More(a)))
//    Increasing(More(a));
    assert 2 <= b - a;
}


method ExampleLemmaUse4(a: int)
{
    var b := More(a);
    Increasing(b); // b < More(b), i.e., More(a) < More(More(a))
    Increasing(a); // a < More(a), i.e., a < More(a) < More(More(a))
    b := More(b); // b is now More(More(a))
    assert 2 <= b - a;
}

method ExampleLemmaUse5(a: int)
{
    Increasing(a); // a < More(a)
    var b := More(a); // b == More(a)
    b := More(b); // c == More(b) == More(More(a))
    if a < 1000 {
        Increasing(More(a)); // More(a) < More(More(a))
//        Increasing(b);
        assert 2 <= b - a;
    }
//    assert 2 <= b - a;
    assert 2 <= b - a || 200 <= a;
}

