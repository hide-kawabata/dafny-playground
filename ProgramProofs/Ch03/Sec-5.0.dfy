
function More(x: int): int 
//    ensures x < More(x)
{
    if x <= 0 then 1 else More(x-2)+3
}

lemma {:induction false} Increasing(x: int)
    ensures x < More(x)
{
    if x <= 0 {

    } else {
        // x > 0
        Increasing(x-2);
        // x > 0 && x-2 < More(x-2)
        // x > 0 && x-3 < x-2 < More(x-2)
        // x > 0 && x < More(x-2)+3
        // x < More(x)
    }
}

method ExampleLemmaUse(a: int) {
    var b := More(a);
    Increasing(a);
    Increasing(b);
    var c := More(b);
    assert 2 <= c - a;
}

