lemma pat1(A: bool, B: bool, C: bool)
    requires A ==> B ==> C
{
    calc {
        A;
    ==>
        B;
    ==>
        C;
    }
    assert A ==> B ==> C;
}

lemma pat2(A: bool, B: bool, C: bool)
    requires (A ==> B) && (B ==> C)
{
    calc {
        A;
    ==>
        B;
    ==>
        C;
    }
    assert A ==> B ==> C;
}
