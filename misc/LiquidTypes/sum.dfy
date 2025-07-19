function sum(k: int): int
{
    if k < 0 then 0 else
        var s := sum(k - 1);
        s + k
}

method sumtest(k: int)
{
    sumprop(k); // this is required to show the following line
    assert sum(k) >= k && sum(k) >= 0;
}

 // this can be shown automatically as a lemma
lemma sumprop(k: int)
    ensures sum(k) >= k && sum(k) >= 0
{}

lemma {:induction false} sumprop1(k: int)
    ensures sum(k) >= k
{
    if k < 0 { // this branch is required    
    } else if k == 0 { // this part is not required
        assert sum(k) == k + sum(k-1) == 0 + 0;
        assert sum(k) >= k == 0;
    } else { // k > 0
        assert sum(k) == k + sum(k-1);
        sumprop1(k-1);
        assert sum(k) == k + sum(k-1) >= k + k - 1 && k >= 1;
        assert sum(k) >= k;
    }
}

lemma {:induction false} sumprop2(k: int)
    ensures sum(k) >= k
{
    if k < 0 { // this branch is required
    } else { // k >= 0
        assert sum(k) == k + sum(k-1);
        if k == 0 { // this part is not required
            assert sum(k) == k + sum(k-1) == 0 + 0 == 0;
            assert sum(k) >= k;
        } else {
            sumprop2(k-1);
            assert sum(k) == k + sum(k-1) >= k + k - 1 && k >= 1;
            assert sum(k) >= k;
        }
    }
}

lemma {:induction false} sumprop3(k: int)
    ensures sum(k) >= k
{
    if k < 0 { // this branch is required
    } else { // k > 0
        sumprop3(k-1);
    }
}

lemma {:induction false} sumprop0(k: int)
    ensures sum(k) >= 0
{
    // case splitting is not required
    sumprop3(k); // sum(k) >= k
}
