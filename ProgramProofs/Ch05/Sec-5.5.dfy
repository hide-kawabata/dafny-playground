function Reduce(m: nat, x: int): int
//    decreases m
{
    if m == 0 then x else Reduce(m / 2, x + 1) - m
}

lemma {:induction false} ReduceUpperBound(m: nat, x: int)
// lemma ReduceUpperBound(m: nat, x: int)
    ensures Reduce(m, x) <= x
{
    if m == 0 {
        // trivial
    } else {
        calc {
            Reduce(m, x); // LHS
        ==  Reduce(m / 2, x + 1) - m;
        <=  { ReduceUpperBound(m / 2, x + 1); } // IH
            x+1 - m;
        <=  { assert m > 0; }
            x; // RHS
        }
    }
}

lemma {:induction false} ReduceLowerBound(m: nat, x: int)
// lemma ReduceLowerBound(m: nat, x: int)
    ensures x - 2 * m <= Reduce(m, x)
{
    if m == 0 {
        // trivial
    } else {
        calc {
            Reduce(m, x); // RHS
        ==  Reduce(m / 2, x + 1) - m;
        >=  { ReduceLowerBound(m / 2, x + 1); } // IH
            (x + 1) - 2 * (m / 2) - m;
        >=  { assert 2*(m/2) <= m; }
            x + 1 - (2*m+1);
        ==  x - 2 * m; // LHS
        }
    }
}

// calc { 3; > 2; == 2; } 
// calc { 3; > 2; 3; } error
// calc { 3; > 2; 2; } no error
// calc { 3; > 2; 1; } error
// calc { 3; > 2; > 1; } no error

