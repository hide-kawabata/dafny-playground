function F(x: int, y: int): int

const L: int
const R: int
//function L(): int
//function R(): int

lemma {:axiom} LeftUnit(x: int)
    ensures F(L, x) == x

lemma {:axiom} RightUnit(x: int)
    ensures F(x, R) == x

lemma LRUnitEqual()
    ensures L == R
{
    calc {
        L;
        { RightUnit(L); }
        F(L, R);
        { LeftUnit(R); }
        R;
    }
}
