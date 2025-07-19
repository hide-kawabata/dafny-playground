function F(x: int, y: int): int

//const L: int
//const R: int
function L(): int
function R(): int

lemma {:axiom} LeftZero(x: int)
    ensures F(L(), x) == L()

lemma {:axiom} RightZero(x: int)
    ensures F(x, R()) == R()

lemma LRZeroEqual()
    ensures L() == R()
{
    calc {
        L();
        { LeftZero(R()); }
        F(L(), R());
        { RightZero(L()); }
        R();
    }
}
