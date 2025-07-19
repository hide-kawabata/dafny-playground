function SeqSum(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
//  decreases hi - lo
  decreases (hi - lo - 100000)
{
    if lo == hi then 0 else s[lo] + SeqSum(s, lo + 1, hi)
}
