//
// CSU55004 Formal Verification
// Assignment 2
// Aron Hoffmann
// 15321585
// 19 November 2019
//

predicate isMax(s: string, lo: nat)
{
    0 <= lo < |s| && forall i | 0 <= i < |s| :: s[i] <= s[lo]
}

method findMax(s: string) returns (lo: nat)
    requires 0 < |s|
    ensures isMax(s, lo)
{
    lo := 0;
    var hi: nat := |s| - 1;

    ghost var max := if s[lo] >= s[hi] then lo else hi;

    while lo < hi
        decreases hi - lo
        invariant 0 <= lo <= hi < |s|
        invariant lo == max || hi == max
        invariant forall i | 0 <= i < (lo + 1) || hi <= i < |s| :: s[i] <= s[max]
    {
        if s[lo] <= s[hi]
        {
            lo := lo + 1;
            max := hi;

            if s[lo] >= s[max] {
                max := lo;
            }
        } else {
            hi := hi - 1;
            max := lo;

            if s[hi] >= s[max] {
                max := hi;
            }
        }
    }
}