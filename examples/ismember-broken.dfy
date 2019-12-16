
predicate member(n: int, s: seq<int>) {
    exists i :: 0 <= i < |s| && s[i] == n
}

predicate notmember(n: int, s: seq<int>) {
    forall i :: 0 <= i < |s| ==> s[i] != n
}

method isMember(m: int, s: seq<int>) returns (ismember: bool)
    ensures ismember ==> member(m, s)
    ensures !ismember ==> notmember(m, s)
{
    ismember := false;
    var i := 0;
    assert notmember(m, s[..i]); //pre-condition
    while (i < |s| && !ismember) 
        decreases |s| - i + (if ismember then 0 else 1)
        invariant 0 <= i <= |s|
        // invariant !ismember ==> notmember(m, s)
        invariant notmember(m, s[..i])
        invariant ismember ==> i < |s|  // or 0 <= i < |s|
        invariant (ismember ==> member(m, s[..i+1]))
    {
        assert notmember(m, s[..i]);
        assert (i < |s| && !ismember);
        assert (s[i] == m) ==> notmember(m, s[..i]);
        assert !(s[i] == m) ==> notmember(m, s[..i+1]);  // logically equivalent to line above && this
        // if s[i] != m {  // bug
        assert (s[i] == m) ==> member(m, s[..i+1]);
        // assert !(s[i] == m) ==> member(m, s[..i]);  // not shown in lecture
        if s[i] == m {
            assert member(m , s[..i+1]);
            assert true ==> member(m, s[..i+1]);
            assert notmember(m, s[..i]); // Weakest pre-condition
            ismember := true;
            assert ismember ==> member(m, s[..i+1]);
            assert notmember(m, s[..i]);
        } else {
            assert ismember ==> member(m, s[..i]);
            assert notmember(m, s[..i+1]);  // Weakest pre-condition
            i := i + 1;
            assert ismember ==> member(m, s[..i]);
            assert notmember(m, s[..i]);
        }
        assert ismember ==> member(m, s[..i+1]);
        assert notmember(m, s[..i]);
    }
    assert notmember(m, s[..i]) && !(i < |s| && !ismember); // post-condition
    assert ismember ==> member(m, s[..i+1]) && !(i < |s| && !ismember);
}