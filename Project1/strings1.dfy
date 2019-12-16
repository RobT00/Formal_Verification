predicate isIndex(i: int, s: string) { 0 <= i < |s| }

predicate isPrefixF(pre: string, str: string) { |pre| <= |str| && pre == str[..|pre|] }

// The following method should return true if and only if pre is a prefix of str. That is, str starts with pre
method isPrefix(pre: string, str: string) returns (res: bool)
    ensures res <==> isPrefixF(pre, str)
{
    if |str| < |pre|
    || pre != str[..|pre|]
    {
        res := false;
    }
    else
    {
        res := true;
    }
    return res;
}


predicate isSubstringF(sub: string, str: string)
{
    |sub| == 0 ||
    (|sub| <= |str| &&
     (exists k | 0 <= k <= |str| - |sub|
               :: isPrefixF(sub, str[k..])))
}

// The following method should return true if and only if sub is a substring of str. That is, str contains sub
method isSubstring(sub: string, str: string) returns (res: bool)
    ensures res <==> isSubstringF(sub, str)
{
    if |sub| == 0 { return true; }
    if |sub| > |str| { return false; }
    res := false;
    var i := 0;
    while i <= |str| - |sub|
        decreases |str| - |sub| - i
        invariant 0 <= i <= |str|
        invariant !res <==> (forall a | 0 <= a < i :: !isPrefixF(sub, str[a..]))
    {
        res := isPrefix(sub, str[i..]);
        if res { return true; } // putting a shortcut in the loop condition prevents verification
        i := i + 1;
    }
    return false;
}

predicate haveCommonKSubstringF(k: nat, str1: string, str2: string) {
    k == 0 ||
    (k <= |str1| &&
     k <= |str2| &&
     (exists a | 0 <= a <= |str1| - k :: isSubstringF(str1[a..][..k], str2)))
}

// The following method should return true if and only if str1 and str1 have a common substring of length k
method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    ensures found <==> haveCommonKSubstringF(k, str1, str2)
{
    if k == 0 { return true; }
    if k > |str1| || k > |str2| { return false; }
    found := false;
    var i := 0;
    while i + k <= |str1|
        decreases |str1| - k - i
        invariant 0 <= i <= |str1| - k + 1
        invariant !found ==> forall a | 0 <= a < i :: !isSubstringF(str1[a..][..k], str2)
        // Dafny can't "find a trigger" if it is in the form str1[a..a+k], that expression is too complicated to infer with
    {
        found := isSubstring(str1[i..][..k], str2);
        if found { return true; }
        i := i + 1;
    }
    return false;
}

function minF(a: int, b: int): int { if a < b then a else b }

method min(a: int, b: int) returns (m: int)
    ensures m == minF(a, b)
{
    if a < b { return a; } else { return b; }
}

/* The following method should return the natural number len which is equal to the length of the longest
    common substring of str1 and str2. Note that every two strings have a common substring of length zero. */
method maxCommonSubstringLength(str1: string, str2: string) returns (len: nat)
    ensures (forall l | 0 <= l <= len :: haveCommonKSubstringF(l, str1, str2)) && (forall l | len < l :: !haveCommonKSubstringF(l, str1, str2))
{
    // len == 0 is trivially true
    len := 0;
    var shorter_len := min(|str1|, |str2|);
    while len < shorter_len
        decreases shorter_len - len
        invariant forall l | 0 <= l <= len :: haveCommonKSubstringF(l, str1, str2)
    {
        var b: bool := haveCommonKSubstring(len + 1, str1, str2);
        if !b
        {
            break;
        }
        len := len + 1;
    }
    return len;
}

// Main method for running
method Main()
{
    print "Running\n";
    var r := maxCommonSubstringLength("ThisIsATest", "ThisIsNotATest");
    print r, "\n";
}