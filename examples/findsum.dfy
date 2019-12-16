
/***
	This function implements the sum of the sub-sequence starting at 0 (inclusive) and ending at j (exclusive).
***/
function sum(s:seq<int>, i:int, j:int) : int 
	requires 0 <= i <= j <= |s|
{
	if i == j then 0
	else sum(s, i, j-1) + s[j-1]
}

lemma sumL(s:seq<int>, i:int, j:int)
	requires 0 <= i <= j < |s|
	ensures sum(s, i, j) + s[j] == sum(s, i, j+1)
{
}

predicate isPrefixSumPred(s: seq<int>, n:int) {
	exists j :: 0 <= j <= |s| && n == sum(s, 0, j)
}
method isPrefixSum(s: seq<int>, n: int) returns (found:bool)
	ensures found ==> isPrefixSumPred(s, n)
	ensures !found ==> !isPrefixSumPred(s, n)
{
	var j := 0;
	var tentativeSum := 0;
	found := (n == tentativeSum);
	while (j < |s| && !found)
		decreases |s| - j + (if found then 0 else 1)
		invariant 0 <= j <= |s|
		invariant tentativeSum == sum(s, 0, j)
		invariant found ==> isPrefixSumPred(s, n)
		invariant !found ==> forall j' :: 0 <= j' <= j ==> n != sum(s, 0, j')
	{
		tentativeSum := tentativeSum + s[j];
		j := j + 1;
		if (n == tentativeSum) {
			found := true;
		} 
	}
}

predicate isSubstringPred(s: seq<int>, n: int) {
	exists l:: 	0 <= l <=|s| && isPrefixSumPred(s[l..], n)
}
predicate isNotSubstringPred(s: seq<int>, n: int) {
	forall i :: 0 <= i <=|s| ==> !isPrefixSumPred(s[i..], n)
}
lemma SubstringSumNegationLemma(s: seq<int>, n: int)
	ensures isSubstringPred(s, n) <==>  !isNotSubstringPred(s,n)
	{}

method isSubstringSum(s: seq<int>, n: int) returns (found:bool)
	ensures found ==> isSubstringPred(s,n)
	ensures !found ==> isNotSubstringPred(s,n)
{
	if (n == 0) { 
		assert n == sum(s, 0, 0);
		assert 0 <= 0 <=|s| && isPrefixSumPred(s[0..],n);
		return true; 
	}
	var k := 0;
	found := false;
	while (k < |s| && !found)
		decreases |s| - k + (if found then 0 else 1)
		invariant 0 <= k <= |s|
		invariant found ==> isPrefixSumPred(s[k..], n)
		invariant !found ==> forall i :: 0 <= i < k ==> !isPrefixSumPred(s[i..], n)
	{
		found := isPrefixSum(s[k..],n);
		if (!found) { k := k + 1; }
	}

}