predicate isPrefixPred(pre:string, str:string)
{
	// True IFF 'pre' is prefix of 'str'
	(|pre| <= |str|) && pre == str[..|pre|]
}

predicate isNotPrefixPred(pre:string, str:string)
{
	// True IFF 'pre' not prefix of 'str'
	// TODO: your formula should not contain &&
	(|pre| > |str|) || pre != str[..|pre|]
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma PrefixNegationLemma(pre:string, str:string)
	ensures  isPrefixPred(pre,str) <==> !isNotPrefixPred(pre,str)
	ensures !isPrefixPred(pre,str) <==>  isNotPrefixPred(pre,str)
{}


predicate isSubstringPred(sub:string, str:string)
{
  // True IFF 'sub' is substring of 'str'
  // TODO
  exists k | 0 <= k <= |str| - |sub| :: sub == str[k..][..|sub|]
//   |sub| == 0 || 
//   (|sub| <= |str| && 
//   (exists k | 0 <= k <= |str| - |sub| :: isPrefixPred(sub, str[k..]))
//   )
}

predicate isNotSubstringPred(sub:string, str:string)
{
	// True IFF 'sub' is not substring of 'str'
	// TODO: your FOL formula should start with a forall - can refer to previous predicates
	forall k | 0 <= k <= |str| - |sub| :: isNotPrefixPred(sub, str[k..])
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma SubstringNegationLemma(sub:string, str:string)
	ensures  isSubstringPred(sub,str) <==> !isNotSubstringPred(sub,str)
	ensures !isSubstringPred(sub,str) <==>  isNotSubstringPred(sub,str)
{}


predicate haveCommonKSubstringPred(k:nat, str1:string, str2:string)
{
  // True IFF 'str1' and 'str2' have common substring of length 'k'
  // TODO - can refer to previous predicates
//   exists a, b | 0 <= a <= |str1| - k && 0 <= b <= |str2| - k && 0 <= k <= min(|str1|, |str2|) :: isSubstringPred(str1[a..][..k], str2) || isSubstringPred(str2[b..][..k], str1)
	exists a | 0 <= a <= |str1| - k && 0 <= k <= min(|str1|, |str2|) :: isSubstringPred(str1[a..][..k], str2)
}

function min(a:int, b:int): int
{
	if a <= b then a else b
}

predicate haveNotCommonKSubstringPred(k:nat, str1:string, str2:string)
{
	// True IFF 'str1' and 'str2' have no common substring of length 'k'
	// TODO: your FOL formula should start with a forall - can refer to previous predicates
	// forall a, b | 0 <= a <= |str1| - k && 0 <= b <= |str2| - k && (k > 0 || k > min(|str1|, |str2|)) :: isNotSubstringPred(str1[a..][..k], str2) || isNotSubstringPred(str2[b..][..k], str1)
	(forall a | 0 <= a <= |str1| - k :: isNotSubstringPred(str1[a..][..k], str2)) || 
	k < 0 || 
	k > min(|str1|, |str2|)
}

// Sanity check: Dafny should be able to automatically prove the following lemma
lemma commonKSubstringLemma(k:nat, str1:string, str2:string)
	ensures  haveCommonKSubstringPred(k,str1,str2) <==> !haveNotCommonKSubstringPred(k,str1,str2)
	ensures !haveCommonKSubstringPred(k,str1,str2) <==> haveNotCommonKSubstringPred(k,str1,str2)
{}
