
/* This predicate states that s is sorted */
predicate sorted(s: seq<int>) {
	forall i, j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
}

/* This predicate states that n exists in some position i of sequence s */
predicate member(s: seq<int>, n: int) {
	exists i :: 0 <= i <|s| && s[i] == n
}

/* This method returns true if n is in s and false otherwise

	Note about double implication:

		A <==>  B means
		A  ==>  B and  B ==>  A therefore, by Modus Tollens rule:
	   !B  ==> !A and !A ==> !B which means
	   !B <==> !A which means
	   !A <==> !B

	So we have 3 logically equivalent options for specifying the behaviour of this method:

	Option 1:  ensures  found <==>  member(s, n)
	Option 2:  ensures !found <==> !member(s, n)
	Option 3:  ensures (found ==> member(s, n)) && (!found ==> !member(s, n))

	Here we chose Option 3, and split it into two post-conditions.
 */
method binsearch(s: seq<int>, n: int) returns (found:bool)
	requires sorted(s)
	ensures !found ==> !member(s, n)										// FIRST post-condition
//	ensures  found ==>  member(s, n)										// SECOND post-condition
{
	var lo := 0;
	var hi := |s| - 1;
	var mid := 0;
	found := false;
	while(lo <= hi && !found)
		decreases hi-lo + (if found then 0 else 1)							// variant -- needed for termination proof
		invariant 0 <= lo <= |s| && -1 <= hi < |s| //&& 0 <= mid <= |s|		// needed to prove that the following 2 lines do not contain an index-out-of-bounds error
		invariant !member(s[..lo],n)										// needed to prove FIRST post-condition
		invariant !member(s[hi+1..],n)										// needed to prove FIRST post-condition
//		invariant found ==> member(s,n)										// needed to prove SECOND post-condition
	{
		mid := (hi + lo)/2;
		if (s[mid] == n) { 
			found := true;
		} else if (s[mid] < n) {
			lo := mid + 1;
		} else {
			hi := mid - 1;
		}
	}
}

/* If n is in s then the method returns an index ind for which s[ind]==n.
  Otherwise, the method returns a negative index ind.

	In this method we will replace the postcondition

		ensures  0 <= ind ==> member(s, n)						//(*1*)

	with the postcondition

		ensures  0 <= ind ==> (ind < |s| && s[ind] == n )		//(*2*)

	(*2*) logically implies (*1*) because of the rule
	'Exists-Introduction' of First-Order Logic.

 */
method binsearchInd(s: seq<int>, n:int) returns (ind:int)
	requires sorted(s)
	ensures ind < 0 ==> !member(s, n)										// FIRST post-condition
	ensures 0 <= ind ==> (ind < |s| && s[ind] == n)							// SECOND post-condition
	// ensures 0 <= ind ==> member(s, n)  // if you comment-in this line it will be proven automatically by the above post-condition
{
	if |s| == 0 { return -1; }
	var lo := 0;
	var hi := |s| - 1;
	var mid := 0;
	ind := -1;
	while(lo <= hi && ind < 0)
		decreases hi-lo + (if 0 <= ind then 0 else 1);						// variant -- needed for termination proof
		invariant 0 <= lo <= |s| && -1 <= hi < |s| && 0 <= mid < |s|		// needed to prove that the following 2 lines do not contain an index-out-of-bounds error
		invariant !member(s[..lo],n)										// needed to prove FIRST post-condition
		invariant !member(s[hi+1..],n)										// needed to prove FIRST post-condition
		invariant -1 <= ind < |s|											// needed to prove SECOND post-condition
		invariant 0 <= ind ==> s[ind] == n									// needed to prove SECOND post-condition
	{
		mid := lo + (hi - lo)/2;
		if (s[mid] == n) { 
			ind := mid;
		} else if (s[mid] < n) {
			lo := mid + 1;
		} else {
			hi := mid - 1;
		}
	}
}
