
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
method linsearch(s: seq<int>, n: int) returns (found:bool)
	ensures !found ==> !member(s, n)										// FIRST post-condition
	ensures  found ==>  member(s, n)										// SECOND post-condition
{
	var ind := 0;
	found := false;
	while(ind < |s| && !found)
		decreases |s|-ind + (if found then 0 else 1)							// variant -- needed for termination proof
		invariant 0 <= ind <= |s| 
		invariant !member(s[..ind],n)										// needed to prove FIRST post-condition
		invariant found ==> member(s,n)										// needed to prove SECOND post-condition
	{
		if (s[ind] == n) { 
			found := true;
		} else {
			ind := ind + 1;
		}
	}
}

/* If n is in s then the method returns 'true' and an index 'ind' for which s[ind]==n.
  Otherwise, the method returns 'false'
 */
method linsearchInd(s: seq<int>, n:int) returns (found:bool, ind:int)
	ensures !found ==> !member(s, n)
	ensures found ==> member(s, n)
{
	ind := 0;
	found := false;
	while(ind < |s| && !found)
		decreases |s|-ind + (if found then 0 else 1);						// variant -- needed for termination proof
		invariant 0 <= ind <= |s|
		invariant !member(s[..ind],n)
		invariant found ==> member(s,n)
	{
		if (s[ind] == n) { 
			found := true;
		} else {
			ind := ind + 1;
		}
	}
}
