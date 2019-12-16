
/* Implementations for finding max element of a sequence */

predicate upperbound(s: seq<int>, max: int) {
	forall i :: 0 <= i < |s| ==> s[i] <= max
}

predicate member(s: seq<int>, n: int) {
	exists i :: 0 <= i <|s| && s[i] == n
}

method Max1(s: seq<int>) returns (max:int)
	requires |s| > 0  			// method precondition
	ensures member(s, max) 		// method postcondition 1
	ensures upperbound(s, max)	// method postcondition 2
{
/* Note: In the following we manually calculate all weakest preconditions,
		starting from postcondition 1. This can be useful for
		- debugging your proof for postcondition 1
		- writing a Hoare logic paper proof in Dafny

		You can do this also for postcondition 2
*/
	assert (|s| > 0);  // method precondition
	assert 0 < 1 <= |s| && member(s[..1], s[0]);  // weakest precondition; IMPLIED
	max := s[0];
	assert 0 < 1 <= |s| && member(s[..1], max);  // weakest precondition
	var i := 1;
	assert 0 < i <= |s| && member(s[..i], max);  // precondition of while loop
	while(i != |s|)
	invariant 0 < i <= |s|
	invariant member(s[..i], max); // while loop invariant 1
	invariant upperbound(s[..i], max); // while loop invariant 2
	{
		assert 0 < i <= |s| && member(s[..i], max) && i != |s|;			// precondition of body of while
		assert s[i]>max ==> 0 < i+1 <= |s| && member(s[..i+1], s[i]);  // weakest precondition; IMPLIED
		if (s[i] > max) { 
			assert 0 < i+1 <= |s| && member(s[..i+1], s[i]);	// weakest precondition
			max := s[i];	
			assert 0 < i+1 <= |s| && member(s[..i+1], max);		// weakest precondition
		}
		assert 0 < i+1 <= |s| && member(s[..i+1], max);			// weakest precondition
		i := i + 1;
		assert 0 < i <= |s| && member(s[..i], max);				// postcondition of body of while
	}
	assert member(s[..i], max) && i <= |s| && !(i != |s|);		// while loop postcondition
	assert member(s, max);										// method postcondition 1; IMPLIED
}


/* This method finds the _index_ of the maximum element.
	Prove its correctness by finding the right invariants.
	Reproduce the paper proof by filling in all weakest preconditions.
 */
method MaxInd(s: seq<int>) returns (maxind:nat)
	requires |s| > 0				// method precondition
//	ensures 0<=maxind<|s|			// method postcondition 1
//	ensures upperbound(s, s[maxind]) // method postcondition 2
{
	maxind := 0;
	var i := 1;
	while(i < |s|)
		invariant 0 < i <= |s|
		invariant 0 <= maxind < |s|
	{
		if (s[i] > s[maxind]) { 
			maxind := i;	
		}
		i := i + 1;
	}
}




