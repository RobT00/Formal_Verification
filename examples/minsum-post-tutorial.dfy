
/*  Read about Dafny (sub-) sequences here: http://rise4fun.com/Dafny/tutorial/Sequences
 *  
 *  Example from Section 4.3.3 (p. 287) of "Logic in Computer Science: Modelling and Reasoning about Systems" by M. Huth and M. Ryan
 *  
 */

/***
	This function implements the sum of the sub-sequence starting at i (inclusive) and ending at j (exclusive).
	To call this function we has to prove the 'requires' statement (precondition).
***/
function sum(a:seq<int>, i:int, j:int) : int 
	requires 0 <= i <= j <=|a|
{
	if i == j then 0
	else sum(a, i, j-1) + a[j-1]
}

/***
	This predicates states that the parameter s is less than or equal to the sum of any subsequence whose start and end are between 0 (inclusive) and k (exclusive).
	To use this predicate we have to prove the precondition.
    We want to use this predicate as invariant (with 0 <= k <= |a|) and as a post-condition (with k == |a|)
***/
predicate lowsum(a: seq<int>, k:int, s: int)
	requires 0 <= k <= |a|
{
	forall i, j  :: 0 <= i < j <= k ==> s <= sum(a,i,j)
}

/***
	This predicate states that the parameter t is less than or equal to the sum of any subsequence whose start is between 0 (inclusive) and k (exclusive) and its end is k-1.
	To use this predicate we have to prove the precondition.
    We want to use this predicate as invariant (with 0 <= k <= |a|) and as a post-condition (with k == |a|)
***/
predicate lowsumend(a: seq<int>, k:int, t: int)
	requires 0 <= k <= |a|
 {
	forall i :: 0 <= i < k ==> t <= sum(a,i,k)
}

/***
   The following two predicates are not used in the book.
   The first states that s contains the sum of a sub-sequence from *some* i (inclusive) to *some* j (exclusive), where 0 <= i < j <= |k|.
   To use this predicate we have to prove the precondition.
   We want to use this predicate as invariant (with 0 <= k <= |a|) and as a post-condition (with k == |a|)
***/
predicate issum(a: seq<int>, k:int, s:int)
	requires 0 <= k <= |a|
{
	exists i,j :: 0 <= i < j <= k && s == sum(a,i,j)
}

/***
    This predicate states that t is the some of a sub-sequence starting from *some* i (inclusive) and ending at k (exclusive).
    To use this predicate we have to prove the precondition.
    We want to use this predicate as invariant (with 0 <= k <= |a|) and as a post-condition (with k == |a|)
***/
predicate issumend(a: seq<int>, k:int, t:int)
	requires 0 <= k <= |a|
{
	exists i:: 0 <= i < k && t == sum(a,i,k)
}

/***
	The following is a lemma that is needed in one part of the proof, to show the implication:

		issumend(a,k,t)	==> issumend(a,k+1,t+a[k])

	when k < |a|.
	We will call this lemma as a method to establish the implication.
***/
lemma issumendL(a: seq<int>, k:int, t:int)
	requires 0 < k < |a|
	requires issumend(a,k,t)
	ensures issumend(a,k+1,t+a[k])
{
	assert exists i :: 0 <= i < k && t == sum(a,i,k);
	assert exists i :: 0 <= i < k && t+a[k] == sum(a,i,k) + a[k];
	assert forall i :: 0 <= i < k ==> sum(a,i,k) + a[k] == sum(a,i,k+1);
}

/***
	This is the minsum method from the book.
	The only difference is that the calls to 'min' have been replaced with if-then-else's.
	Here we proved that the result of the method is less than or equal to the sum of any sub-sequence in 'a': lowsum(a,|a|,ret).
	We also prove that the result *is* the sum of some sub-sequence in 'a'.
***/
method minsum(a: seq<int>) returns (ret:int)
	requires |a| > 0
	ensures lowsum(a,|a|,ret)
	ensures issum(a,|a|,ret)				// This post condition is not in the book. It makes sure that the result is indeed the sum of *some* sequence.
{
	var k := 1;
	var t := a[0];
	var s := a[0];
	assert s == sum(a,0,1);					// needed to prove the invariant issum(a,k,s)
	while (k != |a|)
		decreases |a| - k					//--> Dafny already figured this variant on its own
		invariant 0 < k <= |a|
		invariant lowsumend(a,k,t)			//--> needed to prove the invariant lowsum(a,k,s), as in the proof in the book
		invariant lowsum(a,k,s)				// INVARIANT for proving the post-condition lowsum(a,|a|,ret)
		invariant issumend(a,k,t)			// --> needed to prove the invariant issum(a,k,s)
		invariant issum(a,k,s)				// INVARIANT for proving the post condition issum(a,|a|,ret)
	{
		if (t + a[k] < a[k]) {
			assert issumend(a,k,t);			// needed to prove the invariant issum(a,k,s)
			issumendL(a,k,t);				// needed to prove the invariant issum(a,k,s)
			t := t + a[k];
			assert issumend(a,k+1,t);		// needed to prove the invariant issum(a,k,s)
		} else {
			t := a[k];
			assert t == sum(a,k, k+1);		// needed to prove the invariant issum(a,k,s)
		}
		if (t < s) {
			s := t;
		}
		k := k + 1;
	}
	return s;
}