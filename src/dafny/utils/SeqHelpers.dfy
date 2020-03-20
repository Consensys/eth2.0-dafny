
/**
 *  Som useful facts about sequences 
 *  and how to simplify/rewrite them. 
 */
module SeqHelpers {

    // lemma one<T>(s: seq<T>)
    //     ensures s == s[..|s|]
    // {}

    /** 
     *  Split head and tail.
     */
    lemma seqHeadTail<T>(s: seq<T>)
        requires |s|>= 1
        ensures [s[0]] + s[1..] == s
    {   //  Thanks Dafny.
    }

    /**
     *  Split init and last at index.
     */
    lemma seqInitLast<T>(s: seq<T>, i : nat)
        requires 0 <= i < |s| - 1
        requires |s| >= 1
        ensures s[..i] + [s[i]] == s[..i + 1]
    {   //  Thanks Dafny.
    }

    /**
     *  Split in two at index.
     */
    lemma seqSplit<T>(s: seq<T>, i : nat)
        requires 0 <= i <= |s| 
        ensures s[..i] + s[i..] == s
    {   //  Thanks Dafny.
    }

    /**
     *  Concatenation is associative.
     */
    lemma seqConcatAssoc<T>(s1: seq<T>, s2 : seq<T>, s3 : seq<T>)
        ensures s1 + s2 + s3 == (s1 + s2) + s3 == s1 + (s2 + s3)
    {   //  Thanks Dafny.
    }

    /**
     *  Empty seq is neutral element for concatenation.
     */
    lemma seqElimEmpty<T>(s : seq<T>)
        ensures s + [] == [] + s == s
    {   //  Thanks Dafny.
    }

    /**
     *  Lenght of shifted sub-sections.
     *
     *  s[k..i] = s[k], ..., s[i - 1]
     *  s[k..] = s[k], ..., s[|s| - 1]
     *  s[k..][..i - k] = first i - k elements of s[k], ..., s[|s| - 1] which is
     *              s[k.. i - 1] as k + i - k = i.
     */
    lemma subSeq<T>(s : seq<seq<T>>, i: nat, k : nat) 
        requires |s| >= 1
        requires 0 <= k <= i < |s|
        ensures s[k..i] == s[k..][..i - k]
    {}
    
}