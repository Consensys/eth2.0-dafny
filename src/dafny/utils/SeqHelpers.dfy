
/**
 *  Som useful facts about sequences 
 *  and how to simplify/rewrite them. 
 */
module SeqHelpers {

    lemma seqHeadTail<T>(s: seq<T>)
        requires |s|>= 1
        ensures [s[0]] + s[1..] == s
    {   //  Thanks Dafny.
    }

    lemma seqInitLast<T>(s: seq<T>, i : nat)
        requires 0 <= i < |s| - 1
        requires |s| >= 1
        ensures s[..i] + [s[i]] == s[..i + 1]
    {   //  Thanks Dafny.
    }

    lemma seqSplit<T>(s: seq<T>, i : nat)
        requires 0 <= i <= |s| 
        ensures s[..i] + s[i..] == s
    {   //  Thanks Dafny.
    }

    lemma seqConcatAssoc<T>(s1: seq<T>, s2 : seq<T>, s3 : seq<T>)
        ensures s1 + s2 + s3 == (s1 + s2) + s3 == s1 + (s2 + s3)
    {   //  Thanks Dafny.
    }

    lemma seqElimEmpty<T>(s : seq<T>)
        ensures s + [] == [] + s == s
    {   //  Thanks Dafny.
    }
    
}