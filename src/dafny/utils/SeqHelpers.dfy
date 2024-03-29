/*
 * Copyright 2021 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
 * License for the specific language governing permissions and limitations 
 * under the License.
 */

 
/**
 *  Some useful facts about sequences 
 *  and how to simplify/rewrite them. 
 */
module SeqHelpers {

    /**
     *  Intersection of two sequences.
     *  
     *  @param  T   A type.
     *  @param  x   A sequence.
     *  @param  y   A sequence.
     *  @returns    The elements in `x` that are in also `y` as a sequence.
     */
    function method seqInter<T(==)>(x : seq<T>, y : seq<T>) : seq<T>
        decreases x 
    {
        if |x| == 0 then []
        else (if x[0] in y then [x[0]] else []) + seqInter(x[1..], y)
    }

    /**
     *  Convert a seq to a set.
     *  
     *  @param  T   A type.
     *  @param  x   A sequence.
     *  @returns    A set with the elements in `x`.
     */
    function method seqToSet<T(!new)>(x : seq<T>) : set<T>
        ensures forall e :: e in x <==> e in seqToSet(x)
        decreases x
    {
        if |x| == 0 then {}
        else { x[0] }  + seqToSet(x[1..])
    }

    /**
     *  If a seq of distinct elements is converted to a set then 
     *  the length of the seq is equivalent to the set.
     *  
     *  @param  T   A type.
     *  @param  x   A sequence.
     *  @returns    A proof that if x is a seq of distinct elements
     *              then |x| == |seqToSet(x)|.
     */
    lemma {:induction x} seqOfDistinctElementsAndSets<T>(x : seq<T>) 
        requires forall i, j :: 0 <= i < j < |x| ==> x[i] != x[j]
        ensures |x| == |seqToSet(x)|
        decreases x 
    {   //  Thanks Dafny
    }

    /** 
     *  Split head and tail.
     *  
     *  @param  T   A type.
     *  @param  x   A sequence.
     *  @returns    A proof if |s|>= 1 then [s[0]] + s[1..] == s.
     */     
    lemma seqHeadTail<T>(s: seq<T>)
        requires |s|>= 1
        ensures [s[0]] + s[1..] == s
    {   //  Thanks Dafny.
    }

    /**
     *  Split init and last at index.
     *  
     *  @param  T   A type.
     *  @param  x   A sequence.
     *  @param  i   A natural number.
     *  @returns    A proof if |s|>= 1 and 0 <= i <= |s| - 1 
     *              then [s[0]] + s[1..] == s.     
     */
    lemma seqInitLast<T>(s: seq<T>, i : nat)
        requires 0 <= i <= |s| - 1
        requires |s| >= 1
        ensures s[..i] + [s[i]] == s[..i + 1]
    {   //  Thanks Dafny.
    }

    /**
     *  Split in two at index.
     *  
     *  @param  T   A type.
     *  @param  x   A sequence.
     *  @param  i   A natural number.
     *  @returns    A proof if 0 <= i <= |s|  then s[..i] + s[i..] == s.          
     */
    lemma seqSplit<T>(s: seq<T>, i : nat)
        requires 0 <= i <= |s| 
        ensures s[..i] + s[i..] == s
    {   //  Thanks Dafny.
    }

    /**
     *  Concatenation is associative.
     *  
     *  @param  T   A type.
     *  @param  s1  A sequence.
     *  @param  s2  A sequence.
     *  @param  s3  A sequence.
     *  @returns    A proof that s1 + s2 + s3 == (s1 + s2) + s3 == s1 + (s2 + s3).          
     */
    lemma seqConcatAssoc<T>(s1: seq<T>, s2 : seq<T>, s3 : seq<T>)
        ensures s1 + s2 + s3 == (s1 + s2) + s3 == s1 + (s2 + s3)
    {   //  Thanks Dafny.
    }

    /**
     *  Empty seq is neutral element for concatenation.
     *
     *  @param  T   A type.
     *  @param  s   A sequence.
     *  @returns    A proof that s + [] == [] + s == s.   
     */
    lemma seqElimEmpty<T>(s : seq<T>)
        ensures s + [] == [] + s == s
    {   //  Thanks Dafny.
    }

    /**
     *  Length of shifted sub-sections.
     *
     *  s[k..i] = s[k], ..., s[i - 1]
     *  s[k..] = s[k], ..., s[|s| - 1]
     *  s[k..][..i - k] = first i - k elements of s[k], ..., s[|s| - 1] which is
     *              s[k.. i - 1] as k + i - k = i.
     *
     *  @param  T   A type.
     *  @param  s   A sequence of sequences.
     *  @param  i   A natural number.
     *  @param  k   A natural number.
     *  @returns    A proof that if |s| >= 1 and 0 <= k <= i < |s|
     *              then s[k..i] == s[k..][..i - k].   
     */
    lemma subSeq<T>(s : seq<seq<T>>, i: nat, k : nat) 
        requires |s| >= 1
        requires 0 <= k <= i < |s|
        ensures s[k..i] == s[k..][..i - k]
    {   //  Thanks Dafny.
    }

    /**
     *  If s is a sequence of length i then s[..i] is equivalent to the full sequence.
     *
     *  @param  T   A type.
     *  @param  s   A sequence.
     *  @param  i   A natural number.
     *  @returns    A proof that if |s| == i and then s[..i] == s.   
     */
     lemma fullSeq<T>(s : seq<T>, i: nat)
        requires |s| == i
        ensures s[..i] == s
    {   // Thanks Dafny
    }
    
}