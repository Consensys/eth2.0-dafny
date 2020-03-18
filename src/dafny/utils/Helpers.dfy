
/** Helper types.  */
module Helpers {

    /** Try type (as in Scala). */
    datatype Try<T> = Success(t : T) | Failure 

    /* Option type */
    datatype Option<T> = None | Some(T)

    /* Either type */
    datatype Either<T> = Left(T) | Right(T)

    /**
     *  Ceiling function.
     *
     *  @param  n   Numerator
     *  @param  d   Denominator
     *  @returns    The smallest integer last than float(n / d).
     */
    function method ceil(n: nat, d: nat) : nat
        requires d != 0
        ensures n >= 1 ==> ceil(n , d) >= 1
        ensures ceil(n ,d) == 0 <==> n == 0
    {
        if (n % d == 0) then 
            n / d
        else 
            n / d + 1
    }       

    /** Create Sequences with same element. 
     *
     *  @tparam T   A type.
     *  @param  t   An value.
     *  @param  k   A non-negative integer.
     *  @returns    A seq [t,t, ..., t] of size k.
     */
    function method timeSeq<T>(t : T, k : nat) : seq<T> 
        ensures |timeSeq(t,k)| == k
        decreases k
    {
        if k == 0 then []
        else [t] + timeSeq(t, k - 1)
    }

    /** 
     *  Sum of the length of subsequences. 
     *  
     *  @tparam T   A type.
     *  @param  s   A sequence of sequences of T.
     *  @returns    The sum of the lengths of the subsequences.
     */
    function sumSubLength<T>(s : seq<seq<T>>) : nat 
        ensures sumSubLength(s) >= 0 
    {
        if s == [] then 0
        else |s[0]| + sumSubLength(s[1..])
    }

    lemma {:induction s} foo2<T>(s: seq<seq<T>>, x : seq<T>)
        ensures flatten([x] + s) == x + flatten(s)
    {   //  Thanks Dafny
    }

    /**
     *  Flatten dsitributes over append element.
     *  This is a lemma used to prove the more general 
     *  distribution lemma `flattenDistributes`.
     */
    lemma {:induction s} distribFlatten<T>(s: seq<seq<T>>, x : seq<T>)
        ensures flatten(s + [x]) == flatten(s) + x
        decreases s
    {
        if (|s| == 0) {
            //  Thansk Dafny
        } else {
            calc == {
                flatten(s + [x]);
                == calc == {
                    s ;
                    ==
                    [s[0]] + s[1..];
                }
                flatten([s[0]] + s[1..] + [x]);
                == calc == {
                    [s[0]] + s[1..] + [x];
                    ==
                    [s[0]] + (s[1..] + [x]);
                }
                flatten([s[0]] + (s[1..] + [x]));
                == { foo2( s[1..] + [x], s[0]); }
                s[0] + flatten(s[1..] + [x]);
                == { distribFlatten(s[1..], x); }
                s[0] + flatten(s[1..]) + x;
            }
        }

    }

    /**
     *  Flatten distributes over concatenation.
     */
    lemma {:induction s2} flattenDistributes<T>(s1: seq<seq<T>>, s2: seq<seq<T>>)
        ensures flatten(s1 + s2) == flatten(s1) + flatten(s2)
        decreases |s2|
    {   
        if (|s2| == 0) {
            calc == {
                flatten(s1 + s2);
                == calc == {
                    s1 + s2 ;
                    == 
                    s1;
                }
                flatten(s1) ;
            }
        } else {
            assert |s2| >= 1;
            calc == {
                flatten(s1 + s2);
                == calc == {
                    s2 ;
                    ==
                    [s2[0]] + s2[1..];
                }
                flatten(s1 + ([s2[0]] + s2[1..]));
                == calc == {
                    s1 + ([s2[0]] + s2[1..]);
                    ==
                    (s1 + [s2[0]]) + s2[1..];
                }
                flatten((s1 + [s2[0]]) + s2[1..]);
                == { flattenDistributes(s1 + [s2[0]], s2[1..]) ;}
                flatten(s1 + [s2[0]]) + flatten(s2[1..]);
                == {distribFlatten(s1, s2[0]) ;}
                (flatten(s1) + s2[0]) + flatten(s2[1..]);
            }
        }
    }

    /** .
     *  Flatten seqs of seqs.
     *
     *  @tparam T   A type.
     *  @param  s   A sequence of sequences of T.
     *  @returns    The flattened sequence which is concatenation of the sequences of
     *              each element.
     *
     *  @example    flatten([]) = [], flatten [ [], [] ] = [], flatten [ [1,2], [3]] = [1,2,3],
     *              flatten([], [1,2]) = [1,2].
     */
    function flatten<T>(s: seq<seq<T>>): seq<T>
        ensures |flatten(s)| == sumSubLength(s)
        decreases  s
    {
        if |s| == 0 then []
        else s[0] + flatten(s[1..])
    }

    //  Properties of flatten

    /** 
     *  The set of elements in flatten is the same as in the union of the elements. 
     */
    lemma {:induction s} lem1<T>(s : seq<seq<T>>, x : T)
        ensures x in flatten(s) <==> exists i :: 0 <= i < |s| && x in s[i]
    {}

   lemma lem3<T>(s : seq<seq<T>>)
        requires |s| >= 1
        ensures sumSubLength(s) == sumSubLength(s[..|s| - 1]) + |s[|s| - 1]|
//    {

//    } 
    
}
