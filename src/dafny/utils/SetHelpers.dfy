/*
 * Copyright 2020 ConsenSys Software Inc.
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
 *  Provide datatype for fork choice rule (and LMD-GHOST)
 */
module SetHelpers {

    /**
     *  If x [= {0, ..., k - 1} and y [= {0, .., k - 1}
     *  then x U y has at most k elements.
     */
    lemma unionCardBound(x : set<nat>, y : set<nat>, k : nat) 
        requires forall e :: e in x ==> e < k
        requires forall e :: e in y ==> e < k
        ensures  forall e :: e in x + y ==> e < k
        ensures |x + y| <= k 
    {
        natSetCardBound(x + y, k);
    }

    /**
     *  If  x [= {0, ..., k - 1} then x has at most k elements.
     */
    lemma natSetCardBound(x : set<nat>, k : nat) 
        requires forall e :: e in x ==> e < k
        ensures |x| <= k 
        decreases k
    {
        if k == 0 {
            assert(x == { });
        } else {
            natSetCardBound(x - { k - 1}, k - 1);
        }
    }

   /**
    *  If a finite set x is included in a finite set y, then
    *  card(x) <= card(y).
    *
    *  @param  T   A type.
    *  @param  x   A finite set.
    *  @param  y   A finite set.
    *  @returns    A proof that x <= y implies card(x) <= card(y)
    *              in other terms, card(_) is monotonic.
    */
    lemma cardIsMonotonic<T>(x : set<T>, y : set<T>) 
        requires x <= y 
        ensures |x| <= |y|
        decreases y 
    {
        if |y| == 0 {
            //  Thanks Dafny
        } else {
            //  |y| >= 1, get an element in y
            var e :| e in y;
            var y' := y - { e };
            //  Split recursion according to whether e in x or not
            cardIsMonotonic(if e in x then x - {e} else x, y');
        }
    }
   
}
