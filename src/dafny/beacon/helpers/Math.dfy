/*
 * Copyright 2020 ConsenSys AG.
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

include "../../libraries/integers/power.i.dfy"
include "../../utils/NativeTypes.dfy"
include "helper_lemmas/MathHelper.dfy"

module  Math
{
    import opened Math__power_i
    import opened Math__power_s
    import opened MathHelperLemmas
    import opened NativeTypes

    /**
     *  Return the largest integer `x` such that `x**2 <= n`
     *
     *  @param       n   A natural number
     *  @return     `x` 
     */    
    method  integer_squareroot(n:nat) returns (x:nat)
    ensures power(x,2) <= n;
    ensures !(exists x' :: x'>x && power(x',2) <= n)
    {
        reveal_power();
        x:=n;    
        var y:nat :=(x+1)/2;

        while(y<x)
            decreases x
            invariant y >= x <==> x*x <= n;
            invariant power(y+1,2) > n as nat;
            invariant power(x+1,2) > n as nat;
        {
            x:=y;

            y:=(x+n/x)/2;
            
            assert power(x,2) > n <==> y < x by 
            {
                LemmaYStrictlyLessThanXIff(x,n);
            }

            assert power(y+1,2) > n by
            {
                LemmaSquareYPlusOneGreaterThanX(x,n);
            }
        }

        forall i | i > x
        ensures power(i,2) > n
        {
            lemma_power_increases(x + 1,i,2);
        }

        return x;
    }    
    
}

