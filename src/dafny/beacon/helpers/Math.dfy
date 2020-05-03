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
    method  integer_squareroot(n:uint64) returns (x:uint64)
    requires n < 0xFFFFFFFFFFFFFFFF;
    ensures power(x as nat,2) <= n as nat;
    ensures !(exists x' {:trigger power(x' as nat,2)} :: x'>x && power(x' as nat,2) <= n as nat)
    {
        reveal_power();
        x:=n;    
        var y :=(x+1)/2;

        while(y<x)
            decreases x
            invariant y >= x <==> x as nat *x as nat <= n as nat;
            invariant power(y as nat +1,2) > n as nat;
            invariant power(x as nat +1,2) > n as nat;
            invariant y <= 0x7FFFFFFFFFFFFFFF;
        {
            LemmaMaxForYDivByX(y as nat,n as nat);
            
            x := y;          

            y:=(x+n/x)/2;
            
            assert power(x as nat,2) > n as nat <==> y < x by 
            {
                LemmaYStrictlyLessThanXIff(x as nat,n as nat);
            }

            assert power(y as nat +1,2) > n as nat by
            {
                LemmaSquareYPlusOneGreaterThanX(x as nat,n as nat);
            }
        }

        forall i {:trigger power(i as nat,2)} | i > x
        ensures power(i as nat,2) > n as nat
        {
            lemma_power_increases((x + 1) as nat,i as nat,2);
        }

        return x;
    }    
    
}

