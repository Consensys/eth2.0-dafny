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

include "../utils/NativeTypes.dfy"
include "../utils/NonNativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "../utils/MathHelpers.dfy"
include "../utils/Helpers.dfy"

/**
 *  Integers serialisation, deserialisation.
 *
 */
module IntSeDes {

    import opened NativeTypes
    import opened NonNativeTypes
    import opened Eth2Types
    import opened MathHelpers
    import opened Helpers

    //  Useful lemmas relating constants to powers of two
    lemma constAsPowersOfTwo() 
        ensures power2(8) == 0x100
        ensures power2(16) == 0x10000
        ensures power2(32) == 0x100000000
        ensures power2(64) ==  0x10000000000000000
        ensures power2(128) == 0x100000000000000000000000000000000
        ensures power2(256) == 0x10000000000000000000000000000000000000000000000000000000000000000 
    {
        calc == {
            power2(16);
            == { productRulePower2(8, 8); }
            power2(8) * power2(8);
            == calc == { power2(8) == 0x100 ; }
            0x100 * 0x100;
            == 
            0x10000;
        }
        calc == {
            power2(32);
            == { productRulePower2(16, 16); }
            power2(16) * power2(16);
            == calc == { power2(16) == 0x100 ; }
            0x10000 * 0x10000;
            == 
            0x100000000;
        }
        calc == {
            power2(64);
            == { productRulePower2(32, 32); }
            power2(32) * power2(32);
            == calc == { power2(32) == 0x100000000 ; }
            0x100000000 * 0x100000000;
            == 
            0x10000000000000000;
        }
        calc == {
            power2(128);
            == { productRulePower2(64, 64); }
            power2(64) * power2(64);
            == calc == { power2(64) == 0x10000000000000000 ; }
            0x10000000000000000 * 0x10000000000000000;
            == 
            0x100000000000000000000000000000000;
        }
        calc == {
            power2(256);
            == { productRulePower2(128, 128); }
            power2(128) * power2(128);
            == calc { power2(128) == 0x100000000000000000000000000000000 ; }
            0x100000000000000000000000000000000 * 0x100000000000000000000000000000000;
            == 
            0x10000000000000000000000000000000000000000000000000000000000000000;
        }
    }

    //  Uintk serialisation and deserielisation.

    /**
     *  Computes the serialisation of a natural value.
     *
     *  @param n     The value to serialise.
     *  @param k     The number of bytes for the result of the serialisation.
     *
     *  @returns     The `k`-byte big endian serialisation of `n`.
     *
     */
    function method uintSe(n: nat, k: nat) : seq<byte>
        requires k >= 1
        requires n < power2(8 * k) 
        ensures |uintSe(n, k)| == k

        decreases n, k
    {
        if ( k == 1 ) then 
            [n as byte]
        else 
            //  ensures pre-cond for recursive call n / 256 < power2(8 * (k - 1))
            //  implied by n < power2(8) * power2(8 * (k - 1)) (productRulePower2)
            productRulePower2(8, 8 * (k - 1));
            [(n % 256) as byte] + uintSe( n / 256, k - 1)
    }

    /**
     *  Deserialise a sequence of bytes into a natural number.
     *
     *  @param  b   A sequence of at least one byte. 
     *
     *  @returns     A natural number obtained by interpreting `b` as big endian.
     */
    function method uintDes(b : seq<byte>) : nat
        requires |b| >= 1
        ensures uintDes(b) < power2(8 * |b|) 

        decreases b
    {
        if ( |b| == 1 ) then 
            b[0] as nat
        else 
            //  Inductive proof of the post-condition uses power2(8) == 256 
            //  and power2(8) * power2(8 * (|b| - 1)) == power2(8 * |b|) 
            productRulePower2(8, 8 * (|b| - 1) );
            (b[0] as nat) + 256 * uintDes(b[1..])
    }

    /**
     *  Composition of deserialise and serialise is the identiy.
     *
     *  @param  n   A natural number
     *  @param  k   A number of bytes.
     */
    lemma {:induction n, k} involution(n : nat, k : nat)
        requires n < power2(8 * k) 
        requires k >= 1
        ensures uintDes(uintSe(n, k)) == n 
    {
        if ( k == 1 ) {
            //  Thanks Dafny
        } else {
            //  Ensuring pre-condition os recursive call to uinSe requires 
            //  power2(8) * power2(8 * (k - 1)) == power2(8 * k) 
            productRulePower2(8, 8 * (k - 1));
            calc == {
                uintDes(uintSe(n, k));
                ==
                uintDes([ (n % 256) as byte] + uintSe( n / 256 , k - 1));
            }
        }
    }
}