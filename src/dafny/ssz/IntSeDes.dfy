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
        calc {
            power2(16);
            == { productRulePower2(8, 8); }
            power2(8) * power2(8);
            == calc { power2(8) == 0x100 ; }
            0x100 * 0x100;
            == 
            0x10000;
        }
        calc {
            power2(32);
            == { productRulePower2(16, 16); }
            power2(16) * power2(16);
            == calc { power2(16) == 0x100 ; }
            0x10000 * 0x10000;
            == 
            0x100000000;
        }
        productRulePower2( 64 , 64 );
        productRulePower2( 128 , 128 );
    }

    //  Uintk serialisation and deserielisation.

    /**
     * Computes the serialisation of a natural value.
     *
     * @param n     The value to serialise.
     * @param k     The number of bytes for the the result of the serialisation.
     *
     * @returns     The `k`-byte big endian serialisation of `n`.
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
            [ (n % 256) as byte] + uintSe( n / 256 , k - 1)
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

    //  Special cases used in Eth2.0 Specs: Uint_k for k in {8, 16, 32, 64, 128, 256}
    
    /** Uint8. */
    function method uint8ToBytes(n: uint8) : seq<byte> 
        requires power2(8) == 0x100
        ensures |uint8ToBytes(n)| == 1
    {
        uintSe(n as nat, 1)
    }
 
    function method byteToUint8(b: seq<byte>) : uint8
        requires |b| == 1
    {
        uintDes(b) as uint8
    }

    /** Encode/decode Uint8 yields Identity. */
    lemma uint8AsBytesInvolutive(n : uint8) 
        ensures byteToUint8(uint8ToBytes(n)) == n
    {   //  Thanks Dafny
    }

    /** Uint16. */
    function method uint16ToBytes(n: uint16) : seq<byte> 
        requires n as nat < power2(2 * 8)
        ensures |uint16ToBytes(n)| == 2
    {
        assert( n as nat < power2(2 * 8));

        uintSe(n as nat, 2)
    }

    function method bytesToUint16(b: seq<byte>) : uint16
        requires |b| == 2
    {
        uintDes(b) as uint16
    }

    /** Encode/decode Uint16 yields Identity. */
    lemma uint16AsBytesInvolutive(n : uint16) 
        requires n as nat < power2(2 * 8)
        ensures bytesToUint16(uint16ToBytes(n)) == n
    {   
        involution(n as nat, 2);
    }

    /** Uint32. */
    function method uint32ToBytes(n: uint32) : seq<byte> 
        requires n as nat < power2(4 * 8)
        ensures |uint32ToBytes(n)| == 4
    {
        uintSe(n as nat, 4)
    }

    function method bytesToUint32(b: seq<byte>) : uint32
        requires |b| == 4
        ensures power2(|b| * 8) == 0x100000000
    {   
        constAsPowersOfTwo();
        uintDes(b) as uint32
    }

    /** Encode/decode Uint32 yields Identity. */
    lemma uint32AsBytesInvolutive(n : uint32) 
        requires n as nat < power2(4 * 8)
        ensures bytesToUint32(uint32ToBytes(n)) == n
    {   
        involution(n as nat, 4);
    }

    /** Uint64. */
    function method uint64ToBytes(n: uint64) : seq<byte> 
        requires n as nat < power2(8 * 8)
        ensures |uint64ToBytes(n)| == 8
    {
        uintSe(n as nat, 8)
    }

    function method bytesToUint64(b: seq<byte>) : uint64
        requires |b| == 8
        ensures power2(|b| * 8) == 0x10000000000000000
    {   
        constAsPowersOfTwo();
        uintDes(b) as uint64
    }

    /** Encode/decode Uint32 yields Identity. */
    lemma uint64AsBytesInvolutive(n : uint64) 
        requires n as nat < power2(8 * 8)
        ensures bytesToUint64(uint64ToBytes(n)) == n
    {   
        involution(n as nat, 8);
    }

    /** Uint128. */
    function method uint128ToBytes(n: uint128) : seq<byte> 
        requires n as nat < power2(16 * 8)
        ensures |uint128ToBytes(n)| == 16
    {
        uintSe(n as nat, 16)
    }

    function method bytesToUint128(b: seq<byte>) : uint128
        requires |b| == 16
        ensures power2(|b| * 8) == 0x100000000000000000000000000000000
    {   
        constAsPowersOfTwo();
        uintDes(b) as uint128
    }

    /** Encode/decode Uint32 yields Identity. */
    lemma uint128AsBytesInvolutive(n : uint128) 
        requires n as nat < power2(16 * 8)
        ensures bytesToUint128(uint128ToBytes(n)) == n
    {   
        involution(n as nat, 16);
    }

    /** Uint256. */
    function method uint256ToBytes(n: uint256) : seq<byte> 
        requires n as nat < power2(32 * 8)
        ensures |uint256ToBytes(n)| == 32
    {
        uintSe(n as nat, 32)
    }

    function method bytesToUint256(b: seq<byte>) : uint256
        requires |b| == 32
        ensures power2(|b| * 8) == 0x10000000000000000000000000000000000000000000000000000000000000000
    {   
        constAsPowersOfTwo();
        uintDes(b) as uint256
    }

    /** Encode/decode Uint32 yields Identity. */
    lemma uint256AsBytesInvolutive(n : uint256) 
        requires n as nat < power2(32 * 8)
        ensures bytesToUint256(uint256ToBytes(n)) == n
    {   
        involution(n as nat, 32);
    }

}