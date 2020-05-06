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
include "../../utils/Helpers.dfy"
include "../../utils/Eth2Types.dfy"
include "helper_lemmas/MathHelper.dfy"

module  Math
{
    import opened Math__power_i
    import opened Math__power_s
    import opened MathHelperLemmas
    import opened NativeTypes
    import opened Eth2Types
    import opened Helpers

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
    
    /**
     * Computes the exclusive-or of two `Bytes32` values
     *
     * @param b1  First `Bytes32` value
     * @param b2  Second `Bytes32` value
     *
     * @returns   A `Bytes32` value corresponding to the exclusive-or of `b1`
     *            and `b2`
     */
    function xor(b1:Bytes32, b2:Bytes32): Bytes32
    ensures forall i | 0 <= i < |xor(b1,b2).bs| :: xor(b1,b2).bs[i] == byteXor(b1.bs[i],b2.bs[i])
    {
        Bytes32(seqBinOpMap<Byte>(b1.bs, b2.bs, byteXor))
    } 

    /**
     * Computes the little endian serialisation of a `uint64` value
     *
     * @param n        A `uint64` value
     * @param length   Length of the serialisation.
     * @requires       n < power(256,length) 
     *                 n <= 8
     *
     * @returns        The `length`-byte little endian serialisation of `n`
     *
     */
    function int_to_bytes(n: uint64, length: uint64) : bytes
    requires n as nat < power(256,length as nat)
    requires length <= 8
    ensures |int_to_bytes(n,length)| == length as int
    {
        reveal_power();
        if(length == 0) then
            []
        else
            [(n % 256) as uint8] +
            int_to_bytes(n / 256, length-1)
    }

    /**
     * Deserialise a sequence of bytes to `uint64` using little endian
     * interpretation
     *
     * @param s Sequence of bytes. Must be no longer than 8 bytes.
     * 
     * @returns A `uint64` value corresponding to the little endian
     * deserialisation of `s`
     */
    function bytes_to_int(s: bytes):uint64
    requires |s| <= 8 
    ensures bytes_to_int(s) as nat < power(256,|s|)
    {
        reveal_power();
        if(|s| == 0) then
            0
        else
            calc ==> {
                bytes_to_int(s[1..]) as nat < power(256,|s|-1);
                bytes_to_int(s[1..]) as nat * 256 < power(256,|s|);
                bytes_to_int(s[1..]) as nat * 256 < power(256,8);
            }
            s[0] as uint64 + bytes_to_int(s[1..])*256
    }

    /** `bytes_to_int` is the inverse of `int_to_bytes` */
    lemma lemmaBytesToIntIsTheInverseOfIntToBytes(n: uint64, length: uint64)
    requires int_to_bytes.requires(n,length)
    ensures bytes_to_int(int_to_bytes(n,length)) == n 
    {
        // Thanks Dafny
    }

    /** `int_to_bytes` is the inverse of `bytes_to_int` */
    lemma lemmaIntToBytesIsTheInverseOfBytesToInt(s: bytes)
    requires bytes_to_int.requires(s)
    ensures int_to_bytes(bytes_to_int(s),|s| as uint64) == s 
    { 
        if(|s|==0)
        {
            // Thanks Dafny
        }
        else
        {
            calc == {
                int_to_bytes(bytes_to_int(s),|s| as uint64);
                int_to_bytes(s[0] as uint64 + bytes_to_int(s[1..])*256,|s| as uint64);
                [s[0]] + int_to_bytes(bytes_to_int(s[1..]),(|s|-1) as uint64);
                // via induction
                [s[0]] + s[1..];
                s;
            }
        }
    }    
}

