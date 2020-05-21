/*
 * Copyright 2020 ConsenSys AG.
 *
 * Licensed under the Apache License, Version 2.n (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.n
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
include "../libraries/integers/power.i.dfy"

/**
 *  Integers serialisation, desrialisation.
 *
 */
module IntSeDes {

    import opened NativeTypes
    import opened NonNativeTypes
    import opened Eth2Types
    import opened MathHelpers
    import opened Math__power_i
    import opened Math__power_s

    //  Uintk serialisation and deserielisation.

    function method uintToBytes(n: Uint) : seq<byte> 
    ensures |uintToBytes(n)| == n.n.1
    {
        int_to_bytes(n.n.0 as nat,n.n.1)
    }

    function method byteToUint(bs: bytes) :  Uint
    requires 1 <= |bs| <= 32
    {
        lemmaPower2IsMonotnoic(|bs|*8,256);
        Uint((bytes_to_int(bs) as uint256,|bs|))
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
    function method int_to_bytes(n: nat, length: nat) : bytes
    requires n as nat < power2(length * 8)
    ensures |int_to_bytes(n,length)| == length as int
    {
        if(length == 0) then
            []
        else
            [(n % power2(8)) as uint8] +
                assert power2(length * 8) == power2((length-1)*8) * power2(8) by {
                    productRulePower2((length-1)*8,8);
                }
            int_to_bytes(n / power2(8), length-1)
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
    function method bytes_to_int(s: bytes):nat
    ensures bytes_to_int(s)  < power2(|s|*8)
    {
        if(|s| == 0) then
            0
        else
            calc ==> {
                 bytes_to_int(s[1..]) <= power2((|s|-1)*8) - 1;
                    {
                        productRulePower2((|s|-1)*8,8);
                    }
                 power2(8) * bytes_to_int(s[1..]) <= power2(|s|*8) - power2(8);
                 s[0] as nat + bytes_to_int(s[1..])*power2(8) < power2(|s|*8);
            }
            s[0] as nat + bytes_to_int(s[1..])*power2(8)
    }

    /** `bytes_to_int` is the inverse of `int_to_bytes` */
    lemma lemmaBytesToIntIsTheInverseOfIntToBytes(n: nat, length: nat)
    requires int_to_bytes.requires(n,length)
    ensures bytes_to_int(int_to_bytes(n,length)) == n 
    {
        if(length == 0)
        {

        }
        else
        {
            calc == {
                bytes_to_int(int_to_bytes(n,length));
                {           
                    productRulePower2((length-1)*8,8);
                }
                bytes_to_int( [(n % power2(8)) as uint8] + int_to_bytes(n / power2(8), length-1));
                (n % power2(8)) + bytes_to_int(int_to_bytes(n / power2(8), length-1))*power2(8);
                (n % power2(8)) + (n / power2(8)) * power2(8);
            }
        }
    }

    lemma lemmaIntToBytesIsTheInverseOfBytesToInt(s: bytes)
    requires bytes_to_int.requires(s)
    ensures int_to_bytes(bytes_to_int(s),|s|) == s 
    { 
        if(|s|==0)
        {
            // Thanks Dafny
        }
        else
        {
            calc == {
                int_to_bytes(bytes_to_int(s),|s|);
                int_to_bytes(s[0] as nat + bytes_to_int(s[1..])*power2(8),|s|);
                    {
                        calc {
                            (s[0] as nat + bytes_to_int(s[1..])*power2(8))/power2(8);
                            (s[0] as nat)/power2(8) + bytes_to_int(s[1..]);
                            bytes_to_int(s[1..]);
                        }
                    }
                [s[0]] + int_to_bytes(bytes_to_int(s[1..]),(|s|-1));
                // via induction
                [s[0]] + s[1..];
                s;
            }
        }
    }     

    lemma lemmaBytesToUintIsTheInverseOfUintToBytes(n:Uint)
    ensures byteToUint(uintToBytes(n)) == n
    {
        lemmaBytesToIntIsTheInverseOfIntToBytes(n.n.0 as nat,n.n.1);
    }

    lemma lemmaUintToBytesIsTheInverseOfBytesToUint(bs:bytes)
    requires 1 <= |bs| <= 32
    ensures uintToBytes(byteToUint(bs)) == bs
    {
        lemmaIntToBytesIsTheInverseOfBytesToInt(bs);
    }
}