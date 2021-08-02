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

include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "Constants.dfy"

/**
 *  Helpers to convert list of bits into uint8 and back
 *
 */
module BytesAndBits {

    import opened Eth2Types
    import opened Constants
    import opened Helpers

    /** Convert a boolean into a byte.
     *
     *  @param      b   A boolean.
     *  @returns        A byte (uint8) such that b?1:0. 
     */
    function method boolToByte(b : bool) : byte
        ensures 0 <= boolToByte(b) <= 1  
    {
        (if b then 1 else 0) as byte
    }

    /**
     *  Convert a byte into a boolean.
     *
     *  @param      b   A byte between 0 and 1.
     *  @returns        The corresponding boolean (b == 1)?true:false.
     */
    function method byteToBool(b : byte) : bool
        requires 0 <= b <= 1
    {
        b == 1
    }

    /**
     *  Check if a sequence of booleans contains only false.
     *  
     *  @param  l   A sequence of bits.
     *  @returns    true iff all the bits in l are false. 
     *
     *  @note       isNull([]) is vacuously true (the forall trivially holds).
     */
    predicate isNull(l : seq<bool>) 
    {
        forall i | 0 <= i < |l| :: !l[i]
    }

    //  The following methods convert 8 bits to byte and byte to 8 bits

    /**
     *  Convert a list of 8 bits into a number. Little endian assumed.
     *
     *  @param  l   A sequence of bits.
     *  @returns    A byte the binary encoding of which is reverse(l).
     */
    function method list8BitsToByte(l : seq<bool>) : byte    
        requires |l| == 8 == BITS_PER_BYTE
        ensures isNull(l) <==> list8BitsToByte(l) == 0
    {
        128 * boolToByte(l[7]) +
        64 * boolToByte(l[6]) +
        32 * boolToByte(l[5]) +
        16 * boolToByte(l[4]) +
        8 * boolToByte(l[3]) +
        4 * boolToByte(l[2]) +
        2 * boolToByte(l[1]) +
        1 * boolToByte(l[0])
    }

    /**
     *  Compute a byte into a seq of 8 bits. Little endian assumed. 
     *
     *  @param  n   A byte, i.e. a number that can be represented with 8 bits.
     *  @returns    A sequence of bits `l` such `reverse(l)` is the binary encoding of `n`. 
     */
    function method byteTo8Bits( n : byte ) : seq<bool>
        ensures | byteTo8Bits(n) | == 8 == BITS_PER_BYTE
    {
        [
            byteToBool((n / 1) % 2),
            byteToBool((n / 2) % 2),
            byteToBool((n / 4) % 2), 
            byteToBool((n / 8) % 2),
            byteToBool((n / 16) % 2),
            byteToBool((n / 32) % 2),
            byteToBool((n / 64) % 2),
            byteToBool((n / 128) % 2)
        ]
    }

    /**
     *  Encode a list of bits into a sequence of bytes, padding with zeros.
     *
     *  The algorithm to encode list of bits into seq of bytes works as follows:
     *      1.  split the list into chunks of 8 bits and encode each one into a byte
     *      2.  if last chunk does not have 8 bits, pad with zeros and make a byte.
     *
     *  @example: l1 = [0,1,0,0] is padded with [0,0,0,0] to obtain [0,1,0,0, 0,0,0,0] 
     *  and this encoded into a byte (little endian). The hexadecimal value is 
     *  thus 0x02: 0000.0010 (in `l1` the bits are ordered from little l1[0]to big l1[7])
     *  @example: with more than one byte needed l2 = [1] * 9 and |l| == 9.
     *  The encoding of l2 is: [1111.1111, 0000.0001] i.e. [0xFF , 0x01] 
     *  
     */
    function method fromBitsToBytes(l : seq<bool>) : seq<byte> 
        ensures  | fromBitsToBytes(l) | == ceil( |l|, BITS_PER_BYTE)
        ensures |l| >= 1 && l[|l| - 1] ==> fromBitsToBytes(l)[|fromBitsToBytes(l)| - 1] >= 1
        decreases l
    {
        if ( |l| == 0) then
            []
        else if ( |l| < BITS_PER_BYTE ) then 
            //  pad to 1 byte
            [ list8BitsToByte( l + FALSE_BYTE[.. (BITS_PER_BYTE - |l| % BITS_PER_BYTE)])]
        else if ( |l| == BITS_PER_BYTE ) then
            //  No need to pad as |l| % 8 == 0.
            [ list8BitsToByte(l) ]
        else  
            //  Encode first element and recursively encode the rest.
            [ list8BitsToByte(l[..BITS_PER_BYTE]) ] + fromBitsToBytes(l[BITS_PER_BYTE..])
    }

    //  Some useful properties.

    /** 
     *  Encode(decode(n)) = Identity(n).
     *  
     *  @param  n   a number.
     *  @returns    Encoding (as a byte) the decoded version of `n` yields `n`.
     */
    lemma encodeOfDecodeByteIsIdentity(n: byte)  
        ensures list8BitsToByte(byteTo8Bits(n)) == n 
    {
        // The following two lemmas help reduce the verification time
        lemmaBoolToByteIsTheInverseOfByteToBool();
        lemmaHelperForEncodeOfDecodeByteIsIdentity(n);
    }

    /**
     * `boolToByte` is the inverse of `byteToBool`
     */
    lemma lemmaBoolToByteIsTheInverseOfByteToBool()
    ensures forall b | 0 <= b <= 1 :: boolToByte(byteToBool(b)) == b;
    {
        // Thanks Dafny.
    }

    /**
     * Helper lemma for the `encodeOfDecodeByteIsIdentity` lemma
     */
    lemma lemmaHelperForEncodeOfDecodeByteIsIdentity(n:byte)
    ensures forall i | i in {1,2,4,8,16,32,64} :: (n%(i*2)/i*i) == i * boolToByte(byteToBool((n/i)%2)); 
    ensures (n/128*128) == 128 * boolToByte(byteToBool((n/128)%2));
    {
        // Thanks Dafny.
    }

    /** 
     *  Decode(encode(l)) = Identity(l).
     *  
     *  @param  l   a list of 8 bits.
     *  @returns    Decoding (as a list of bits) the encoded version of `l` yields `l`.
     *
     */    
    lemma decodeOfEncode8BitsIsIdentity(l : seq<bool>) 
        requires |l| == 8 == BITS_PER_BYTE
        ensures byteTo8Bits(list8BitsToByte(l)) == l 
    {   //  Thanks Dafny.
    }

    /** 
     *  Zero is the only byte represented by the null sequence.
     *
     *  @param  n   A byte
     */
    lemma byteIsZeroIffBinaryIsNull(n : byte) 
        ensures n == 0 <==> isNull(byteTo8Bits(n))
    {
        calc <==> {
            n == 0;
            <==> {  //   This can be omitted as Dafny  uses it anyway. 
                    encodeOfDecodeByteIsIdentity(n); 
                 } 
            list8BitsToByte(byteTo8Bits(n)) == 0;
            <==>  //    Ensures of list8BitsToByte
            isNull(byteTo8Bits(n));
        }
    }
}