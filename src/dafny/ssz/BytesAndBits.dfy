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


include "../utils/Eth2Types.dfy"

/**
 *  Helpers to convert list of bits into uint8 and back
 *
 */
module BytesAndBits {

    import opened Eth2Types

    /** Convert a boolean into a Byte.
     *
     *  @param      b   A boolean.
     *  @returns        A Byte (uint8) such that b?1:0. 
     */
    function method boolToByte(b : bool) : Byte
        ensures 0 <= boolToByte(b) <= 1  
    {
        (if b then 1 else 0) as Byte
    }

    /**
     *  Convert a Byte into a boolean.
     *
     *  @param      b   A byte between 0 and 1.
     *  @returns        The corresponding boolean (b == 1)?true:false.
     */
    function method byteToBool(b : Byte) : bool
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

    /**
     *  Convert a list of 8 bits into a number.
     *
     *  @param  l   A sequence of bits.
     *  @returns    A byte the binary encoding of which is reverse(l).
     */
    function method list8BitsToByte(l : seq<bool>) : Byte    
        requires |l| == 8 
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
     *  Compute a list of bits given a Byte.
     *
     *  @param  n   A byte, i.e. a number that can be represented with 8 bits.
     *  @returns    A sequence of bits `l` such `reverse(l)` is the binary encoding of `n`. 
     */
    function method byteTo8Bits( n : Byte ) : seq<bool>
        ensures | byteTo8Bits(n) | == 8 
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

    //  Some useful properties.

    /** 
     *  Encode(decode(n)) = Identity(n).
     *  
     *  @param  n   a number.
     *  @returns    Encoding (as a Byte) the decoded version of `n` yields `n`.
     */
    lemma encodeOfDecodeByteIsIdentity(n: Byte)  
        ensures list8BitsToByte(byteTo8Bits(n)) == n 
    {   //  Thanks Dafny.
    }

    /** 
     *  Decode(encode(l)) = Identity(l).
     *  
     *  @param  l   a list of 8 bits.
     *  @returns    Decoding (as a list of bits) the encoded version of `l` yields `l`.
     *
     */    
    lemma decodeOfEncode8BitsIsIdentity(l : seq<bool>) 
        requires |l| == 8
        ensures byteTo8Bits(list8BitsToByte(l)) == l 
    {   //  Thanks Dafny.
    }

    /** 
     *  Zero is the only byte represented by the null sequence.
     *
     *  @param  n   A Byte
     */
    lemma byteIsZeroIffBinaryIsNull(n : Byte) 
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