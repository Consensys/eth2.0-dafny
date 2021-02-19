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

include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "../utils/MathHelpers.dfy"
include "../utils/SeqHelpers.dfy"
include "BytesAndBits.dfy"
include "Constants.dfy"

/**
 *  vector<Boolean> serialisation, desrialisation.
 *
 */
 module BitVectorSeDes {

    import opened NativeTypes
    import opened Eth2Types
    import opened BytesAndBits
    import opened Helpers
    import opened MathHelpers
    import opened SeqHelpers
    import opened Constants


    /**
     *  Encode a vector of bits into a sequence of bytes.
     *
     *  This is the inductive specification of serialise for bitvector.
     *  The `method` attribute makes it executable.
     *  This recursive function always terninates (decreases l).
     *
     *  The algorithm to encode a vector of bits works as follows:
     *  1. given a vector of bits l, 
     *  2. if |l| * 8 is not 0, append 8 - |l| % 8 zeros to l 
     *     to obtain a list of size multiple of 8
     *     let l' = l + possibly some [0]
     *     This ensures that |l'| % 8 == 0 and can be seen as a sequence of Bytes
     *  3. Encode l' with the `list8BitsToByte` algorithm.
     *
     *  @example: l = [0,1,0,0] yields l' = [0,1,0,0] + [0,0,0,0]
     *  (add 4 0es to ensure the size of l' is multiple of 8).
     *  l' is a byte and is encoded as a uint8 `n` as follows: the bitvector 
     *  representation of n is reverse(l'). `n` in hexadecimal is thus: 0000.0010 
     *  which is the uint8 0x02.
     *  
     */
    function method {:induction l} fromBitvectorToBytes(l : seq<bool>) : seq<byte> 
        requires |l| > 0
        ensures | fromBitvectorToBytes(l) | == ceil( |l|, BITS_PER_BYTE)
        ensures | fromBitvectorToBytes(l) | > 0
        ensures (|l| % BITS_PER_BYTE) != 0 
                    ==>
                        fromBitvectorToBytes(l)[|fromBitvectorToBytes(l)|-1] as nat < power2(|l|% BITS_PER_BYTE);        
        decreases l
    {
        if ( |l| <= BITS_PER_BYTE ) then
            [ list8BitsToByte( l + timeSeq(false,BITS_PER_BYTE - |l|)) ]
        else  
            //  Encode first 8 bits and recursively encode the rest.
            [ list8BitsToByte(l[..BITS_PER_BYTE]) ] + fromBitvectorToBytes(l[BITS_PER_BYTE..])
    }

    /**
     *  Decode a sequence of bytes into vector of bits
     *  
     *  This is the inductive specification of deserialise for bitvector.
     *  The `method` attribute turns it into an executable recursive function
     *  and always terminates (decreases xb).
     *
     *  @param  xb  A non-empty sequence of bytes, the last element
     *              of which is >= power2(len % 8) if len % 8 != 0.
     *  @returns    The deserialised bitvector.
     */
    function method fromBytesToBitVector(xb : seq<byte>, len: nat) : seq<bool> 
        requires |xb| > 0
        requires len <= |xb| * BITS_PER_BYTE < len + BITS_PER_BYTE
        ensures |fromBytesToBitVector(xb,len)| == len
        decreases xb
    {
        if ( |xb| == 1 ) then 
            //  Remove suffix 0*.
            byteTo8Bits(xb[0])[.. len] 
        else 
            //  Recursive decoding.
            byteTo8Bits(xb[0]) + fromBytesToBitVector(xb[1..], len - BITS_PER_BYTE)
    }

    //  Main proofs  

    /**
     *  Decoding of encoded bitvector l returns l. 
     */
    lemma {:induction l} bitvectorDecodeEncodeIsIdentity(l : seq<bool>)
        requires |l| > 0
        ensures fromBytesToBitVector( fromBitvectorToBytes (l), |l| ) == l 
    {
        //  The structure of the proof is split in 2 cases to follow
        //  the definition of fromBitvectorToBytes and make it easier to prove
        if(|l| <= BITS_PER_BYTE) {
            decodeOfEncode8BitsIsIdentity(l + timeSeq(false,BITS_PER_BYTE - |l|)); 
        }
        else {
            calc == {
                fromBytesToBitVector( fromBitvectorToBytes (l), |l| );
                fromBytesToBitVector([ list8BitsToByte(l[..BITS_PER_BYTE]) ] + fromBitvectorToBytes(l[BITS_PER_BYTE..]), |l|);
                { decodeOfEncode8BitsIsIdentity(l[..BITS_PER_BYTE]); }
                l[..BITS_PER_BYTE] + fromBytesToBitVector(fromBitvectorToBytes(l[BITS_PER_BYTE..]), |l| - BITS_PER_BYTE);
                l[..BITS_PER_BYTE] + l[BITS_PER_BYTE..];
                l;
            }
        }
    }

    /**
     *  Bitvector encoding of a decoded `xb` returns `xb`.
     */
    lemma  {:induction xb} bitvectorEncodeDecodeIsIdentity(xb: seq<byte>, len:nat) 
        requires |xb| > 0
        requires len <= |xb| * BITS_PER_BYTE < len + BITS_PER_BYTE
        ensures fromBitvectorToBytes( fromBytesToBitVector(xb, len)) == xb
        decreases xb
    {
        //  The structure of the proof is split in 2 cases to follow
        //  the definition of fromBytesToBitVector and make it easier to prove
        if ( |xb| == 1) 
        {
            calc == {
                fromBitvectorToBytes(fromBytesToBitVector(xb,len));
                fromBitvectorToBytes(byteTo8Bits(xb[0])[.. len] );
                [ list8BitsToByte( byteTo8Bits(xb[0])[.. len] + timeSeq(false,BITS_PER_BYTE - len)) ];
                { assume byteTo8Bits(xb[0])[.. len] + timeSeq(false,BITS_PER_BYTE - len) == byteTo8Bits(xb[0]);}
                [ list8BitsToByte( byteTo8Bits(xb[0])) ];
                    {encodeOfDecodeByteIsIdentity(xb[0]);}
                [xb[0]];
            }
        } else { // |xb| > 1 
            calc == {
                fromBitvectorToBytes(fromBytesToBitVector(xb,len));
                fromBitvectorToBytes(byteTo8Bits(xb[0]) + fromBytesToBitVector(xb[1..], len-BITS_PER_BYTE));
                { encodeOfDecodeByteIsIdentity(xb[0]); }
                [xb[0]] + fromBitvectorToBytes(fromBytesToBitVector(xb[1..], len-BITS_PER_BYTE));
                { bitvectorEncodeDecodeIsIdentity(xb[1..], len-BITS_PER_BYTE); }
                [xb[0]] + xb[1..];
                xb;
            }
        }
    }

    /**
     *  Serialise is injective for bitvector of the same length.
     */
    lemma {:induction l1, l2} bitvectorSerialiseIsInjectiveGeneral(l1: seq<bool>, l2 : seq<bool>)
        requires |l1| > 0 
        requires |l2| > 0
        requires |l1| == |l2|
        ensures fromBitvectorToBytes(l1) == fromBitvectorToBytes(l2) ==> l1 == l2 
    {
        calc ==> {
            fromBitvectorToBytes(l1) == fromBitvectorToBytes(l2) ;
            ==> { bitvectorDecodeEncodeIsIdentity(l1) ; bitvectorDecodeEncodeIsIdentity(l2) ; }
            l1 == l2 ;
        }
    }   

    /**
     *  Deserialise is injective for bitvectors.
     */
    lemma {:induction xa, xb} bitvectorDeserialiseIsInjective(xa: seq<byte>, xb : seq<byte>, lena: nat, lenb: nat)
        requires |xa| > 0
        requires lena <= |xa| * BITS_PER_BYTE < lena + BITS_PER_BYTE
        requires |xb| > 0
        requires lenb <= |xb| * BITS_PER_BYTE < lenb + BITS_PER_BYTE
        ensures fromBytesToBitVector(xa,lena) == fromBytesToBitVector(xb,lenb) ==> xa == xb 
    {
        calc ==> {
            fromBytesToBitVector(xa,lena) == fromBytesToBitVector(xb,lenb) ;
            ==> {
                bitvectorEncodeDecodeIsIdentity(xa,lena) ; bitvectorEncodeDecodeIsIdentity(xb, lenb) ;
            }
            xa == xb ;
        }
    }

}