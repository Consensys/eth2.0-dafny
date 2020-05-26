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
include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "../utils/SeqHelpers.dfy"
include "BytesAndBits.dfy"
include "Constants.dfy"

/**
 *  list<Boolean> serialisation, desrialisation.
 *
 */
 module BitListSeDes {

    import opened NativeTypes
    import opened Eth2Types
    import opened BytesAndBits
    import opened Helpers
    import opened SeqHelpers
    import opened Constants

    /**
     *  Compute largest index in l with a true value.
     *
     *  @param      l   A sequence of 8 bits, containing at least one true bit.
     *  @returns        The largest index with a true bit.
     *
     *  @example        0100_0001 returns 7, 1000_1000 returns 4,
     *                  1110_1010 returns 6.
     *  
     */
    function method largestIndexOfOne(l : seq<bool>) : nat 
        requires |l| == BITS_PER_BYTE == 8
        requires exists i: nat | 0 <= i < |l| :: l[i]
        ensures 0 <= largestIndexOfOne(l) < |l| 
        ensures l[largestIndexOfOne(l)] == true
        ensures forall i : nat | largestIndexOfOne(l) < i < |l| :: l[i] == false
    {
        if l[7] then 7
        else if l[6] then 6
        else if l[5] then 5
        else if l[4] then 4
        else if l[3] then 3
        else if l[2] then 2
        else if l[1] then 1
        else 0
    }
 
    /**
     *  Encode a list of bits into a sequence of bytes.
     *
     *  This is the inductive specification of serialise for bitlists.
     *  The `method` attribute makes it executable.
     *  This recursive function always terninates (decreases l).
     *
     *  The algorithm to encode list of bits works as follows:
     *  1. given a list of bits l, 
     *  2. append 1 to l, this is a sentinnelle, and let l' = l + [1] 
     *  3. if |l'| * 8 is not 0, append 8 - (|l| + 1) % 8 zeros to l' 
     *     to obtain a list of size multiplw of 8
     *     let l'' = l' + possibly some [0]
     *     This ensures that |l''| % 8 == 0 and can be seen as a sequence of Bytes
     *  4. Encode l'' with the `list8BitsToByte` algorithm.
     *
     *  @example: l = [0,1,0,0] yields l' = [0,1,0,0] + [1]
     *  l'' = [0,1,0,0,1] + [0,0,0] (add 3 0's to ensure the size of l'' is 
     *  multiple of 8).
     *  l'' is a byte and is encoded as a uint8 `n` as follows: the bitvector 
     *  representation of n is reverse(l''). `n` in hexadecimal is thus: 0001.0010 
     *  which is the uint8 0x12.
     *
     *  @example: with more than one byte needed l = [0] * 8 and |l| == 8.
     *  l' = [0] * 8 + [1], l'' = [0] * 8 + [1] + [0] * 7
     *  Reverse(l'') = [0] * 7 + [1] + [0] * 8
     *  and the encoding of l is: [1000.0000, 0000.0000] i.e. [0x01 , 0x00] 
     *  
     */
    function method fromBitlistToBytes(l : seq<bool>) : seq<byte> 
        ensures | fromBitlistToBytes(l) | == ceil( |l| + 1, BITS_PER_BYTE)
        ensures fromBitlistToBytes(l)[|fromBitlistToBytes(l)| - 1] >= 1
        
        decreases l
    {
        if ( |l| < BITS_PER_BYTE - 1 ) then 
            //  8 - (|l| + 1) % 8 = 8 for |l| == 7 so we need to pad.
            [ list8BitsToByte( l + [true] + FALSE_BYTE[.. (BITS_PER_BYTE - (|l| + 1) % BITS_PER_BYTE )])]
        else if ( |l| == BITS_PER_BYTE - 1 ) then
            //  No need to pad as |l + [true]| % 8 == 0.
            [ list8BitsToByte( l + [true]) ]
        else  
            //  Encode first 8 bits and recursively encode the rest.
            [ list8BitsToByte(l[..BITS_PER_BYTE]) ] + fromBitlistToBytes(l[BITS_PER_BYTE..])
    }

    /**
     *  Decode a sequence of bytes into seq<bool>.
     *  
     *  This is the inductive specification of deserialise for bitlists.
     *  The `method` attribute turns it into an executable recursive function
     *  and always terminates (decreases xb).
     *
     *  @param  xb  A non-empty sequence of bytes, the last element
     *              of which is >= 1.
     *  @returns    The sequence of bits upto (and except) the last true bit. 
     */
    function method fromBytesToBitList(xb : seq<byte>) : seq<bool> 
        requires |xb| >= 1
        requires xb[|xb|-1] >= 1
        ensures BITS_PER_BYTE * (|xb| - 1) >= 0
        ensures BITS_PER_BYTE * (|xb| - 1) <= |fromBytesToBitList(xb)| <= BITS_PER_BYTE * |xb|

        decreases xb
    {
        //  Last element e = xb[|xb| - 1] >= 1 implies byteTo8Bits(e) != [0] * 8
        byteIsZeroIffBinaryIsNull(xb[|xb| - 1]);
        assert !isNull(byteTo8Bits(xb[|xb| - 1])) ;
        if ( |xb| == 1 ) then 
            //  Remove suffix 1 0*.
            byteTo8Bits(xb[0])[.. largestIndexOfOne(byteTo8Bits(xb[0]))] 
        else 
            //  Recursive decoding.
            byteTo8Bits(xb[0]) + fromBytesToBitList(xb[1..])
    }

    //  Main proofs  

    /**
     *  Decoding of encoded l returns l. 
     */
    lemma {:induction l} bitlistDecodeEncodeIsIdentity(l : seq<bool>) 
        ensures fromBytesToBitList( fromBitlistToBytes (l) ) == l 
    {
        //  The structure of the proof is split in 3 cases to follow
        //  the definition of fromBitlistToBytes and make it easier to prove
        if ( |l| < BITS_PER_BYTE - 1 ) {
            //  Thanks Dafny
        } else if ( |l| == BITS_PER_BYTE - 1 ) {
            //  Thanks Dafny
        } else {
            calc == {
                fromBytesToBitList( fromBitlistToBytes (l) );
                == //   Definition of fromBitlistToBytes
                fromBytesToBitList([list8BitsToByte(l[..BITS_PER_BYTE])] + fromBitlistToBytes(l[BITS_PER_BYTE..]));
                == { simplifyFromByteToListFirstArg(
                        list8BitsToByte(l[..BITS_PER_BYTE]), 
                        fromBitlistToBytes(l[BITS_PER_BYTE..])
                        ) ;  
                }
                byteTo8Bits(list8BitsToByte(l[..BITS_PER_BYTE])) + 
                    fromBytesToBitList(fromBitlistToBytes(l[BITS_PER_BYTE..]));
                == { decodeOfEncode8BitsIsIdentity(l[..BITS_PER_BYTE]); }
                l[0..BITS_PER_BYTE] + fromBytesToBitList(fromBitlistToBytes(l[BITS_PER_BYTE..]));
                ==  //  Induction on l[8..]. 
                    //  This last step can be ommitted as Dafny figures it out.
                l[0..BITS_PER_BYTE] + l[BITS_PER_BYTE..];
            }
        }
    }

    /**
     *  Encoding a decoded `xb` returns `xb`.
     */
    lemma {:induction xb} bitlistEncodeDecodeIsIdentity(xb: seq<byte>) 
        requires |xb| >= 1
        requires xb[|xb| - 1] >= 1
        ensures fromBitlistToBytes(fromBytesToBitList(xb)) == xb
    {
        if ( |xb| == 1 ) {
            if( xb[0] >= 0x80)
            {
                calc == {
                    fromBitlistToBytes(fromBytesToBitList(xb)) ;
                    fromBitlistToBytes(byteTo8Bits(xb[0])[.. largestIndexOfOne(byteTo8Bits(xb[0]))]);
                    [ list8BitsToByte( byteTo8Bits(xb[0])[.. 7] + [true]) ];
                    [ list8BitsToByte( byteTo8Bits(xb[0]))];
                        {encodeOfDecodeByteIsIdentity(xb[0]);}
                    xb;
                }
            }
            else
            {
                calc == {
                    fromBitlistToBytes(fromBytesToBitList(xb)) ;
                    fromBitlistToBytes(byteTo8Bits(xb[0])[.. largestIndexOfOne(byteTo8Bits(xb[0]))]);
                }

                var bl:= byteTo8Bits(xb[0])[.. largestIndexOfOne(byteTo8Bits(xb[0]))];
                var blPadded:= bl + [true] + FALSE_BYTE[.. (BITS_PER_BYTE - (|bl| + 1) % BITS_PER_BYTE )];

                calc == {
                    fromBitlistToBytes(byteTo8Bits(xb[0])[.. largestIndexOfOne(byteTo8Bits(xb[0]))]);
                    [ list8BitsToByte(blPadded)];
                    [ list8BitsToByte( byteTo8Bits(xb[0]))];
                        {encodeOfDecodeByteIsIdentity(xb[0]);}
                    xb;
                }
            }
        } else {
            calc == {
                fromBitlistToBytes(fromBytesToBitList(xb)) ;
                ==  //  Definition of fromBytesToBitList
                fromBitlistToBytes(byteTo8Bits(xb[0]) + fromBytesToBitList(xb[1..])) ;
                == { simplifyFromBitListToByteFirstArg(
                        xb[0],
                        fromBytesToBitList(xb[1..])
                    ) ;
                }
                [xb[0]] + fromBitlistToBytes(fromBytesToBitList(xb[1..])); 
                ==  //  Induction on xb[1..]
                    //  This last step can be ommitted as Dafny figures it out.
                 [xb[0]] + xb[1..];
            }
        }
    }

    /**
     *  Serialise is injective for bitlists.
     */
    lemma {:induction l1, l2} bitlistSerialiseIsInjective(l1: seq<bool>, l2 : seq<bool>)
        ensures fromBitlistToBytes(l1) == fromBitlistToBytes(l2) ==> l1 == l2 
    {
        calc ==> {
            fromBitlistToBytes(l1) == fromBitlistToBytes(l2) ;
            ==> { bitlistDecodeEncodeIsIdentity(l1) ; bitlistDecodeEncodeIsIdentity(l2) ; }
            l1 == l2 ;
        }
    }

    /**
     *  Deserialise is injective for sequences of bytes.
     */
    lemma {:induction xa, xb} bitlistDeserialiseIsInjective(xa: seq<byte>, xb : seq<byte>)
        requires |xa| >= 1
        requires xa[|xa| - 1] >= 1
        requires |xb| >= 1
        requires xb[|xb| - 1] >= 1
        ensures fromBytesToBitList(xa) == fromBytesToBitList(xb) ==> xa == xb 
    {
        calc ==> {
            fromBytesToBitList(xa) == fromBytesToBitList(xb) ;
            ==> {
                bitlistEncodeDecodeIsIdentity(xa) ; bitlistEncodeDecodeIsIdentity(xb) ;
            }
            xa == xb ;
        }
    }

    //  Simplifications in first argument.

    /**
     *  Rewriting (simplification) rule for fromBytesToBitList.
     */
    lemma {:induction m} simplifyFromByteToListFirstArg(b : byte, m : seq<byte>) 
        requires |m| >= 1
        requires m[|m| - 1] >= 1
        ensures fromBytesToBitList([b] + m) == 
            byteTo8Bits(b) + fromBytesToBitList(m) 
    { 
        if ( |m| == 0 ) {
            calc {
                fromBytesToBitList([b] + m) ;
                == { seqElimEmpty([b]); }
                fromBytesToBitList([b]);
                == //   Definition of fromBytesToBitList
                byteTo8Bits(b) ;
                == { seqElimEmpty(byteTo8Bits(b)) ; }
                byteTo8Bits(b) + [];
                == calc {
                    fromBytesToBitList([]);
                    ==
                    [];
                }
                byteTo8Bits(b) + fromBytesToBitList([]);
            }
        } else {
            calc {
                fromBytesToBitList([b] + m) ;
                == //   Definition of fromBytesToBitList
                byteTo8Bits(b) + fromBytesToBitList(m);
            }
        }
    }

    /**
     *  Rewriting (simplification) rule for fromBitlistToBytes.
     */
    lemma {:induction xl} simplifyFromBitListToByteFirstArg(e: byte, xl : seq<bool>) 
        ensures fromBitlistToBytes(byteTo8Bits(e) + xl) == 
            [ e ] + fromBitlistToBytes(xl) 
    { 
        calc == {
            fromBitlistToBytes(byteTo8Bits(e) + xl);
            == 
            [ list8BitsToByte((byteTo8Bits(e) + xl)[..BITS_PER_BYTE]) ] + 
                fromBitlistToBytes((byteTo8Bits(e) + xl)[BITS_PER_BYTE..]) ; 
            ==  {encodeOfDecodeByteIsIdentity(e);}
            [e] + fromBitlistToBytes((byteTo8Bits(e) + xl)[BITS_PER_BYTE..]) ;
        }
    }

    /**
     *  fromBitlistToBytes surjective on |xb| >= 1 && xb[|xb| - 1] >= 1
     */
    lemma {:induction xb} surjective(xb : seq<byte>) 
        requires |xb| >= 1 
        requires xb[|xb| - 1] >= 1
        ensures exists l : seq<bool> {:induction l} :: xb == fromBitlistToBytes(l) 

        decreases xb
    {
        if ( |xb| == 1 ) {
            var l : seq<bool> := fromBytesToBitList(xb);
            bitlistEncodeDecodeIsIdentity(xb);
        } else {
            //  Induction assumption on xb[1..]
            var xl : seq<bool> :| fromBitlistToBytes(xl) == xb[1..];
            calc == {
                fromBitlistToBytes(byteTo8Bits(xb[0]) + xl) ;
                == {
                    simplifyFromBitListToByteFirstArg(
                        xb[0],
                        xl
                    ) ;
                }
                [xb[0]] + fromBitlistToBytes(xl);
                == 
                xb;
            }
        }
    }
}