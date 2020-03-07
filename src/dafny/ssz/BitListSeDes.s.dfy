include "./BitListSeDes.i.dfy"
include "../utils/Eth2Types.dfy"

/**
 *  list<Boolean> serialisation, desrialisation.
 *
 */
 module BitListSeDes__s {

    import opened Eth2Types
    import opened BitListSeDes__i

    /** Encode(decode(n)) = Identity(n).
     *  
     *  @param  n   a number.
     *  @returns    Encoding (as a Byte) the decoded version of `n` yields `n`.
     */
    lemma encodeOfDecodeIsIdentity(n: Byte)  
        ensures list8BitsToByte(byteToList8Bits(n)) == n 
    {   //  Thanks Dafny.
    }

    /** Decode(encode(l)) = Identity(l).
     *  
     *  @param  l   a list of 8 bits.
     *  @returns    Decoding (as a list of bits) the encoded version of `l` yields `l`.
     *
     */    
     lemma decodeOfEncodeIsIdentity(l : seq<bool>) 
        requires |l| == 8
        ensures byteToList8Bits(list8BitsToByte(l)) == l 
    {   //  Thanks Dafny.
    }

    /** Binary representation of a Byte n is [0] * 8 iff n == 0. */
    lemma byteIsZeroIffBinaryIsNull(n : Byte) 
        ensures n == 0 <==> isNull(byteToList8Bits(n))
    {
        calc <==> {
            n == 0;
            <==>
            list8BitsToByte(byteToList8Bits(n)) == 0;
            <==>  
            isNull(byteToList8Bits(n));
        }
    }

    /**
     *  The spec of the encoding.
     *  
     *  @param  l   A list of bits.
     *  @param  k   A (fake) parameter which must be |l| / 8.
     *  
     *  @enures     Every byte of the encoding except last one
     *              corresponds to a chunk of 8 bits in `l`.
     *  
     */
    lemma allChunksExceptLast(l : seq<bool>, k : nat)
        requires k == |l| / 8 
        ensures forall i : nat | 0 <= i <  ceil ( |l| + 1 , 8) - 1 :: 
            realBitlistToBytes(l)[i] == list8BitsToByte(l[ (i * 8).. (i * 8 + 8)])
    {
        forall ( i : nat ) 
            ensures 0 <= i < ceil ( |l| + 1 , 8) - 1 ==> realBitlistToBytes(l)[i] == list8BitsToByte(l[ (i * 8).. (i * 8 + 8)])
        {
            if ( 0 <= i < ceil ( |l| + 1 , 8) - 1 ) {
                calc == {
                    realBitlistToBytes(l)[i] ;
                    == bitListToBytes(l[.. 8 * k])[i];
                    == { lm(l[.. 8 * k], i);}
                    list8BitsToByte( (l[.. 8 * k])[ (i * 8).. (i * 8 + 8)] );
                }
            }
        }
    }

    /**
     *  Each bitListToBytes(l)[i] of encoding corresponds to the binary reprersentation
     *  of l[ i * 8 + 0], l[ i * 8 + 1], ... l[i * 8 + 7].
     */
    lemma {:induction l} mapByteTo8Bits(l: seq<bool>, i : nat) 
        requires |l| % 8 == 0
        requires 0 <= i < |l| / 8
        ensures 
            bitListToBytes(l)[i] == list8BitsToByte(l[ (i * 8).. (i * 8 + 8)]) 
    {
        encodeChunks8BitsAsBytes(l, |l| / 8);
    }

    /** Property of last Byte of encoding. 
     *  
     *  @param  l   A list of bits.
     *  @param  k   A (fake) parameter which must be |l| / 8.
     *  
     *  @ensures    Last Byte is the encoding of last |l| - (k - 1) * 8 bits
     *              padded with [true, false, ... false].
     */
    lemma {:induction l} lastChunk(l : seq<bool>, k : nat, padding: seq<bool>)
        requires (|l| + 1) % 8 == 0 ==> |padding| == 0
        requires (|l| + 1) % 8 != 0 ==> |padding| == 8 - ((|l| + 1) % 8) 
        requires k ==  ceil ( |l| + 1, 8) 
        requires padding == timeSeq(false, |padding|)

        ensures k >= 1
        ensures (|l| + 1 + |padding|) % 8 == 0 
        ensures |l[(k - 1) * 8 ..]| + 1 + |padding| == 8
        ensures realBitlistToBytes(l)[k - 1] == 
                        list8BitsToByte(l[(k - 1) * 8 ..] + [true] + padding)
    {   //  Thanks Dafny
    }

    /** The last Byte of the encoding is always larger than 1. 
     *  
     *  @param  l   A list of bits.
     *
     *  @ensures    Encoding has at least one byte.
     *  @ensures    The last byte of the encoding is >= 1.
     *
     *  @note: This is because whatever `l` is a 1 or true bit is appended before
     *  the encoding is computed.
     */
    lemma lastChunkLargerNotNull(l : seq<bool>)
        ensures |realBitlistToBytes(l)| >= 1
        ensures realBitlistToBytes(l)[|realBitlistToBytes(l)|-1] >= 1
    {   //  Thanks Dafny
    }

    lemma {:induction xb} last8BitsSameOnSuffix(xb: seq<Byte>, b : Byte) 
        requires |xb| >= 1
        ensures bytesTo8BitList([b] + xb)[8 * |xb|..] == bytesTo8BitList(xb)[8 * (|xb| - 1)..] 
    {   //  Thanks Dafny
    }

    /** Simplify concatenation with [].  
     *
     *  @tparam T   A type.
     *  @param  xb  A sequence of elements.
     *  
     *  @ensures    [] is a nuetral element for Concatenation (left or right) .
     */
    lemma simplifyEmptyConcat<T>(xb: seq<T>) 
        ensures xb + [] == xb 
        ensures [] + xb == xb 
    {   //  Thanks Dafny
    }
    
    /**
     *  Decoding of sequence of Bytes with last Byte >= 1.
     *
     *  @param  xb  A sequence of al least one Byte, such that last one >= 1
     *  
     *  @ensures    One of the last 8 bits of the conversion of `xb` with bytesTo8BitList
     *              is true.
     */
    lemma {:induction xb} lastNonNull(xb: seq<Byte>) 
        requires |xb| >= 1
        requires xb[|xb| - 1] >= 1
        ensures !isNull(bytesTo8BitList(xb)[8 * (|xb| - 1)..])
        
        decreases |xb|
    {
        if ( |xb| == 1 ) {
            //  Base case
            calc <== {
                !isNull(bytesTo8BitList(xb)[8 * (|xb| - 1)..]);
                == 
                !isNull(bytesTo8BitList(xb)[0..]);
                == 
                !isNull(bytesTo8BitList([xb[0]])[0..]);
                ==
                !isNull(byteToList8Bits(xb[0])[0..] + bytesTo8BitList([]));
                //  As bytesTo8BitList([]) == [] it can be simplified
                == { simplifyEmptyConcat(byteToList8Bits(xb[0])[0..]); }
                !isNull(byteToList8Bits(xb[0])[0..]);
                //  For xb[0] a byte, byteToList8Bits(xb[0])[0..] can be simplified.
                == calc == { 
                    byteToList8Bits(xb[0])[0..];
                     == byteToList8Bits(xb[0]);
                }
                !isNull(byteToList8Bits(xb[0])) ;
                == { byteIsZeroIffBinaryIsNull(xb[0]) ; }
                true ;
            }
        } else {
            //  Induction
            lastNonNull(xb[1..]);
            last8BitsSameOnSuffix(xb[1..], xb[0]);
        }
    }
    
    /**
     *  Complete specification of encoding for BitLists.
     *
     *  @param  l           The bitlist to encode.
     *  @param  k           Not really needed as it is fixed but makes the proof 
     *                      easier to read.
     *  @param  pad     
     */
    lemma {:induction pad} bitListEncodingSpec(l : seq<bool>, k : nat, pad : seq<bool>) 

        requires k == ceil ( |l| + 1, 8)
        requires (|l| + 1) % 8 == 0 ==> |pad| == 0
        requires (|l| + 1) % 8 != 0 ==> |pad| == 8 - ((|l| + 1) % 8) 
        requires pad == timeSeq(false, |pad|)

        ensures | realBitlistToBytes(l) | == k
        ensures forall i : nat | 0 <= i <  k - 1 :: 
            realBitlistToBytes(l)[i] == list8BitsToByte(l[ (i * 8).. (i * 8 + 8)])
        ensures realBitlistToBytes(l)[k - 1] == 
                        list8BitsToByte(l[(k - 1) * 8 ..] + [true] + pad)
    {
        forall (i : nat) 
            ensures 0 <= i < ceil ( |l| + 1 , 8) - 1 ==> 
                realBitlistToBytes(l)[i] == list8BitsToByte(l[ (i * 8).. (i * 8 + 8)]) 
            {
                  allChunksExceptLast( l, |l| / 8);     
            }
    }

    //  Proof of involution

    /** Simplify  bytesTo8BitList.
     *
     *  For seq of length >= 1, bytesTo8BitList can be simplified.
     */
    lemma {:induction m} simplifyByteToListFirstArg(b : Byte, m : seq<Byte>) 
        ensures bytesTo8BitList([b] + m) == 
            byteToList8Bits(b) + bytesTo8BitList(m) 
    { //  Dafny proves it.
    }

    /**
     *  Decoding and encoded l : seq<bool> returns l. 
     */
    lemma {:induction l} decodeEncodeIsIdentity(l : seq<bool>) 
        requires | l | % 8 == 0
        ensures bytesTo8BitList( bitListToBytes (l) ) == l 
        {
            if ( l == [] ) {
                //  Dafny figures it out.
            } else {
                calc == {
                    bytesTo8BitList( bitListToBytes (l) ) ; 
                    == //   Definition of bitListToBytes
                    bytesTo8BitList([list8BitsToByte(l[..8])] + bitListToBytes(l[8..]));
                    == { simplifyByteToListFirstArg(
                            list8BitsToByte(l[..8]),
                            bitListToBytes(l[8..])
                            ) ; 
                        }
                     byteToList8Bits(list8BitsToByte(l[..8])) + 
                                bytesTo8BitList(bitListToBytes(l[8..]));
                    == { decodeOfEncodeIsIdentity(l[..8]); }
                    l[0..8] +  bytesTo8BitList(bitListToBytes(l[8..]));
                }
            }
        }

    /**
     *  The result sequence of the encoding encodes successive 
     *  chunks of 8 bits into a Byte.
     *
     *  @requires   A list of bits of size multiple of 8.
     *  @note:      The second parameter k is introduced to make it easier
     *              to reason by induction simultaneously on l and k.
     */
    lemma {:induction l,k} encodeChunks8BitsAsBytes(l: seq<bool>, k : nat) 
        requires |l| == 8 * k
        ensures forall i : nat | 0 <= i < k :: 
            bitListToBytes(l)[i] == list8BitsToByte(l[ (i * 8).. (i * 8 + 8)])
        decreases l, k
    {
        if ( l == [] ) {
            //  Thanks Dafny
        } else {
            forall (i : nat) 
                ensures 0 <= i < k ==> 
                    bitListToBytes(l)[i] == list8BitsToByte(l[ i * 8.. i * 8 + 8]) {
                if ( i > 0 ) {
                    //  for 0 < i < k: 
                    //  Induction assumption on the smaller element l[8..], k - 1
                    encodeChunks8BitsAsBytes(l[8..], k - 1);
                } else {
                    //  for i == 0, thanks Dafny 
                }
            }
        }
    }

    lemma {:induction l} lm(l: seq<bool>, i : nat) 
        requires |l| % 8 == 0
        requires 0 <= i < |l| / 8
        ensures 
            bitListToBytes(l)[i] == list8BitsToByte(l[ (i * 8).. (i * 8 + 8)]) 
    {
        encodeChunks8BitsAsBytes(l, |l| / 8);
    }
 }