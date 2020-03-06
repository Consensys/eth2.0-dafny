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

    /** Last element of encoding. */
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
    {
        //  Thanks Dafny
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

    /** Simplify  bytesToBitList.
     *
     *  For seq of length >= 1, bytesToBitList can be simplified.
     */
    lemma {:induction m} simplifyByteToListFirstArg(b : Byte, m : seq<Byte>) 
        ensures bytesToBitList([b] + m) == 
            byteToList8Bits(b) + bytesToBitList(m) 
    { //  Dafny proves it.
    }

    /**
     *  Decoding and encoded l : seq<bool> returns l. 
     */
    lemma {:induction l} decodeEncodeIsIdentity(l : seq<bool>) 
        requires | l | % 8 == 0
        ensures bytesToBitList( bitListToBytes (l) ) == l 
        {
            if ( l == [] ) {
                //  Dafny figures it out.
            } else {
                calc == {
                    bytesToBitList( bitListToBytes (l) ) ; 
                    == //   Definition of bitListToBytes
                    bytesToBitList([list8BitsToByte(l[..8])] + bitListToBytes(l[8..]));
                    == { simplifyByteToListFirstArg(
                            list8BitsToByte(l[..8]),
                            bitListToBytes(l[8..])
                            ) ; 
                        }
                     byteToList8Bits(list8BitsToByte(l[..8])) + 
                                bytesToBitList(bitListToBytes(l[8..]));
                    == { decodeOfEncodeIsIdentity(l[..8]); }
                    l[0..8] +  bytesToBitList(bitListToBytes(l[8..]));
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