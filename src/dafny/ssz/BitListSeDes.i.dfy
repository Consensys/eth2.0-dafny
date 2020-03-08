include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "BytesAndBits.dfy"

/**
 *  list<Boolean> serialisation, desrialisation.
 *
 */
 module BitListSeDes__i {

    import opened NativeTypes
    import opened Eth2Types
    import opened BytesAndBits
    import opened Helpers

    /** Create Sequences with same element. 
     *
     *  @tparam T   A type.
     *  @param  t   An value.
     *  @param  k   A non-negative integer.
     *  @returns    A seq [t,t, ..., t] of size k.
     */
    function method timeSeq<T>(t : T, k : nat) : seq<T> 
        ensures |timeSeq(t,k)| == k
        decreases k
    {
        if k == 0 then []
        else [t] + timeSeq(t, k - 1)
    }

    /**
     *  Compute largest index in l with a true value.
     *
     *  @param      l   A sequence of 8 bits, containign at least one true bit.
     *  @returns        The largest index with a true bit.
     *
     *  @example        0100_0001 returns 7, 1000_1000 returns 4,
     *                  1110_1010 returns 6.
     *  
     */
    function method largestIndexOfOne(l : seq<bool>) : nat 
        requires |l| == 8
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
 
     /** Simplify neutral element [] when concatenating sequence.
     *  
     *  @tparam     T   A type.
     *  @param      xb  A sequence of elements of type `T`.
     */
    lemma simplifyEmptyConcat<T>(xb: seq<T>) 
        ensures xb + [] == xb 
        ensures [] + xb == xb 
    {   //  Thanks Dafny
    }
    
    /**
     *  Encode a list of bits into a sequence of bytes.
     *
     *  This is the inductive specification of serialise for bitlists.
     *  The `method` attribute makes it executable.
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
     *  l'' is a Byte and is encoded as a uint8 `n` as follows: the bitvector 
     *  representation of n is reverse(l''). `n` in hexadecimal is thus: 0001.0010 
     *  which is the uint8 0x12.
     *
     *  @example: with more than one byte needed l = [0] * 8 and |l| == 8.
     *  l' = [0] * 8 + [1], l'' = [0] * 8 + [1] + [0] * 7
     *  Reverse(l'') = [0] * 7 + [1] + [0] * 8
     *  and the encoding of l is: [1000.0000, 0000.0000] i.e. [0x01 , 0x00] 
     *  
     */
    function method fromBitlistToBytes(l : seq<bool>) : seq<Byte> 
        ensures | fromBitlistToBytes(l) | == ceil( |l| + 1, 8)
        ensures fromBitlistToBytes(l)[|fromBitlistToBytes(l)| - 1] >= 1
        
        decreases l
    {
        if ( |l| < 7 ) then 
            //  8 - (|l| + 1) % 8 = 8 for |l| == 7 so we treat it separately.
            [ list8BitsToByte( l + [true] + timeSeq(false, 8 - (|l| + 1) % 8)) ]
        else if ( |l| == 7 ) then
            //  No need to pad.
            [ list8BitsToByte( l + [true]) ]
        else  
            [ list8BitsToByte(l[..8]) ] + fromBitlistToBytes(l[8..])
    }

    /**
     *  Decode a sequence of bytes into seq<bool>.
     *  
     *  This is the inductive specification of deserialsie for bitlists.
     *  The `method` attribute turns it into an executable function.
     *
     *  @param  xb  A non-empty sequence of bytes, the last element
     *              of which is >= 1.
     *  @returns    The sequence of bits upto (and except) the last true bit. 
     */
    function method fromBytesToBitList(xb : seq<Byte>) : seq<bool> 
        requires |xb| >= 1
        requires xb[|xb|-1] >= 1
        ensures 8 * (|xb| - 1) >= 0

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

    lemma {:induction m} simplifyFromByteToListFirstArg(b : Byte, m : seq<Byte>) 
        requires |m| >= 1
        requires m[|m| - 1] >= 1
        ensures fromBytesToBitList([b] + m) == 
            byteTo8Bits(b) + fromBytesToBitList(m) 
    { //  Dafny proves it.
    }

    /**
     *  Decoding of encoded l : seq<bool> returns l. 
     */
    lemma {:induction l} decodeEncodeIsIdentity(l : seq<bool>) 
        ensures fromBytesToBitList( fromBitlistToBytes (l) ) == l 
    {
        if ( |l| < 7 ) {
            //  Thanks Dafny
        } else if ( |l| == 7 ) {
            //  Thanks Dafny
        } else {
            calc == {
                fromBytesToBitList( fromBitlistToBytes (l) );
                == 
                fromBytesToBitList([list8BitsToByte(l[..8])] + fromBitlistToBytes(l[8..]));
                == { simplifyFromByteToListFirstArg(
                        list8BitsToByte(l[..8]), 
                        fromBitlistToBytes(l[8..])
                        ) ;  
                    }
                    byteTo8Bits(list8BitsToByte(l[..8])) + 
                    fromBytesToBitList(fromBitlistToBytes(l[8..]));
                == { decodeOfEncode8BitsIsIdentity(l[..8]); }
                l[0..8] + fromBytesToBitList(fromBitlistToBytes(l[8..]));
            }
        }
    }
 }