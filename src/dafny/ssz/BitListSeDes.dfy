
include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"

/**
 *  list<Boolean> serialisation, desrialisation.
 *
 */
 module BitListSeDes {

    import opened NativeTypes
    import opened Eth2Types

    // Functions to convert list of bits into uint8 and back

    /** Convert a bool into a Byte.
     *
     *  @param      b   A boolean.
     *  @returns        A Byte (uint8) such that b?1:0. 
     */
    function method boolToByte(b : bool) : Byte
        ensures 0 <= boolToByte(b) <= 1
    {
        if b then 
            1 as Byte
        else 
            0 as Byte
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
        if b >= 1 then 
            true
        else 
            false
    }

    /**
     *  Convert a list of 8 bits into a number.
     *
     *  @param  l   A sequence of bits.
     *  @returns    A byte the binary encoding of which is reverse(l).
     */
    function method list8BitsToByte(l : seq<bool>) : Byte    
        requires |l| == 8 
    {
        128 * boolToByte(l[0]) +
        64 * boolToByte(l[1]) +
        32 * boolToByte(l[2]) +
        16 * boolToByte(l[3]) +
        8 * boolToByte(l[4]) +
        4 * boolToByte(l[5]) +
        2 * boolToByte(l[6]) +
        1 * boolToByte(l[7])
    }

    /**
     *  Compute a list of bits given a number.
     *
     *  @param  n   A byte, i.e. a number that can be represented with 8 bits.
     *  @returns    A sequence of bits `l` such `reverse(l)` is the binary encoding of `n`. 
     */
    function method byteToList8Bits( n : Byte ) : seq<bool>
        ensures |byteToList8Bits(n)| == 8 
    {
        [
            byteToBool((n / 128) % 2),
            byteToBool((n / 64) % 2),
            byteToBool((n / 32) % 2), 
            byteToBool((n / 16) % 2),
            byteToBool((n / 8) % 2),
            byteToBool((n / 4) % 2),
            byteToBool((n / 2) % 2),
            byteToBool((n / 1) % 2)
        ]
    }

    //  Some properties of the previous functions with lemmas l1 and l2 below.

    /** Encode(decode(n)) = Identity(n).
     *  
     *  @param  n   a number.
     *  @returns    Encoding (as a Byte) the decoded version of `n` yields `n`.
     */
    lemma l1(n: Byte)  
        ensures list8BitsToByte(byteToList8Bits(n)) == n 
    {
    }

    /** Decode(encode(l)) = Identity(l).
     *  
     *  @param  l   a list of 8 bits.
     *  @returns    Decoding (as a list of bits) the encoded version of `l` yields `l`.
     *
     */    
     lemma l2(l : seq<bool>) 
        requires |l| == 8
        ensures byteToList8Bits(list8BitsToByte(l)) == l 
    {
    }

    // function method bitList8ToByte(l : seq<bool>) : Byte 
    //     requires |l| == 8
    //     ensures 

    /**
     *  Encode a list of bits into a sequence of bytes.
     *
     *  @param  l       The list of bits to encode such that |l| modulo 8 == 0.
     *  @return         The encoding of the list of bits `l`.
     *
     */
    function method bitListToBytes(l: seq<bool>) : seq<Byte> 
        requires |l| % 8 == 0
        ensures | bitListToBytes(l) | == | l | / 8 
        decreases l
    {
        /*
         *  The algorithm to encode list of bits works as follows:
         *  1. given a list of bits l
         *  2. let l' = l + [1] (append 1 to l, this is a sentinnelle)
         *  3. append |l'| modulo 8 zeros to l'
         *      l'' = l' + [0] * (|l'| modulo 8)
         *  |l''| is a multiple of 8 and can be seen as a sequence of Bytes
         *  4. Encode the first 8 bits into a Byte (`list8BitsToByte`), 
         *      and recursively encode the tail i.e. the bits after the first 8 bits.
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
         *  @note: the actual encoding of 8 bits by reversing the order seems unimportant
         *  as long as the decoding uses the same assumption and reverse the list of bits
         *  obtained from the binary encoding of a Byte.
         */
        if ( l == [] ) then
            //  If l is empty we have completed the encoding.
            []
        else 
            //  Encode first 8 bits, and concatenate encoding of the tail.
            //  Note: l[i..j] returns a sequence of the first j elements with
            //  the first i elements dropped. When i ommitted it defaults to 0.
            [list8BitsToByte(l[..8])] + bitListToBytes(l[8..])    
    }

    /**  */
    function bytesToBitList(l : seq<Byte>) : seq<bool> 
        ensures | bytesToBitList(l) | % 8 == 0
        decreases l
    {
        if ( l == [] ) then
            []
        else 
            byteToList8Bits(l[0]) + bytesToBitList(l[1..])
    }

    //  Proof of involution

    lemma {:induction m} lemmaHelper1(b : Byte, m : seq<Byte>) 
        ensures bytesToBitList([b] + m) == 
            byteToList8Bits(b) + bytesToBitList(m) 
    { //  Dafny proves it.
    }

    lemma {:induction l} decodeEncodeIsIdentity(l : seq<bool>) 
        requires | l | % 8 == 0
        ensures bytesToBitList( bitListToBytes (l) ) == l 
        {
            if ( l == [] ) {
                //  Dafny figures it out.
            } else {
                calc == {
                    bytesToBitList( bitListToBytes (l) ) ; 
                    == 
                    bytesToBitList([list8BitsToByte(l[..8])] + bitListToBytes(l[8..]));
                    == { lemmaHelper1(list8BitsToByte(l[..8]),bitListToBytes(l[8..])) ; }
                     byteToList8Bits(list8BitsToByte(l[..8])) + 
                                bytesToBitList(bitListToBytes(l[8..]));
                    == { l2(l[..8]); }
                    l[0..8] +  bytesToBitList(bitListToBytes(l[8..]));
                }
            }
        }
 }