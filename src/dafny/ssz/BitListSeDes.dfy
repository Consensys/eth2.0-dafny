
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

    function method list8BitsTouint8(l : seq<bool>) : Byte    
        requires |l| == 8 

    function method uint8ToList8Bits( n : uint8 ) : seq<bool>
        ensures |uint8ToList8Bits(n)| == 8

    //  We assume some properties of the previous functions with l1 and l2 below.

    /** Encode(decode(n)) = Identity(n).
     *  
     *  @param  n   a number.
     *  @proof      Encoding (as a Byte) the decoded version of `n` yields `n`.
     */
    lemma {:axiom} l1(n: Byte)  
        ensures list8BitsTouint8(uint8ToList8Bits(n)) == n 

    /** Decode(encode(l)) = Identity(l).
     *  
     *  @param  l   a list of 8 bits.
     *  @proof      Decoding (as a list of bits) the encoded version of `l` yields `l`.
     *
     */    
     lemma {:axiom} l2(l : seq<bool>) 
        requires |l| == 8
        ensures uint8ToList8Bits(list8BitsTouint8(l)) == l

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
         *  4. Encode the first 8 bits into a Byte, and recursively encode the 
         *      tail i.e. the bits after the first 8 bits.
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
            [list8BitsTouint8(l[..8])] + bitListToBytes(l[8..])    
    }
 }