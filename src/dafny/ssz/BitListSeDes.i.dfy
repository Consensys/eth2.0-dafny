include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"

/**
 *  list<Boolean> serialisation, desrialisation.
 *
 */
 module BitListSeDes__i {

    import opened NativeTypes
    import opened Eth2Types

    // Helpers to convert list of bits into uint8 and back

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
        b == 1
    }

    /**
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
    function method byteToList8Bits( n : Byte ) : seq<bool>
        ensures | byteToList8Bits(n) | == 8 
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
     *  Ceiling function.
     *
     *  @param  n   Numerator
     *  @param  d   Denominator
     *  @returns    The smallest integer last than float(n / d).
     */
    function ceil(n: nat, d: nat) : nat
        requires d != 0
        ensures n >= 1 ==> ceil(n , d) >= 1
        ensures ceil(n ,d) == 0 <==> n == 0
    {
        if (n % d == 0) then 
            n / d
        else 
            n / d + 1
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
   
    /**
     *  Encode a list of 8*n bits into a sequence of bytes.
     *
     *  @param  l       The list of bits to encode such that |l| modulo 8 == 0.
     *  @return         The encoding of the list of bits `l`.
     *
     */
    function method bitListToBytes(l: seq<bool>) : seq<Byte> 
        requires |l| % 8 == 0
        ensures | bitListToBytes(l) | == | l | / 8 
        ensures |l| > 0 ==> | bitListToBytes(l) | > 0 
       
        decreases l
    {
        if ( l == [] ) then
            //  If l is empty we have completed the encoding.
            []
        else 
            /*   
             *  Encode first 8 bits, and concatenate with encoding of the tail.
             *  Note: l[i..j] returns a sequence of the first j elements with
             *  the first i elements dropped. When i ommitted it defaults to 0
             *  and when j is ommitted it default to |l|.
             */
            [list8BitsToByte(l[..8])] + bitListToBytes(l[8..])    
    }
        
    /** 
     *  Convert a list of bytes into a BitList.
     *  
     *  @param  l   A list of Bytes.
     *  @returns    A list of bits that correspond to the binary encoding
     *              of each byte and has size |l| * 8.
     */
    function method bytesTo8BitList(l : seq<Byte>) : seq<bool> 
        ensures | bytesTo8BitList(l) | % 8 == 0
        ensures | bytesTo8BitList(l) | == 8 * |l|

        decreases l
    {
        if ( l == [] ) then
            []
        else 
            byteToList8Bits(l[0]) + bytesTo8BitList(l[1..])
    }

 }