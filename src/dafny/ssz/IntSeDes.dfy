
include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"

/**
 *  Integers serialisation, desrialisation.
 *
 */
 module IntSeDes {

    import opened NativeTypes
    import opened Eth2Types

    //  Uintk serialisation and deserielisation.

    /** Uint8. */
    function method uint8ToBytes(n: uint8) : seq<Byte> 
        ensures |uint8ToBytes(n)| == 1
    {
        [n as Byte]
    }
 

    function method bytesToUint8(xs: seq<Byte>) : uint8
        requires |xs| == 1
    {
        (xs[0] as uint8)
        
    }


    /** Encode/decode Uint8 yields Identity. */
    lemma uint8AsBytesInvolutive(n : uint8) 
        ensures bytesToUint8(uint8ToBytes(n)) == n
    {   //  Thanks Dafny
    }

    /** Uint16. */
    // function method bytesToUint16(xs: seq<Byte>) : uint16 
    //     requires |xs| == 2

    // function method uint16ToBytes(n : uint16) : seq<Byte> 
    //     ensures |uint16ToBytes(n)| == 2
    //     ensures bytesToUint16(uint16ToBytes(n)) == n

   
 }