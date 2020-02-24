
include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "IntSeDes.dfy"
include "BoolSeDes.dfy"

/**
 *  SSZ library.
 *
 *  Serialise, deserialise
 */
 module SSZ {

    import opened NativeTypes
    import opened Eth2Types
    import opened IntSeDes
    import opened BoolSeDes

    /** The serialisable objects. */
    datatype Serialisable = 
            Uint8(n: uint8)
        |   Bool(b: bool)

    function method length(s: Serialisable) : nat {
        match s
        case Uint8(x) => 1
        case Bool(b) => 1
    }

    /** Encode/decode Uint8 yields Identity. */
    lemma uint8AsBytesInvolutive(n : uint8) 
        ensures bytesToUint8(uint8ToBytes(n)) == n

 
    function method serialise(s : Serialisable) : seq<Byte> 
    {
        match s 
            case Bool(b) => boolToBytes(b)

            case Uint8(n) => uint8ToBytes(n)
    }

    function method deserialise(xs : seq<Byte>, t : Serialisable) : Serialisable 
        /* The lengths must match ... for now. */
        requires length(t) == |xs|
    {
        match t

            case Bool(_) => Bool(bytesToBool(xs))

            case Uint8(_) => Uint8(bytesToUint8(xs[0..1]))
    }


 }