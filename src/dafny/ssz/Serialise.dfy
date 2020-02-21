
include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"

/**
 *  SSZ library.
 *
 *  Serialise, deserialise
 */
 module SSZ {

    import opened NativeTypes
    import opened Eth2Types

    function method as_uint16(s: seq<Byte>) : uint16 
        requires |s| == 2

    function method as_Bytes(k : uint16) : seq<Byte> 
        ensures |as_Bytes(k)| == 2
        ensures as_uint16(as_Bytes(k)) == k

    /* Serialise an Byte. */
    function method serialise(k : uint16) : seq<Byte> {
        as_Bytes(k)
    }

    function method deserialise(s : seq<Byte>) : uint16 
        requires |s| == 2
    {
        as_uint16(s)
    } 

    lemma serialiseIsInvolutive(k : uint16) 
        ensures deserialise(serialise(k)) == k {

        }

    lemma injectiveSerialise( n: uint16, m : uint16) 
        ensures serialise(n) == serialise(m) ==> n == m

 }