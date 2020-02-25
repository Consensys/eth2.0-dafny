
include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"

/**
 *  Boolean serialisation, desrialisation.
 *
 */
 module BoolSeDes {

    import opened NativeTypes
    import opened Eth2Types

    function method boolToBytes(b: bool) : seq<Byte> 
        ensures | boolToBytes(b) | == 1 
    {
        if b then 
            [1 as Byte]
        else 
            [0 as Byte]
    }

    function method bytesToBool(xs: seq<Byte>) : bool
        requires | xs | == 1 
    {
       (xs[0] as nat) > 0
    }

 }