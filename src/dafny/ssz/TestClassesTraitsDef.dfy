

include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"
// include "IntSeDes.dfy"
// include "BoolSeDes.dfy"

/**
 *  SSZ library.
 *
 *  Serialise, deserialise
 */
 module OtherSSZ {

    import opened NativeTypes
    import opened Eth2Types
    // import opened IntSeDes
    // import opened BoolSeDes

    trait Serialisable {

        function method serialise() : seq<uint8>

        method deserialise(xs: seq<uint8>) returns (s: Serialisable, ts: seq<uint8>)
                requires |xs| >= 1


    }

    class FooInt extends Serialisable {
        
        constructor( n : uint8 )

        function method serialise() : seq<uint8>
        {
             [1 as uint8]
        }

        method deserialise(xs: seq<uint8>)  returns (r : Serialisable, tl: seq<uint8>)
        requires |xs| >= 1
        {
            r := new FooInt(xs[0] as uint8);
            tl := xs[1..];
        }
    }

    // lemma l(t : Serialisable) 
    //  ensures (t.deserialise(t.serialise())) == t
// {
//         var r := t.serialise();
//         var r2, xs := t.deserialise(r);

//         match r2 
//             case FooInt(v) => assert 
//         assert r == r2;
//     }

 }