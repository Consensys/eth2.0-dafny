include "../utils/DafTests.dfy"
include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "../Constants.dfy"
include "Serialise.dfy"
include "IntSeDes.dfy"
include "BoolSeDes.dfy"
include "Merkleise.dfy"

/**
 *  SSZ_Merkleise library.
 *
 *  size_of, chunk_count, pack, merkleise, get_hash_tree_root
 */
 module SSZ_MerkleiseTests {

    import opened NativeTypes
    import opened Eth2Types
    import opened Eth2Constants
    import opened IntSeDes
    import opened BoolSeDes
    import opened SSZ
    import opened Helpers
    import opened DafTest 
    import opened SSZ_Merkleise

    method Main() {

        //  Chunkcount tests
        var rb := [
            TestItem(
                "Count chunks for serialised uint8(5) is 1",
                () => chunkCount(Uint8(5, Uint8_)) == 1 
            ),
            TestItem(
                "Count chunks for serialised bool true is 1",
                () => chunkCount(Bool(true, Bool_)) == 1 
            )
        ];

        // //  run the tests.
        var t1 := TestSuite("Count chunks tests", rb);
        
        executeTests(t1);

        //  rightPadZeros tests
         var r2 := [
            TestItem(
                "Right pad with zeros 127 has size 32",
                () => |rightPadZeros(serialise(Uint8(127, Uint8_)))| == 32 
            )
            // TestItem(
            //     "Count chunks for serialised bool true is 1",
            //     () => chunkCount(Bool(true, Bool_)) == 1 
            // )
        ];

        // //  run the tests.
        var t2 := TestSuite("Right pad with zeros tests", r2);
        
        executeTests(t2);

    }
}
