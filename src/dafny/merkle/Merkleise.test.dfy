/*
 * Copyright 2020 ConsenSys AG.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 */

include "../utils/DafTests.dfy"
include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "../ssz/Serialise.dfy"
include "../ssz/IntSeDes.dfy"
include "../ssz/BoolSeDes.dfy"
include "./Merkleise.dfy"

/**
 *  SSZ_Merkleise library.
 *
 *  size_of, chunk_count, pack, merkleise, get_hash_tree_root
 */
 module SSZ_MerkleiseTests {

    import opened NativeTypes
    import opened Eth2Types
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
