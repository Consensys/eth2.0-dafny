/*
 * Copyright 2021 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
 * License for the specific language governing permissions and limitations 
 * under the License.
 */

include "../../../src/dafny/ssz/IntSeDes.dfy"
include "../../../src/dafny/utils/DafTests.dfy"
include "../../../src/dafny/utils/Helpers.dfy"
include "../../../src/dafny/utils/NativeTypes.dfy"
/**
*  Tests for serialise/deserialise BitListSeDes.
*
*/
module BitListSeDesTests {
    
    import opened NativeTypes
    import opened IntSeDes
    import opened DafTest 
    import opened Helpers
    
    /**
     *  Dafny compiles the Main method if it finds one.
     */
    method Main() {
        constAsPowersOfTwo();
        //  Serialise with Uintk
        var rb := [
            TestItem(
                "Serialise uint16 0 is [0x00, 0x00]",
                () => uintSe(0, 2) == [0x00, 0x00]
            ),
            TestItem(
                "Serialise uint16 1 is [0x01, 0x00]",
                () => uintSe(1, 2) == [0x01, 0x00]
            ),
            TestItem(
                "Serialise uint16 256 is [0x00, 0x01]",
                () => 
                    uintSe(256, 2) == [0x00, 0x01]
            ),
            TestItem(
                "Serialise uint32 65536 is [0x00, 0x00, 0x01, 0x00]",
                () => uintSe(65536, 4) == [0x00, 0x00, 0x01, 0x00]
            ),  
            TestItem(
                "Serialise uint64 1,099,511,627,776 (2^40) is [0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00]",
                () => 
                    uintSe(1_099_511_627_776, 8) == [0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00]
            ),
            TestItem(
                "Serialise uint8 0 is [0x00]",
                () => uintSe(0, 1) == [0x00]
            )
        ];

        
        // print uint64ToBytes(1_099_511_627_776 as uint64);
        //  run the tests.
        var t1b := TestSuite("Serialise uints", rb);
        
        executeTests(t1b);

        //  Deserialise tests
        var r2 := [
            TestItem(
                "Deserialise [0x01] into uint8 is 1",
                () => uintDes([0x01]) == 1
            ),
            TestItem(
                "Deserialise [0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00] into uint64 is 1_099_511_627_776",
                () => uintDes([0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00]) == 1_099_511_627_776
            )        
        ];

        //  Deserialise test suite.
        var t2 := TestSuite("Deserialise bytes into uints", r2);

         //  run the deserialise tests.
        executeTests(t2);
    }
}
