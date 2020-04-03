/*
 * Copyright 2020 ConsenSys AG.
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

include "./BitListSeDes.dfy"
include "../utils/DafTests.dfy"
include "../utils/Helpers.dfy"

/**
*  Tests for serialise/deserialise BitListSeDes.
*
*/
module BitListSeDesTests {
    
    import opened BitListSeDes
    import opened DafTest 
    import opened Helpers
    
    /**
     *  Dafny compiles the Main method if it finds one.
     */
    method Main() {

        //  Serialise with fromBitlistToBytes
        var rb := [
            TestItem(
                "Serialise [] is [1]",
                () => fromBitlistToBytes([]) == [0x01]
            ),
            TestItem(
                "Serialise [0,1,0,0] is [0x12]",
                () => 
                    fromBitlistToBytes([false, true, false, false]) == [0x12]
            ),
            TestItem(
                "Serialise [1] * 7 is [0xff]",
                () =>
                    fromBitlistToBytes(timeSeq(true,7)) == [0xff]
            ),
            TestItem(
                "Serialise [0] * 5 is [0x20]",
                () =>
                    fromBitlistToBytes(timeSeq(false,5)) == [0x20]
            ),
            TestItem(
                "Serialise [1] * 4  is [0x1f]",
                () => 
                    fromBitlistToBytes(timeSeq(true,4)) == [0x1f]
            ),
            TestItem(
                "Serialise [1] * 8  is [0xff, 0x01]",
                () => fromBitlistToBytes(timeSeq(true,8)) == [0xff, 0x01]
            ),
            TestItem(
                "Serialise [1,1,0,1,0,1,0,0] is [0x2b, 0x01]",
                () => fromBitlistToBytes(
                    [true, true, false, true, false, true, false, false]) == [0x2b, 0x01]
            ),
            TestItem(
                "Serialise [1] + [0] * 15 is [0x01,0x00,0x01]",
                () => fromBitlistToBytes([true] + timeSeq(false,15)) ==
                    [0x01, 0x00, 0x01]
            )
        ];

        //  run the tests.
        var t1b := TestSuite("Serialise BitLists [add sentinelle and padding]", rb);
        
        executeTests(t1b);

        //  Deserialise tests
        var r2 := [
            TestItem(
                "Deserialise [0x01] is []",
                () => fromBytesToBitList([1]) == []
            ),
            TestItem(
                "Deserialise [0x03] is [true]",
                () => fromBytesToBitList([3]) == [true]
            ),
            TestItem(
                "Deserialise [0x05] is [true, false]",
                () => fromBytesToBitList([0x05]) == [true, false]
            ),
            TestItem(
                "Deserialise [0xff,0x01] is [true] * 8",
                () => fromBytesToBitList([0xff,0x01]) == timeSeq(true,8)
            ),
            TestItem(
                "Deserialise [0x01,0x00,0x01] is [true] +  [false] * 15",
                () => fromBytesToBitList([0x01,0x00,0x01]) == [true] + timeSeq(false,15)
            )
            
        ];

        //  Deserialise test suite.
        var t2 := TestSuite("Deserialise bytes into BitList", r2);

         //  run the deserialise tests.
        executeTests(t2);
    }
}
