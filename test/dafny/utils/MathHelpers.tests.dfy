/*
 * Copyright 2020 ConsenSys Software Inc.
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

include "../../../src/dafny/utils/DafTests.dfy"
include "../../../src/dafny/utils/MathHelpers.dfy"

/**
 * Some tests for checking power of 2.
 */
module MathHelpersTests {

    import opened DafTest 
    import opened MathHelpers

    /**
     *  Dafny compiles the Main method if it finds one.
     */
    method Main() {

        //  Compute next power of 2
        var rb := [
            TestItem(
                "get_next_power_of_two(0) == 1",
                () => get_next_power_of_two(0) == 1
            ),
            TestItem(
                "get_next_power_of_two(1) == 1",
                () => get_next_power_of_two(1) == 1
            ),
            TestItem(
                "get_next_power_of_two(2) == 2",
                () => get_next_power_of_two(2) == 2
            ),
            TestItem(
                "get_next_power_of_two(3) == 4",
                () => get_next_power_of_two(3) == 4
            ),
            TestItem(
                "get_next_power_of_two(14) == 16",
                () => get_next_power_of_two(14) == 16
            ),
            TestItem(
                "get_next_power_of_two(25) == 32",
                () => get_next_power_of_two(25) == 32
            ),
            TestItem(
                "get_next_power_of_two(1001) == 1024",
                () => get_next_power_of_two(1001) == 1024
            ),
            TestItem(
                "get_next_power_of_two(128) == 128",
                () => get_next_power_of_two(128) == 128
            ),
            TestItem(
                "get_next_power_of_two(7) == 8",
                () => get_next_power_of_two(7) == 8
            ),
            TestItem(
                "get_next_power_of_two(48) == 64",
                () => get_next_power_of_two(48) == 64
            )
        ];

        //  run the tests.
        var t1b := TestSuite("get_next_power_of_two", rb);
        
        executeTests(t1b);

        //  Compute prev power of 2
        var rc := [
            TestItem(
                "get_prev_power_of_two(1) == 1",
                () => get_prev_power_of_two(1) == 1
            ),
            TestItem(
                "get_prev_power_of_two(2) == 2",
                () => get_prev_power_of_two(2) == 2
            ),
            TestItem(
                "get_prev_power_of_two(3) == 2",
                () => get_prev_power_of_two(3) == 2
            ),
            TestItem(
                "get_prev_power_of_two(14) == 8",
                () => get_prev_power_of_two(14) == 8
            ),
            TestItem(
                "get_prev_power_of_two(25) == 16",
                () => get_prev_power_of_two(25) == 16
            ),
            TestItem(
                "get_prev_power_of_two(1001) == 512",
                () => get_prev_power_of_two(1001) == 512
            ),
            TestItem(
                "get_prev_power_of_two(128) == 128",
                () => get_prev_power_of_two(128) == 128
            ),
            TestItem(
                "get_prev_power_of_two(7) == 4",
                () => get_prev_power_of_two(7) == 4
            )
        ];

        //  run the tests.
        var t2 := TestSuite("get_next_power_of_two", rc);
        
        executeTests(t2);
    }

}
    /** Some desirable properties of get_prev_power_of_two.  */
    // lemma test_get_prev_power_of_two(n: nat) 
    // ensures get_prev_power_of_two(0) == 1 
    // ensures get_prev_power_of_two(1) == 1 
    // ensures get_prev_power_of_two(2) == 2 
    // ensures get_prev_power_of_two(3) == 2 
    // ensures get_prev_power_of_two(8) == 8 
    // ensures get_prev_power_of_two(15) == 8
    // ensures get_prev_power_of_two(121) == 64
    //     {
    //     }