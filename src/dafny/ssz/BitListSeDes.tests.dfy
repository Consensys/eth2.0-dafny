include "./BitListSeDes.i.dfy"
include "../utils/DafTests.dfy"

/**
*  Tests for serialise/deserialise BitListSeDes.
*
*/
module BitListSeDesTests {
    
    import opened BitListSeDes__i
    import opened DafTest 
    
    /**
     *  Dafny compiles the Main method if it finds one.
     */
    method Main() {
        //  Define the tests.
        var r := [
            TestItem(
                //  Name of test
                "Serialise [] is []",
                //  Body of test in the form () => something that evaluates to bool
                () => bitListToBytes([]) == []
            ),
            TestItem(
                "Serialise [0,1,0,0, 1,0,0,0] is [0x12]",
                () => 
                    bitListToBytes([false, true, false, false] +
                        [true] + timeSeq(false,3)) == [0x12]
            ),
            TestItem(
                "Serialise [1] * 8 is [0xff]",
                () =>
                    bitListToBytes(timeSeq(true,8)) == [0xff]
            ),
            TestItem(
                "Serialise [0] * 5 + [1,0,0] is [0x20]",
                () =>
                    bitListToBytes(timeSeq(false,5) + 
                        [true, false, false]) == [0x20]
            ),
            TestItem(
                "Serialise [1] * 4 + [1] + [0] * 3 is [0x1f]",
                () => 
                    bitListToBytes((timeSeq(true,4) + 
                        [true, false, false, false])
                            ) == [0x1f]
            ),
            TestItem(
                "Serialise [1] * 8 + [1] + [0] * 7 is [0xff, 0x01]",
                () => bitListToBytes(timeSeq(true,8) + 
                            [true] + 
                            timeSeq(false,7) 
                            ) == [0xff, 0x01]
            ),
            TestItem(
                "Serialise [1,1,0,1,0,1,0,0] + [1] + [0] * 7 is [0x2b, 0x01]",
                () => bitListToBytes(
                    [true, true, false, true, false, true, false, false] +
                    [true] + 
                    timeSeq(false,7)
                    ) == [0x2b, 0x01]
            ),
            TestItem(
                "Serialise [1] + [0] * 15 + [1] + [0] * 7 is [0x01,0x00,0x01]",
                () => bitListToBytes([true] + 
                    timeSeq(false,15) + [true] +
                    timeSeq(false,7)
                    ) ==
                    [0x01, 0x00, 0x01]
            )
        ];

        //  run the tests.
        executeTests(r);
    }
}

/**
*  Tests for serialise BitListSeDes.
*
*/
module BitListSeDesTests2 {
    
    import opened BitListSeDes__i
    import opened DafTest 
    
    /**
     *  Dafny compiles the Main method if it finds one.
     */
    method Main() {

        //  Serialise tests.
        var r := [
            TestItem(
                //  Name of test
                "Serialise [] is []",
                //  Body of test in the form () => something that evaluates to bool
                () => bitListToBytes([]) == []
            ),
            TestItem(
                "Serialise [0,1,0,0, 1,0,0,0] is [0x12]",
                () => 
                    bitListToBytes([false, true, false, false] +
                        [true] + timeSeq(false,3)) == [0x12]
            ),
            TestItem(
                "Serialise [1] * 8 is [0xff]",
                () =>
                    bitListToBytes(timeSeq(true,8)) == [0xff]
            ),
            TestItem(
                "Serialise [0] * 5 + [1,0,0] is [0x20]",
                () =>
                    bitListToBytes(timeSeq(false,5) + 
                        [true, false, false]) == [0x20]
            ),
            TestItem(
                "Serialise [1] * 4 + [1] + [0] * 3 is [0x1f]",
                () => 
                    bitListToBytes((timeSeq(true,4) + 
                        [true, false, false, false])
                            ) == [0x1f]
            ),
            TestItem(
                "Serialise [1] * 8 + [1] + [0] * 7 is [0xff, 0x01]",
                () => bitListToBytes(timeSeq(true,8) + 
                            [true] + 
                            timeSeq(false,7) 
                            ) == [0xff, 0x01]
            ),
            TestItem(
                "Serialise [1,1,0,1,0,1,0,0] + [1] + [0] * 7 is [0x2b, 0x01]",
                () => bitListToBytes(
                    [true, true, false, true, false, true, false, false] +
                    [true] + 
                    timeSeq(false,7)
                    ) == [0x2b, 0x01]
            ),
            TestItem(
                "Serialise [1] + [0] * 15 + [1] + [0] * 7 is [0x01,0x00,0x01]",
                () => bitListToBytes([true] + 
                    timeSeq(false,15) + [true] +
                    timeSeq(false,7)
                    ) ==
                    [0x01, 0x00, 0x01]
            )
        ];

        //  run the serialise tests.
        executeTests(r);

        //  Deserialise tests
        var r2 := [
            TestItem(
                "Deserialise [1] is []",
                () => realBytesToBitList([1]) == []
            )
            
        ];

         //  run the deserialise tests.
        executeTests(r2);
    }
}
