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
 
include "../../../../src/dafny/utils/NativeTypes.dfy"
include "../../../../src/dafny/utils/Eth2Types.dfy"
include "../../../../src/dafny/utils/Helpers.dfy"
include "../../../../src/dafny/ssz/BytesAndBits.dfy"
include "../../../../src/dafny/ssz/BitListSeDes.dfy"
include "../../../../src/dafny/utils/DafTests.dfy"
include "../../test_utils/StringConversions.dfy"
include "../../../../src/dafny/merkle/Merkleise.dfy"
include "../../../../src/dafny/beacon/helpers/Crypto.dfy"
include "../../../lowlevel_modules/CommandLine.dfy"
include "ThirdPartyMerkleisation.dfy"
include "../../../lowlevel_modules/Rand.dfy"

datatype FailureReason = Limit | Content

/** Helper lemma used by `getRandomBytes32` */
lemma lemmaBytes32IsWellTypedAndOfTypeBytes32(s:Eth2Types.RawSerialisable)
requires s.Bytes?
requires |s.bs| == 32
ensures Eth2Types.wellTyped(s)
ensures Eth2Types.typeOf(s) == Eth2Types.Bytes_(32)
{
    // Thanks Dafny
}

/** Return a random Byte 
 * 
 * @param x Dummy input not used in the computations
 * @returns A random Byte value
 * 
 * @note The dummy input is required only because the verification fails if 
 *       a naked lambda is used in `getRandomListBytes32`
*/
function method {:opaque} getRandomBytes32(x:nat): Eth2Types.RawSerialisable
ensures getRandomBytes32(x).Bytes?
ensures |getRandomBytes32(x).bs| == 32
ensures  Eth2Types.wellTyped(getRandomBytes32(x))
ensures Eth2Types.typeOf(getRandomBytes32(x)) == Eth2Types.Bytes_(32)
{
    var r := Eth2Types.Bytes(Helpers.initSeq<Eth2Types.byte>( (x:nat) => (Rand.Rand() % 0x100) as Eth2Types.byte,32));
    lemmaBytes32IsWellTypedAndOfTypeBytes32(r);
    assert Eth2Types.wellTyped(r);
    assert Eth2Types.typeOf(r) == Eth2Types.Bytes_(32);
    r
}


/**
 * Returns random List of Bytes32 of size between 0 and 2000-1
 */
function method getRandomListBytes32(): Eth2Types.Serialisable
ensures getRandomListBytes32().List?
ensures getRandomListBytes32().t == Eth2Types.Bytes_(32)
ensures 0 <= |getRandomListBytes32().l| < 2000
ensures getRandomListBytes32().limit >= |getRandomListBytes32().l|
{
    // List length is a randomised number between 0 and 2000-1
    var numElemnts := Rand.Rand() % 2000;
    var limit := numElemnts +
                    (if numElemnts == 0 then 
                        Rand.Rand() % 100
                    else
                        Rand.Rand() % numElemnts);

    var l :=  Helpers.initSeq<Eth2Types.RawSerialisable>(
                getRandomBytes32,
                numElemnts as nat);

    assert limit >= |l|;
    assert forall i | 0 <= i < |l| :: Eth2Types.typeOf(l[i]) == Eth2Types.Bytes_(32);
    assert (forall i | 0 <= i < |l| :: Eth2Types.wellTyped(l[i]));
    
    Eth2Types.List(
        l,
        Eth2Types.Bytes_(32),
        limit
    )

}

/**
 * @param s List
 *
 * @returns True iff the hash tree root calculated by the third party
 * markleisation function matches the value returned by the Dafny
 * correct-by-construction merkleisation function
 */
predicate method verifyList(list: Eth2Types.Serialisable, failPercentage: nat, failureReason: FailureReason)
requires list.List?
requires list.t == Eth2Types.Bytes_(32)
{
    var dfyHashRoot := SSZ_Merkleise.getHashTreeRoot(list);
    assert forall i | 0 <= i < |list.l| :: Eth2Types.typeOf(list.l[i]) == Eth2Types.Bytes_(32);
    assert forall i | 0 <= i < |list.l| :: |list.l[i].bs| == 32;

    var ThirdPartyBitlist :=    if |list.l| >= 2000 * (100 - failPercentage) /100 then 
                                    match failureReason
                                        case Content =>
                                            if |list.l| > 0  then
                                                Eth2Types.List(
                                                    [Eth2Types.Bytes(
                                                        [((list.l[0].bs[0] as nat +1 ) % 0x100) as Eth2Types.byte]
                                                        + list.l[0].bs[1..]
                                                    )
                                                    ] + list.l[1..]
                                                    ,
                                                    list.t,
                                                    list.limit
                                                )
                                            else
                                                Eth2Types.List(
                                                    [Eth2Types.Bytes(Helpers.timeSeq<Eth2Types.byte>(0,32))],
                                                    Eth2Types.Bytes_(32),
                                                    1
                                                )
                                        case Limit =>
                                            Eth2Types.List(
                                                    list.l
                                                    ,
                                                    list.t,
                                                    list.limit * 2
                                                )

                                else
                                    list
                                ;

    
    assert forall i | 0 <= i < |list.l| :: Eth2Types.wellTyped(list.l[i]);

    var ThirdParthyHash := ThirdPartyMerkleisation.ListBytes32Root(
                                Helpers.seqMap(ThirdPartyBitlist.l, (ui:Eth2Types.RawSerialisable) requires ui.Bytes? && |ui.bs| == 32 => ui.bs)
                                ,
                                ThirdPartyBitlist.limit);

    dfyHashRoot == ThirdParthyHash
}

/**
 * @param numTests Number of test items to create
 * @param percFailure Percentage of tests that should fail
 * @param failureReason Failure reason for the tests that should fail
 * 
 * @returns A sequence of randomly generated test items
 */
function method CompileRecTest(numTests:nat, percFailure:nat, failureReason: FailureReason) :seq<DafTest.TestItem>
requires 0 <= percFailure <= 100
ensures |CompileRecTest(numTests,percFailure, failureReason)| == numTests
{
    if numTests == 0 then
        []
    else
        var list := getRandomListBytes32();

        [createTestItem(list,percFailure, failureReason)] +
        CompileRecTest(numTests-1,percFailure, failureReason)
}

/** Create a test item
 * @param list List to be tested
 * @param percFailure Percentage of tests that should fail
 * @param failureReason Failure reason for the tests that should fail
 */
function method createTestItem(list: Eth2Types.Serialisable, percFailure: nat, failureReason: FailureReason): DafTest.TestItem
requires list.List?
requires list.t == Eth2Types.Bytes_(32)
{   
    // The following assert is requires in the case that the content of the list is printed
    // assert forall i | 0 <= i < |list.l| :: Eth2Types.typeOf(list.l[i]) == Eth2Types.Bytes_(32);
    DafTest.TestItem(
                "Test for List of size " + 
                StringConversions.itos(|list.l|) + 
                " and limit " +
                StringConversions.itos(list.limit) + 
                ":\n"
                // The following line prints the list content. However, note that while it works correctly with list size
                // limited to 20, with list size limited to 2000 fails on execution, I belive due to some stack overflow issue.
            
                // StringConversions.join(
                //     StringConversions.ByteSeqToHexSeqCompressed(
                //         Helpers.flatten(Helpers.seqMap(list.l, (el:Eth2Types.RawSerialisable) requires el.Bytes? => el.bs))
                //         ),"")
            ,
                () => verifyList(list,percFailure, failureReason)
    )
}

/**
 * @param args Command line arguments
 * 
 * @returns true iff the command line arguments are well formed
 */
predicate method correctInputParameters(args: seq<string>)
{
    && |args| == 4
    && StringConversions.isNumber(args[1])
    && StringConversions.isNumber(args[2])
    && 0 <= StringConversions.atoi(args[2]) <= 100
    && args[3] in {"content", "limit"}
}

/**
 * Execution Entry Point
 */
method Main()
{
    var args := GetCommandLineParamters();

    if(correctInputParameters(args))
    {
        var numTests := StringConversions.atoi(args[1]);
        var percFailure := StringConversions.atoi(args[2]);
        var failureReason := if args[3] == "content" then Content else Limit;

        assert failureReason.Limit? <==> args[3] == "limit";

        var fixedTest := [
                            // The following test must be added once pySSZ is fixed to allow merkleisation of lists with limit 0
                            // createTestItem(Eth2Types.List([],Eth2Types.Uint64_,0),percFailure,failureReason),
                          createTestItem(Eth2Types.List([],Eth2Types.Bytes_(32),1),percFailure,failureReason)
                          ];

        var tests :=    fixedTest +
                        CompileRecTest(numTests,percFailure, failureReason);


        var merkleTestSuite := DafTest.TestSuite("List Merkleisation",tests[..numTests]);

        DafTest.executeTests(merkleTestSuite);
    }
    else
    {
        print "First argument must be a natural number indicating the number of tests.\n";
        print "The second argument must be a natural number between 0 and 100 (included) which specifies the average percentage of tests that should fail.\n";
        print "The third argument must be either the string \"content\" or the string \"limit\". "+
              "This argument indicates whether the tests expected to fail should fail because of a variation in the list content or in the list limit.\n";
    }
}

/**
 * This is just to ensure the tye "mycrypto" module is reference otherwise the
 * Go compiler throws an error
 */
method dummy_method()
{
    var dummy := Crypto.hash([]);
}