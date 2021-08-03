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

/**
 * Returns a random sequence of Uint64 of size between 0 and 2000-1
 */
function method getRandomListUint64(): Eth2Types.Serialisable
ensures getRandomListUint64().List?
ensures getRandomListUint64().t == Eth2Types.Uint64_
ensures 0 <= |getRandomListUint64().l| < 2000
ensures getRandomListUint64().limit >= |getRandomListUint64().l|
{
    // List length is a randomised number between 0 and 2000-1
    var numElemnts := Rand.Rand() % 2000;
    var limit := numElemnts +
                    (if numElemnts == 0 then 
                        Rand.Rand() % 100
                    else
                        Rand.Rand() % numElemnts);


    var l :=  Helpers.initSeq<Eth2Types.RawSerialisable>(
                (x:nat) => Eth2Types.Uint64(Rand.Rand()% 0x10000000000000000), 
                numElemnts as nat);

    assert (forall i | 0 <= i < |l| :: Eth2Types.wellTyped(l[i]));
    assert forall i | 0 <= i < |l| :: Eth2Types.typeOf(l[i]) == Eth2Types.Uint64_;

    Eth2Types.List(
        l,
        Eth2Types.Uint64_,
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
requires list.t == Eth2Types.Uint64_
{
    var dfyHashRoot := SSZ_Merkleise.getHashTreeRoot(list);
    assert forall i | 0 <= i < |list.l| :: Eth2Types.typeOf(list.l[i]) == Eth2Types.Uint64_;

    var ThirdPartyBitlist :=    if |list.l| >= 2000 * (100 - failPercentage) /100 then 
                                    match failureReason
                                        case Content =>
                                            if |list.l| > 0  then
                                                Eth2Types.List(
                                                    [Eth2Types.Uint64(
                                                        (list.l[0].n as nat + 1) % 0x10000000000000000
                                                    )
                                                    ] + list.l[1..]
                                                    ,
                                                    list.t,
                                                    list.limit
                                                )
                                            else
                                                Eth2Types.List(
                                                    [Eth2Types.Uint64(0)],
                                                    Eth2Types.Uint64_,
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
    assert forall i | 0 <= i < |list.l| :: list.l[i].n < 0x10000000000000000;
    assert forall i | 0 <= i < |ThirdPartyBitlist.l| :: ThirdPartyBitlist.l[i].n < 0x10000000000000000;

    var ThirdParthyHash := ThirdPartyMerkleisation.ListUint64Root(
                                Helpers.seqMap(ThirdPartyBitlist.l, (ui:Eth2Types.RawSerialisable) requires ui.Uint64? => ui.n)
                                ,
                                ThirdPartyBitlist.limit);

    dfyHashRoot == ThirdParthyHash
}

/**
 * @param numTests Number of test items to create
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
        var list := getRandomListUint64();

        [createTestItem(list,percFailure, failureReason)] +
        CompileRecTest(numTests-1,percFailure, failureReason)
}

function method createTestItem(list: Eth2Types.Serialisable, percFailure: nat, failureReason: FailureReason): DafTest.TestItem
requires list.List?
requires list.t == Eth2Types.Uint64_
{
    DafTest.TestItem(
                "Test for List of size " + 
                StringConversions.itos(|list.l|) + 
                " and limit " +
                StringConversions.itos(list.limit) + 
                ":\n"
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
                          createTestItem(Eth2Types.List([],Eth2Types.Uint64_,1),percFailure,failureReason)];

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