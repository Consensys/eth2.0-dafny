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
 * Returns random sequence of booleans of size between 0 and 2000-1
 */
function method getRandomBoolSeq(): Eth2Types.Serialisable
ensures getRandomBoolSeq().Bitlist?
ensures 0 <= |getRandomBoolSeq().xl| < 2000
ensures getRandomBoolSeq().limit >= |getRandomBoolSeq().xl|
{
    // Bitlist length is a randomised number between 0 and 2000-1
    var numBits := Rand.Rand() % 2000;
    var limit := Rand.Rand() % 100 + numBits;

    Eth2Types.Bitlist(
        Helpers.initSeq<bool>(
                (x:nat) => 
                    if Rand.Rand()%2 == 0 then false else true, 
                numBits as nat),
        limit
    )

}

/**
 * @param s Bitlist
 *
 * @returns True iff the hash tree root calculated by the PrysmaticLab
 * `BitlistRoot` function matches the value returned by the Dafny
 * correct-by-construction `getHashTreeRoot` function
 *
 * @note For demo purposes, for any bitlist of size higher than 1000, a `true`
 * bit is appended to it before passing it to the PrysmaticLab `BitlistRoot`
 * function which will cause the verification to fail.
 */
predicate method verifyBoolSeq(bitlist: Eth2Types.Serialisable, failPercentage: nat, failureReason: FailureReason)
requires bitlist.Bitlist?
{
    var dfyHashRoot := SSZ_Merkleise.getHashTreeRoot(bitlist);

    var ThirdPartyBitlist :=    if |bitlist.xl| >= 2000 * (100 - failPercentage) /100 then 
                                    match failureReason
                                        case Content =>
                                            if |bitlist.xl| > 0  then
                                                Eth2Types.Bitlist(
                                                    [!bitlist.xl[0]] + bitlist.xl[1..]
                                                    ,
                                                    bitlist.limit
                                                )
                                            else
                                                Eth2Types.Bitlist(
                                                    [true]
                                                    ,
                                                    1
                                                )
                                        case Limit =>
                                            Eth2Types.Bitlist(
                                                    bitlist.xl
                                                    ,
                                                    bitlist.limit * 2
                                                )

                                else
                                    bitlist
                                ;

    var ThirdParthyHash := ThirdPartyMerkleisation.BitlistRoot(
                                ThirdPartyBitlist.xl,
                                BitListSeDes.fromBitlistToBytes(ThirdPartyBitlist.xl),
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
        var bitlist := getRandomBoolSeq();

        [createTestItem(bitlist,percFailure, failureReason)] +
        CompileRecTest(numTests-1,percFailure, failureReason)
}

function method createTestItem(bitlist: Eth2Types.Serialisable, percFailure: nat, failureReason: FailureReason): DafTest.TestItem
requires bitlist.Bitlist?
{
    DafTest.TestItem(
                "Test for Bitlist of size " + 
                StringConversions.itos(|bitlist.xl|) + 
                " and limit " +
                StringConversions.itos(bitlist.limit) + 
                ":\n" + 
                StringConversions.bitlistToString(bitlist.xl)
            ,
                () => verifyBoolSeq(bitlist,percFailure, failureReason)
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

        var fixedTest := [createTestItem(Eth2Types.Bitlist([],0),percFailure,failureReason),
                          createTestItem(Eth2Types.Bitlist([],1),percFailure,failureReason)];

        var tests :=    fixedTest +
                        CompileRecTest(numTests,percFailure, failureReason);


        var merkleTestSuite := DafTest.TestSuite("Bitlist Merkleisation",tests[..numTests]);

        DafTest.executeTests(merkleTestSuite);
    }
    else
    {
        print "First argument must be a natural number indicating the number of tests.\n";
        print "The second argument must be a natural number between 0 and 100 (included) which specifies the average percentage of tests that should fail.\n";
        print "The third argument must be either the string \"content\" or the string \"limit\". "+
              "This argument indicates whether the tests expected to fail should fail because of a variation in the bitlist content or in the bitlist limit.\n";
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