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
 
include "../../../../src/dafny/utils/NativeTypes.dfy"
include "../../../../src/dafny/utils/Eth2Types.dfy"
include "../../../../src/dafny/utils/Helpers.dfy"
include "../../../../src/dafny/ssz/BytesAndBits.dfy"
include "../../../../src/dafny/ssz/BitVectorSeDes.dfy"
include "../../../../src/dafny/utils/DafTests.dfy"
include "../../test_utils/StringConversions.dfy"
include "../../../../src/dafny/merkle/Merkleise.dfy"
include "../../../../src/dafny/beacon/helpers/Crypto.dfy"
include "../../../lowlevel_modules/CommandLine.dfy"
include "ThirdPartyMerkleisation.dfy"
include "../../../lowlevel_modules/Rand.dfy"

/**
 * Returns random sequence of booleans of size between 1 and 2000, inclusive
 */
function method getRandomBoolSeq(): Eth2Types.Serialisable
ensures getRandomBoolSeq().Bitvector?
ensures 1 <= |getRandomBoolSeq().xl| <= 2000
{
    // Bitvector length is a randomised number between 1 and 2000
    var numBits := (Rand.Rand() % 2000) + 1;
    
    Eth2Types.Bitvector(
        Helpers.initSeq<bool>(
                (x:nat) => 
                    if Rand.Rand()%2 == 0 then false else true,
                numBits as nat)
    )

}

/**
 * @param bitvector         Bitvector Eth2 Type
 * @param failPercentage    Value between 0 and 100
 *
 * @returns True iff the hash tree root calculated by the PrysmaticLab
 * `BitvectorRoot` function matches the value returned by the Dafny
 * correct-by-construction `getHashTreeRoot` function
 *
 * @note For demo purposes, for any bitvector of size higher than 1000, a `true`
 * bit is appended to it before passing it to the PrysmaticLab `BitvectorRoot`
 * function which will cause the verification to fail.
 */
predicate method verifyBoolSeq(bitvector: Eth2Types.Serialisable, failPercentage: nat)
requires bitvector.Bitvector?
{
    var dfyHashRoot := SSZ_Merkleise.getHashTreeRoot(bitvector);

    var ThirdPartyBitvector :=  if |bitvector.xl| >= 2000 * (100 - failPercentage) /100 then 
                    
                                    if |bitvector.xl| > 0  then
                                        Eth2Types.Bitvector(
                                            [!bitvector.xl[0]] + bitvector.xl[1..]
                                        )
                                    else
                                        Eth2Types.Bitvector(
                                            [true]
                                        )
                                else
                                    bitvector
                                ;

    var ThirdParthyHash := ThirdPartyMerkleisation.BitvectorRoot(
                                ThirdPartyBitvector.xl,
                                BitVectorSeDes.fromBitvectorToBytes(ThirdPartyBitvector.xl));

    dfyHashRoot == ThirdParthyHash
}

/**
 * @param numTests          Number of test items to create
 * @param failPercentage    Value between 0 and 100
 * 
 * @returns A sequence of randomly generated test items
 */
function method CompileRecTest(numTests:nat, percFailure:nat) :seq<DafTest.TestItem>
requires 0 <= percFailure <= 100
ensures |CompileRecTest(numTests,percFailure)| == numTests
{
    if numTests == 0 then
        []
    else
        var bitlist := getRandomBoolSeq();

        [createTestItem(bitlist,percFailure)] +
        CompileRecTest(numTests-1,percFailure)
}

function method createTestItem(bitvector: Eth2Types.Serialisable, percFailure: nat): DafTest.TestItem
requires bitvector.Bitvector?
{
    DafTest.TestItem(
                "Test for Bitvector of size " + 
                StringConversions.itos(|bitvector.xl|) + 
                ":\n" + 
                StringConversions.bitvectorToString(bitvector.xl)
            ,
                () => verifyBoolSeq(bitvector,percFailure)
    )
}

/**
 * @param args Command line arguments
 * 
 * @returns true iff the command line arguments are well formed
 */
predicate method correctInputParameters(args: seq<string>)
{
    && |args| == 3
    && StringConversions.isNumber(args[1])
    && StringConversions.isNumber(args[2])
    && 0 <= StringConversions.atoi(args[2]) <= 100
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
        
        var fixedTest := [createTestItem(Eth2Types.Bitvector([false]),percFailure)];

        var tests :=    fixedTest +
                        CompileRecTest(numTests,percFailure);


        var merkleTestSuite := DafTest.TestSuite("Bitvector Merkleisation",tests[..numTests]);

        DafTest.executeTests(merkleTestSuite);
    }
    else
    {
        print "First argument must be a natural number indicating the number of tests.\n";
        print "The second argument must be a natural number between 0 and 100 (included) which specifies the average percentage of tests that should fail.\n";
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