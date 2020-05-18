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
include "../../../../src/dafny/ssz/BitListSeDes.dfy"
include "../../../../src/dafny/utils/DafTests.dfy"
include "../../test_utils/StringConversions.dfy"
include "../../../../src/dafny/merkle/Merkleise.dfy"
include "../../../../src/dafny/beacon/helpers/Crypto.dfy"
include "../../../lowlevel_modules/CommandLine.dfy"
include "ThirdPartyMerkleisation.dfy"
include "../../../lowlevel_modules/Rand.dfy"

/**
 * Returns random sequence of booleans of size between 0 and 2000-1
 */
function method getRandomBoolSeq(): seq<bool>
ensures 0 <= |getRandomBoolSeq()| < 2000
{
    // Bitlist length is a randomised number between 0 and 2000-1
    var numBits := Rand.Rand() % 2000;

    Helpers.initSeq<bool>(
            (x:nat) => 
                if Rand.Rand()%2 == 0 then false else true, 
            numBits as nat)

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
predicate method verifyBoolSeq(s:seq<bool>, failPercentage: nat)
{
    var dfyBitlist := Eth2Types.Bitlist(s);
    var dfyHashRoot := SSZ_Merkleise.getHashTreeRoot(dfyBitlist);

    var ThirdPartyBitlist := if |s| >= 2000 * (100 - failPercentage) /100 then s + [true] else s;

    var bfbsn := |SSZ_Merkleise.bitfieldBytes(s)| * 256;
    var ThirdParthyHash := ThirdPartyMerkleisation.BitlistRoot(
                                ThirdPartyBitlist,
                                BitListSeDes.fromBitlistToBytes(ThirdPartyBitlist),
                                bfbsn);

    dfyHashRoot == ThirdParthyHash
}

/**
 * @param numTests Number of test items to create
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
        var boolseq := getRandomBoolSeq();

        [DafTest.TestItem(
                "Test for Bitlist of size " + 
                StringConversions.itos(|boolseq|) + 
                ":\n" + 
                StringConversions.bitlistToString(boolseq)
            ,
                () => verifyBoolSeq(boolseq,percFailure)
        )] +
        CompileRecTest(numTests-1,percFailure)
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

        var merkleTestSuite := DafTest.TestSuite("Bitlist Merkleisation",
                                    CompileRecTest(numTests,percFailure));

        DafTest.executeTests(merkleTestSuite);
    }
    else
    {
        print "First argument must be a natural number indicating the number of tests\n";
        print "The second argument must be a natural number between 0 and 100 (included) which specifies the average percentage of tests that should fail\n";
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