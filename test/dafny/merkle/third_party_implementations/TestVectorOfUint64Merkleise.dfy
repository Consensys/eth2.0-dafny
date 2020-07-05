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
 * Returns a random sequence of Uint64 of size between 1 and 2000
 */
function method getRandomVectorUint64(): Eth2Types.Serialisable
ensures getRandomVectorUint64().Vector?
ensures forall i |  0 <= i < |getRandomVectorUint64().v| :: Eth2Types.typeOf(getRandomVectorUint64().v[i]) == Eth2Types.Uint64_
ensures 0 < |getRandomVectorUint64().v| <= 2000
{
    // Vector length is a randomised number between 1 and 2000
    var numElemnts := (Rand.Rand() % 2000) + 1;

    var v :=  Helpers.initSeq<Eth2Types.RawSerialisable>(
                (x:nat) => Eth2Types.Uint64(Rand.Rand()% 0x10000000000000000), 
                numElemnts as nat);

    assert (forall i | 0 <= i < |v| :: Eth2Types.wellTyped(v[i]));
    assert forall i | 0 <= i < |v| :: Eth2Types.typeOf(v[i]) == Eth2Types.Uint64_;

    Eth2Types.Vector(v)
}

/**
 * @param s Vector
 *
 * @returns True iff the hash tree root calculated by the third party
 * markleisation function matches the value returned by the Dafny
 * correct-by-construction merkleisation function
 */
predicate method verifyVector(vector: Eth2Types.Serialisable, failPercentage: nat)
requires vector.Vector?
requires forall i |  0 <= i < |vector.v| :: Eth2Types.typeOf(vector.v[i]) == Eth2Types.Uint64_
{
    var dfyHashRoot := SSZ_Merkleise.getHashTreeRoot(vector);
    assert forall i | 0 <= i < |vector.v| :: Eth2Types.typeOf(vector.v[i]) == Eth2Types.Uint64_;

    var ThirdPartyVector :=     if |vector.v| >= 2000 * (100 - failPercentage) /100 then 
                                        Eth2Types.Vector(
                                            [Eth2Types.Uint64(
                                                (vector.v[0].n as nat + 1) % 0x10000000000000000
                                            )
                                            ] + vector.v[1..]
                                        )
                                            
                                else
                                    vector
                                ;

    assert forall i | 0 <= i < |vector.v| :: Eth2Types.wellTyped(vector.v[i]);
    assert forall i | 0 <= i < |vector.v| :: vector.v[i].n < 0x10000000000000000;
    assert forall i | 0 <= i < |ThirdPartyVector.v| :: ThirdPartyVector.v[i].n < 0x10000000000000000;

    var ThirdParthyHash := ThirdPartyMerkleisation.VectorUint64Root(
                                Helpers.seqMap(ThirdPartyVector.v, (ui:Eth2Types.RawSerialisable) requires ui.Uint64? => ui.n)
                                );

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
        var vector := getRandomVectorUint64();

        [createTestItem(vector,percFailure)] +
        CompileRecTest(numTests-1,percFailure)
}

function method createTestItem(vector: Eth2Types.Serialisable, percFailure: nat): DafTest.TestItem
requires vector.Vector?
requires forall i |  0 <= i < |vector.v| :: Eth2Types.typeOf(vector.v[i]) == Eth2Types.Uint64_
{
    DafTest.TestItem(
                "Test for Vector of size " + 
                StringConversions.itos(|vector.v|) + 
                ":\n"
            ,
                () => verifyVector(vector,percFailure)
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
        
        var fixedTest := [createTestItem(Eth2Types.Vector([Eth2Types.Uint64(0x0)]),percFailure),
                          createTestItem(Eth2Types.Vector([Eth2Types.Uint64(0x1)]),percFailure),
                          createTestItem(Eth2Types.Vector([Eth2Types.Uint64(0x1111111111111111)]),percFailure)];

        var tests :=    fixedTest +
                        CompileRecTest(numTests,percFailure);


        var merkleTestSuite := DafTest.TestSuite("Vector Merkleisation",tests[..numTests]);

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