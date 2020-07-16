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

// This constant is required due to a bug in PySSZ which causes an exception to be 
// thrown when building a uint64 type with a value >= MAX_VALUE_FOR_UINT64
const MAX_VALUE_FOR_UINT64: nat := 0x100000000;

/**
 * Helper function.
 *
 * @returns A randomly generated `wellTyped` `RawSerialisable` value of `Tipe`
 * `Uint64`
 */
function method {:fuel Rand.Rand,0,0} getRandomUint64(): Eth2Types.RawSerialisable
ensures Eth2Types.wellTypedContainerField(getRandomUint64(),Eth2Types.Uint64_);
{
    var val := (Rand.Rand() as nat % MAX_VALUE_FOR_UINT64);
    assert val < 0x10000000000000000;
    Eth2Types.Uint64(val)
}

/**
 * Helper lemma.
 *
 * A RawSerialisable value constructed with the Bytes constructor using a non
 * empty sequence as parameter is `wellTyped`
 */
lemma lemmaWellTypedBytes(r:Eth2Types.RawSerialisable)
requires r.Bytes?
requires |r.bs| > 0
ensures Eth2Types.wellTyped(r)
{ }

/** 
 * Helper function.
 * 
 * @returns A randomly generated `Bytes32` value.
 */
function method {:fuel Rand.Rand,0,0} getRandomBytes32(): Eth2Types.Bytes32 
{
    var bs := Helpers.initSeq<Eth2Types.byte>((x:nat) => (Rand.Rand()% 0x100) as Eth2Types.byte,32);
    assert |bs| == 32;
    var r := Eth2Types.Bytes(bs);
    lemmaWellTypedBytes(r);
    r
}

/**
 * Helper function.
 *
 * @returns A randomly generated `wellTyped` `RawSerialisable` value of `Tipe`
 * `Vector_(Bytes_(32),SLOTS_PER_HISTORICAL_ROOT)`
 */
function method {:fuel getRandomBytes32,0,0} getRandomRootVector(): Eth2Types.RawSerialisable
ensures Eth2Types.wellTypedContainerField(getRandomRootVector(), Eth2Types.Vector_(Eth2Types.Bytes_(32),Constants.SLOTS_PER_HISTORICAL_ROOT as nat));
{
    Eth2Types.Vector(getRandomRootSeq(Constants.SLOTS_PER_HISTORICAL_ROOT as nat))
}

/**
 * Helper function for `getRandomRootVector`
 * 
 * @param n Number of elements
 * @returns A randomly generated sequence of `n` `Bytes32` values
 */
function method {:fuel getRandomBytes32,0,0} getRandomRootSeq(n:nat): seq<Eth2Types.Bytes32>
ensures |getRandomRootSeq(n)| == n
ensures forall i | 0 <= i < |getRandomRootSeq(n)| :: Eth2Types.wellTyped(getRandomRootSeq(n)[i])
{
    if n == 0 then
        []
    else
        [getRandomBytes32()] + getRandomRootSeq(n-1)
}

/**
 * Helper function for the `verifyBeaconState` function
 *
 * @param n A natural number < 0x10000000000000000
 * @returns `n` wrapped into a RawSerialisable constructed with the `Uint64`
 *          constructor
 */
function method castToUint64(n:nat): Eth2Types.RawSerialisable
requires n < 0x10000000000000000
ensures castToUint64(n).Uint64?
ensures Eth2Types.wellTypedContainerField(castToUint64(n),Eth2Types.Uint64_);
{
    var r:= Eth2Types.Uint64(n);
    assert Eth2Types.wellTyped(r);
    r
}

/**
 * Helper lemma for the function `getRandomBeaconBlockHeader`
 *
 * A RawSerialisable value constructed using a `wellTyped` Uint64 value and two
 * `Bytes32` values complies to the constraints of the `BeaconBlockHeader` type
 */
lemma lemmaWellTypedBeaconBlockHeader(slot:Eth2Types.RawSerialisable, parent_root:Eth2Types.Bytes32, state_root:Eth2Types.Bytes32)
requires    Eth2Types.wellTypedContainerField(slot,Eth2Types.Uint64_)
requires    Eth2Types.wellTypedContainerField(parent_root,Eth2Types.Bytes_(32))
requires    Eth2Types.wellTypedContainerField(state_root,Eth2Types.Bytes_(32))
ensures var bbh:= Eth2Types.BeaconBlockHeader(slot,parent_root,state_root);
            && Eth2Types.wellTyped(bbh)
            && Eth2Types.wellTypedContainerField(bbh,Eth2Types.BeaconBlockHeader_);
{ }

/**
 * Helper function.
 * 
 * @returns A randomly generated `BeaconBlockHeader` value
 */
function method getRandomBeaconBlockHeader(): Eth2Types.BeaconBlockHeader
ensures getRandomBeaconBlockHeader().BeaconBlockHeader?
ensures Eth2Types.wellTyped(getRandomBeaconBlockHeader())
ensures Eth2Types.typeOf(getRandomBeaconBlockHeader()) == Eth2Types.BeaconBlockHeader_
{
    var slot := getRandomUint64();
    
    var bs1: Eth2Types.Bytes32 := getRandomBytes32();

    var bs2: Eth2Types.Bytes32 := getRandomBytes32();

    lemmaWellTypedBeaconBlockHeader(slot,bs1,bs2);

    Eth2Types.BeaconBlockHeader(
        slot,
        bs1,
        bs2
    )
}

/**
 * Helper function.
 * 
 * @returns A randomly generated `BeaconState` value
 */
function method {:fuel getRandomBytes32,0,0} {:fuel Rand.Rand,0,0} getRandomBeaconState(): Eth2Types.BeaconState
{
    var slot := getRandomUint64();

    var bbh  :=  getRandomBeaconBlockHeader();

    var block_roots := getRandomRootVector();
  
    var state_roots := getRandomRootVector();

    Eth2Types.BeaconState(
        slot,
        bbh,
        block_roots,
        state_roots
    )
}

/**
 * @param s A `BeaconState` value
 *
 * @returns True iff the hash tree root calculated by the third party
 * markleisation function matches the value returned by the Dafny
 * correct-by-construction merkleisation function
 */
predicate method verifyBeaconState(bs: Eth2Types.BeaconState, failPercentage: nat)
requires bs.BeaconState?
requires Eth2Types.wellTypedContainer(bs)
requires 0 <= failPercentage <= 100
{
    var dfyHashRoot := SSZ_Merkleise.getHashTreeRoot(bs);

    var ThirdPartyBeaconState: Eth2Types.BeaconState :=    
                                if bs.slot.n >= MAX_VALUE_FOR_UINT64 * (100 - failPercentage) /100 then
                                    var newS := castToUint64((bs.slot.n+1) % 0x10000000000000000);                                    
                                    var newBs:=
                                    Eth2Types.BeaconState(
                                        newS,
                                        bs.latest_block_header,
                                        bs.block_roots,
                                        bs.state_roots
                                    );
                                    assert Eth2Types.wellTypedContainer(newBs);
                                    newBs
                                    
                                else
                                    bs
                                ;

    var ThirdParthyHash := ThirdPartyMerkleisation.BeaconStateRoot(ThirdPartyBeaconState);

    dfyHashRoot == ThirdParthyHash
}

/**
 * Generate test items
 * 
 * @param numTests Number of test items to create
 * @param perfFailure Percentage of tests that should fail
 * 
 * @returns A sequence of randomly generated test items
 */
function method CompileTest(numTests:nat, percFailure:nat) :seq<DafTest.TestItem>
requires 0 <= percFailure <= 100
ensures |CompileTest(numTests,percFailure)| == numTests
{
    CompileRecTest(numTests,percFailure,0)
}

/**
 * Helper function for generating test items.
 * 
 * @param numTests Number of test items to create
 * @param perfFailure Percentage of tests that should fail
 * @param count Num of tests generated so far
 * 
 * @returns A sequence of randomly generated test items
 */
function method CompileRecTest(numTests:nat, percFailure:nat, count:nat) :seq<DafTest.TestItem>
requires 0 <= percFailure <= 100
ensures |CompileRecTest(numTests,percFailure,count)| == numTests
{
    if numTests == 0 then
        []
    else
        [createTestItem(getRandomBeaconState(),percFailure,count)] +
        CompileRecTest(numTests-1,percFailure,count+1)
}

/**
 * Create a test item.
 * 
 * @param bs BeaconState value to test
 * @param perfFailure Percentage of tests that should fail
 * @param count Num of tests generated so far
 * 
 * @returns A test item
 */
function method createTestItem(bs: Eth2Types.BeaconState, percFailure: nat, count:nat): DafTest.TestItem
requires bs.BeaconState?
requires Eth2Types.wellTypedContainer(bs)
requires 0 <= percFailure <= 100
{
    DafTest.TestItem(
                "Test #"
                + StringConversions.itos(count+1)
                + "\n"
            ,
                () => verifyBeaconState(bs,percFailure)
    )
}

/**
 * Validate command line arguments
 * 
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

        var fixedTest := [];

        var tests :=    fixedTest +
                        CompileTest(numTests,percFailure);


        var merkleTestSuite := DafTest.TestSuite("Beacon State Merkleisation",tests[..numTests]);

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