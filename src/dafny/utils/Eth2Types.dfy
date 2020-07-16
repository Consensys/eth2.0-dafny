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

include "NativeTypes.dfy"
include "NonNativeTypes.dfy"
include "../utils/Helpers.dfy"
include "../utils/MathHelpers.dfy"
include "../ssz/Constants.dfy"

/** 
 * Define the types used in the Eth2.0 spec.
 * From types.k in the Eth2 spec.
 *
 */
module Eth2Types {

    import opened NativeTypes
    import opened NonNativeTypes
    import opened Helpers
    import opened MathHelpers
    import opened Constants

    //  The Eth2 basic types.

    /** The type `byte` corresponds to a 'uint8' */
    type byte = uint8
    /** The type `bytes` corresponds to a sequence of 'Bytes's */
    type bytes = seq<byte>

    datatype BitlistWithLength = BitlistWithLength(s:seq<bool>,limit:nat)

    type CorrectBitlist = u:BitlistWithLength | |u.s| <= u.limit witness BitlistWithLength([],0)

    /** The default zeroed Bytes32.  */
    // const SEQ_EMPTY_32_BYTES := timeSeq<byte>(0,32)

    /** The type `Seq32Byte` corresponding to sequences of 32 `Bytes`s */
    type Seq32Byte = x:seq<byte> | |x| == 32 witness timeSeq(0 as byte, 32)
    // SEQ_EMPTY_32_BYTES

    /** Create type synonym for a chunk */
    type chunk = Seq32Byte

    /** Create type synonym for a hash 'root' */
    type hash32 = Seq32Byte

    /** The serialisable objects. */
    datatype RawSerialisable = 
            Uint8(n: nat)
        |   Uint16(n: nat)
        |   Uint32(n: nat)
        |   Uint64(n: nat)
        |   Uint128(n: nat)
        |   Uint256(n: nat)
        |   Bool(b: bool)
        |   Bitlist(xl: seq<bool>, limit:nat)
        |   Bitvector(xl: seq<bool>)
        |   Bytes(bs: seq<byte>)
        |   List(l:seq<RawSerialisable>, t:Tipe, limit: nat)
        |   Vector(v:seq<RawSerialisable>)
        |   BeaconBlockHeader(
                slot: RawSerialisable,
                // proposer_index: RawSerialisable,
                parent_root: RawSerialisable,
                state_root: RawSerialisable
                // body_root: RawSerialisable
            )
        |   BeaconState(
                slot: RawSerialisable,
                latest_block_header: RawSerialisable,
                block_roots: RawSerialisable,
                state_roots: RawSerialisable
            )

    function method sequenceOfFields(s:Serialisable): seq<Serialisable>
    requires  isContainer(s)
    ensures forall i | 0 <= i < |sequenceOfFields(s)| :: sequenceOfFields(s)[i] < s
    {
        assert wellTyped(s);
        match s 
            case BeaconBlockHeader(f1,f2,f3) => 
                seqMap([f1,f2,f3],castToSerialisable)

            case BeaconState(f1,f2,f3,f4) => 
                seqMap([f1,f2,f3,f4],castToSerialisable)
    }

    predicate wellTypedContainerField(f:RawSerialisable, t:Tipe)
    ensures wellTypedContainerField(f,t) <==> wellTyped(f) && typeOf(f) == t
    decreases f
    {
        wellTyped(f) && typeOf(f) == t
    }   

    /** Well typed predicate for `RawSerialisable`s
     * @param s `RawSerialisable` value
     * @returns `true` iff `s` is a legal value for serialisation and
     *           merkleisation
     */    
    predicate wellTyped(s:RawSerialisable)
    decreases s, 0, 0
    {
        if !isContainer(s) then
            match s 
                case Bool(_) => true
        
                case Uint8(n) => n < 0x100

                case Uint16(n) => n < 0x10000

                case Uint32(n) => n < 0x100000000

                case Uint64(n) => n < 0x10000000000000000

                case Uint128(n) => n < 0x100000000000000000000000000000000

                case Uint256(n) => n < 0x10000000000000000000000000000000000000000000000000000000000000000 

                case Bitlist(xl,limit) => |xl| <= limit

                case Bitvector(xl) => |xl| > 0

                case Bytes(bs) => |bs| > 0

                case List(l, t, limit) =>   && |l| <= limit
                                            && t != Bool_
                                            && (forall i | 0 <= i < |l| :: wellTyped(l[i]))                                   
                                            && forall i | 0 <= i < |l| :: typeOf(l[i]) == t 

                case Vector(v) =>   && |v| > 0
                                    && (forall i | 0 <= i < |v| :: wellTyped(v[i])) 
                                    && (forall i,j | 0 <= i < |v| && 0 <= j < |v| :: typeOf(v[i]) == typeOf(v[j]))
                                    && (typeOf(v[0])) != Bool_
        else
            wellTypedContainer(s)
                  
    }

    predicate wellTypedContainer(s:RawSerialisable)
    requires isContainer(s)
    decreases s, 0, 0, 0
    {
        match s 
            case BeaconBlockHeader(slot,parent_root,state_root) =>
                    && wellTypedContainerField(slot,Uint64_)
                    && wellTypedContainerField(parent_root,Bytes_(32))
                    && wellTypedContainerField(state_root,Bytes_(32))

            case BeaconState(slot,latest_block_header,block_roots,state_roots) =>
                    && wellTypedContainerField(slot,Uint64_)
                    && wellTypedContainerField(latest_block_header, BeaconBlockHeader_)
                    && wellTypedContainer(latest_block_header)
                    && wellTypedContainerField(block_roots, Vector_(Bytes_(32),SLOTS_PER_HISTORICAL_ROOT as nat))
                    && wellTypedContainerField(state_roots, Vector_(Bytes_(32),SLOTS_PER_HISTORICAL_ROOT as nat))
    }

    /**
     * The type `Serialisable` corresponds to well typed `RawSerialisable`s
     */
    type Serialisable = s:RawSerialisable | wellTyped(s) witness Uint8(0)


    type BeaconBlockHeader = s:Serialisable |   && s.BeaconBlockHeader?
                                                && wellTypedContainer(s)
                                                witness BeaconBlockHeader(Uint64(0),Bytes(timeSeq(0 as byte, 32)),Bytes(timeSeq(0 as byte, 32)))

    type BeaconState = s:Serialisable |   && s.BeaconState?
                                          && wellTypedContainer(s)
                                          witness BeaconState(  Uint64(0),
                                                                BeaconBlockHeader(Uint64(0),Bytes(timeSeq(0 as byte, 32)),Bytes(timeSeq(0 as byte, 32))),
                                                                Vector(timeSeq(Bytes(timeSeq(0 as byte, 32)), SLOTS_PER_HISTORICAL_ROOT as nat)),
                                                                Vector(timeSeq(Bytes(timeSeq(0 as byte, 32)), SLOTS_PER_HISTORICAL_ROOT as nat)))
    /**
     * Helper function to cast a well typed `RawSerialisable` to a
     * `Serialisable`. Its mainly usage is for the cases where `Serialisable` is
     * used as type parameter.
     * 
     * @param s RawSerialisable value
     * @returns `s` typed as `Serialisable`
     */
    function method castToSerialisable(s:RawSerialisable):Serialisable
    requires wellTyped(s)
    {
        s
    }

    // type CorrectlyTypedSerialisable = s:Serialisable | s.List? ==> 

    /** The type `Bytes4` corresponds to a Serialisable built using the
     * `Bytes` constructor passing a sequence of 4 `byte`s to it
     */
    type Bytes4 = s:Serialisable |  s.Bytes? && |s.bs| == 4
                                    witness Bytes(timeSeq(0 as byte, 4))

    /** The type `Bytes32` corresponds to a Serialisable built using the
     * `Bytes` constructor passing a sequence of 32 `byte`s to it
     */
    type Bytes32 = s:Serialisable | s.Bytes? && |s.bs| == 32
                                    witness Bytes(timeSeq(0 as byte, 32))

    /** The type `Bytes48` corresponds to a Serialisable built using the
     * `Bytes` constructor passing a sequence of 48 `byte`s to it
     */
    type Bytes48 = s:Serialisable | s.Bytes? && |s.bs| == 48
                                    witness Bytes(timeSeq(0 as byte, 48))

    /** The type `Bytes96` corresponds to a Serialisable built using the
     * `Bytes` constructor passing a sequence of 96 `byte`s to it
     */
    type Bytes96 = s:Serialisable | s.Bytes? && |s.bs| == 96
                                    witness Bytes(timeSeq(0 as byte, 96))

    // EMPTY_BYTES32

    // const EMPTY_BYTES32 := Bytes32(SEQ_EMPTY_32_BYTES)
    
    type Root = Bytes32

    /** Some type tags.
     * 
     *  In Dafny we cannot extract the type of a given object.
     *  In the proofs, we need to specify the type when deserialise is called
     *  and also to prove some lemmas.
     */
    datatype Tipe =
            Uint8_
        |   Uint16_
        |   Uint32_
        |   Uint64_
        |   Uint128_
        |   Uint256_
        |   Bool_
        |   Bitlist_(limit:nat)
        |   Bitvector_(len:nat)
        |   Bytes_(len:nat)
        |   List_(t:Tipe, limit:nat)
        |   Vector_(t:Tipe, len:nat)
        |   BeaconBlockHeader_
        |   BeaconState_

    predicate method isContainerTipe(t:Tipe)
    {
        || t.BeaconBlockHeader_?
        || t.BeaconState_?
    }

    /**
     * Check if a `Tipe` is the representation of a basic `Serialisable` type
     *
     * @param t The `Tipe` value
     * @returns `true` iff `t` is the representation of a basic `Serialisable`
     *          type
     */
    predicate method isBasicTipe(t:Tipe)
    {
        !
        (   || t.Bitlist_?
            || t.Bitvector_?
            || t.Bytes_?
            || t.List_?
            || t.Vector_?
            || isContainerTipe(t)
        )
    }

    predicate method isContainer(s:RawSerialisable)
    {
        || s.BeaconBlockHeader?
        || s.BeaconState?
    }    

    lemma equivalenceIsContainerIsContainerTipe(s:RawSerialisable)
    requires wellTyped(s)
    ensures isContainer(s) <==> isContainerTipe(typeOf(s))
    {
        // Thanks Dafny
    }

   /**  The Tipe of a serialisable.
     *  This function allows to obtain the type of a `Serialisable`.
     *  
     *  @param  s   A serialisable.
     *  @returns    Its tipe.
     */
    function method typeOf(s : RawSerialisable) : Tipe 
    requires wellTyped(s)
    decreases s, 0
    {
            match s 
                case Bool(_) => Bool_
        
                case Uint8(_) => Uint8_

                case Uint16(_) => Uint16_

                case Uint32(_) => Uint32_

                case Uint64(_) => Uint64_

                case Uint128(_) => Uint128_

                case Uint256(_) => Uint256_

                case Bitlist(_,limit) => Bitlist_(limit)

                case Bitvector(bs) => Bitvector_(|bs|)

                case Bytes(xl) => Bytes_(|xl|)

                case List(l, t, limit) =>   List_(t, limit)

                case Vector(v) => Vector_(typeOf(v[0]),|v|)

                case BeaconBlockHeader(_,_,_) => BeaconBlockHeader_

                case BeaconState(_,_,_,_) => BeaconState_
    }


    /**
     * Bitwise exclusive-or of two `byte` value
     *
     * @param a  First value
     * @param b  Second value
     * @returns  Bitwise exclusive-or of `a` and `b`
     */
    function byteXor(a:byte, b:byte): byte
    {
        ((a as bv8)^(b as bv8)) as byte
    }      

    //  Old section

    /** Simple Serialisable types. */
    trait SSZ {
        /** An SSZ must offer an encoding into array of bytes. */
        function hash_tree_root () : HashTreeRoot 
    }

    /* A String type. */
    type String = seq<char>

    type HashTreeRoot = Option<array<byte>>
    // Basic Python (SSZ) types.
    /* Hash. (Should probably be a fix-sized bytes. */
    type Hash = Bytes32

    //  TODO: change the Bytes type
    // type SerialisedBytes = seq<byte> 
    
    type BLSPubkey = String
    type BLSSignature = String      //a BLS12-381 signature.

    type Slot = uint64
    type Gwei = int

    // Custom types

    /* Validator registry index. */
    type ValidatorIndex = Option<int>

    // List types
    // Readily available in Dafny as seq<T>

    // Containers

    /**
     *  A fork.
     *
     *  @param  version         The version. (it was forked at?)
     *  @param  currentVersion  The current version.
     *  @param  epoch           The epoch of the latest fork.
     */
    class Fork extends SSZ {
        var version: int
        var currentVersion : int
        var epoch: int

        /** Generate a hash tree root.  */
        function hash_tree_root() : HashTreeRoot {
            None
        }
    }

    /** 
     *  A Checkpoint. 
     *
     *  @param  epoch   The epoch.
     *  @param  hash    The hash.
     */
    class CheckPoint {
        var epoch: int
        var hash: Hash

        /** Generate a hash tree root.  */
        function hash_tree_root() : HashTreeRoot {
            None
        }
    }
}