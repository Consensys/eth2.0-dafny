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

    /** The RawSerialisable type.
     *
     *  This datatype is an over-approximation of Serialisable for some
     *  constructors like Bitlist and below. The constraints are defined 
     *  separately in `Serialisable`. 
     *
     *  Ideally we would like to define constraints on the parameters of a constructor
     *  in the datatype but this is not possible in Dafny.
     */
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
        |   Container(fl: seq<RawSerialisable>)

    /** 
     *  Define constraints on parameters of constructors of `RawSerialisable`.
     *
     *  @param      s   `RawSerialisable` value
     *  @returns        `true` iff `s` meets some well-formedness constraints (defined on the parameters).
     */    
    predicate wellTyped(s : RawSerialisable)
        //  The predicate is recursively defined on subtypes so we have to provide a termination clause.
        decreases s, 0
    {
        match s 
            case Bool(_) => true
    
            //  The following uintk tyoesd are less than 2^k

            case Uint8(n) => n < 0x100

            case Uint16(n) => n < 0x10000

            case Uint32(n) => n < 0x100000000

            case Uint64(n) => n < 0x10000000000000000

            case Uint128(n) => n < 0x100000000000000000000000000000000

            case Uint256(n) => n < 0x10000000000000000000000000000000000000000000000000000000000000000 

            //  Lists and vectors.

            case Bitlist(xl,limit) =>
                //  A bitlist must have less than limit elements
                |xl| <= limit

            case Bitvector(xl) => 
                //  Bitvectors must have length >= 1
                |xl| > 0

            case Bytes(bs) => 
                //  Bytes have length >= 1
                |bs| > 0

            case Container(_) => 
                //  All the fileds of a container must be well-typed
                forall i | 0 <= i < |s.fl| :: wellTyped(s.fl[i])

            case List(l, t, limit) =>   
                //  Lists must have less than limit elements, cannot be of type bool (there
                // is bitlist for that) and the type of the elements is welltyped and constant.
                |l| <= limit
                && (forall i | 0 <= i < |l| :: wellTyped(l[i]))                                   
                && forall i | 0 <= i < |l| :: typeOf(l[i]) == t 

            case Vector(v) =>   
                //  Vectors must have less than limit elements, and the type of the elements is welltyped and constant.
                |v| > 0
                && (forall i | 0 <= i < |v| :: wellTyped(v[i])) 
                && (forall i,j | 0 <= i < |v| && 0 <= j < |v| :: typeOf(v[i]) == typeOf(v[j]))
    }

    /**
     *  The type `Serialisable` corresponds to well typed `RawSerialisable`s.
     *  
     *  The type inhabited and a witness is Uint8(0).
     */
    type Serialisable = s:RawSerialisable | wellTyped(s) witness Uint8(0)

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
        |   Container_
        |   List_(t:Tipe, limit:nat)
        |   Vector_(t:Tipe, len:nat)

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
            || t.Container_?
            || t.List_?
            || t.Vector_?
        )
    }

   /**  The Tipe of a serialisable.
     *  This function allows to obtain the type of a `Serialisable`.
     *  
     *  @param  s   A serialisable.
     *  @returns    Its tipe.
     */
    function method typeOf(s : RawSerialisable) : Tipe 
    requires wellTyped(s)
    decreases s
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

                case Container(_) => Container_

                case List(l, t, limit) =>   List_(t, limit)

                case Vector(v) => Vector_(typeOf(v[0]),|v|)
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

    // Custom types

    /* A String type. */
    type String = seq<char>

    /* Hash. (Should probably be a fix-sized bytes. */
    type Hash = Bytes32

    //  TODO: change the Bytes type
    // type SerialisedBytes = seq<byte> 
    
    type BLSPubkey = Bytes48
    
    type BLSSignature = String      //a BLS12-381 signature.

    type Slot = uint64
    type Gwei = uint64

    /** An epoch is unsigned int over 64 bits. */
    type Epoch = uint64

    /* Validator registry index. */
    type ValidatorIndex = uint64

    // Containers

    /** 
     *  A Checkpoint. 
     *  
     *  Checkpoints have s slot number that is a multiple of
     *  SLOTS_PER_EPOCH and so only `epoch` is needed.
     *  
     *  @link{https://benjaminion.xyz/eth2-annotated-spec/phase0/beacon-chain/#checkpoint}
     *
     *  @param  epoch   The first slot of `epoch`.
     *  @param  root    The hash of the block that corresponds the checkpoint. 
     */
    datatype CheckPoint = CheckPoint(
        epoch: Epoch,
        root: Root        
    )    

     /** 
     *  A vote ie. an AttestationData.  
     *  
     *  @link{https://benjaminion.xyz/eth2-annotated-spec/phase0/beacon-chain/#attestationdata}
     *
     *  @param  slot        The assigned slot for the validator to produce its attestation.
     *  @param  source      The source (why shoukd it be justified?) checkpoint.
     *  @param  target      The target (why shoukd it be justified) checkpoint. 
     */
    datatype AttestationData = AttestationData(
        slot: Slot,
        // index, CommitteeIndex, not used, should be the committee the valudator belongs to.
        // beacon_block_root: Root, the (best?) block for `slot` ads determined by running LMD-GHOST. 
        source: CheckPoint,
        target: CheckPoint        
    )    
}