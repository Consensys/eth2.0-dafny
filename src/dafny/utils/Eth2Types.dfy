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

    /** The serialisable objects. */
    datatype Serialisable = 
            Uint8(n: uint8)
        |   Bool(b: bool)
        //|   Bitlist(xl:CorrectBitlist)
        |   Bitlist(xl: seq<bool>)
        |   Bytes32(bs: Seq32Byte)
        |   Container(fl: seq<Serialisable>)

    /** The type `Bytes32` corresponding to a Serialisable built using the
     * `Bytes32` constructor 
     */
    type Bytes32 = s:Serialisable | && s.Bytes32? witness Bytes32(timeSeq(0 as byte, 32))
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
        |   Bitlist_
        |   Bytes32_
        |   Container_

   /**  The Tipe of a serialisable.
     *  This function allows to obtain the type of a `Serialisable`.
     *  
     *  @param  s   A serialisable.
     *  @returns    Its tipe.
     */
    function typeOf(s : Serialisable) : Tipe {
            match s 
                case Bool(_) => Bool_
        
                case Uint8(_) => Uint8_

                case Uint16(_) => Uint16_

                case Uint32(_) => Uint32_

                case Uint64(_) => Uint64_

                case Uint128(_) => Uint128_

                case Uint256(_) => Uint256_

                case Bitlist(_) => Bitlist_

                case Bytes32(_) => Bytes32_

                case Container(_) => Container_
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