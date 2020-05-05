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
/** 
 * Define the types used in the Eth2.0 spec.
 * From types.k in the Eth2 spec.
 *
 */
module Eth2Types {

    import opened NativeTypes
    import opened Helpers

    //  The Eth2 basic types.

    /** The type `Seq32uint8` corresponding to sequences of 32 `uint8`s */
    type Seq32uint8 = x:seq<uint8> | |x| == 32
                                    witness timeSeq(0,32)

    /** The serialisable objects. */
    datatype Serialisable = 
            Uint8(n: uint8)
        |   Bool(b: bool)
        |   Bitlist(xl: seq<bool>)
        |   Bytes32(bs: Seq32uint8)

    /** The type `Bytes32` corresponding to a Serialisable built using the
     * `Bytes32` constructor 
     */
    type Bytes32 = s:Serialisable | && s.Bytes32?
                                    witness Bytes32(timeSeq(0,32))

    /** Some type tags.
     * 
     *  In Dafny we cannot extract the type of a given object.
     *  In the proofs, we need to specify the type when deserialise is called
     *  and also to prove some lemmas.
     */
    datatype Tipe =
            Uint8_
        |   Bool_
        |   Bitlist_
        |   Bytes32_

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

                case Bitlist(_) => Bitlist_

                case Bytes32(_) => Bytes32_
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
    type Hash = String

    //  TODO: change the Bytes type
    // type SerialisedBytes = seq<Byte> 
    type Byte = uint8
    type BLSPubkey = String
    type BLSSignature = String      //a BLS12-381 signature.

    type Slot = int
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