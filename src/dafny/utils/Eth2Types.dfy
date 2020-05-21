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
    
    /** The default zeroed Bytes32.  */
    // const SEQ_EMPTY_32_BYTES := timeSeq<byte>(0,32)

    /** The type `Seq32Byte` corresponding to sequences of 32 `Bytes`s */
    type Seq32Byte = x:seq<byte> | |x| == 32 witness timeSeq(0 as byte, 32)
    // SEQ_EMPTY_32_BYTES

    datatype Uint256WithByteLength = Uint256WithByteLength(n:uint256,byteLength:nat)

    type CorrectUint256WithByteLength = u:Uint256WithByteLength |   && u.n as nat < power2(u.byteLength * 8)
                                                                    && 1 <= u.byteLength <= 32
                                                                    witness Uint256WithByteLength(0,1)

    // type Uint256WithByteLength = x:(uint256,nat) | && x.0 as nat < power2(x.1 * 8)
    //                                            && 1 <= x.1 <= 32 
    //                                            witness (0,1)

    /** Create type synonym for a chunk */
    type chunk = Seq32Byte

    /** Create type synonym for a hash 'root' */
    type hash32 = Seq32Byte

    /** The serialisable objects. */
    datatype Serialisable = 
            Uint(n: CorrectUint256WithByteLength)
        |   Bool(b: bool)
        |   Bitlist(xl: seq<bool>)
        |   Bytes32(bs: Seq32Byte)
        |   Container(fl: seq<Serialisable>)

    type Uint = s:Serialisable |    s.Uint?
                                    witness Uint(Uint256WithByteLength(0,1))
    

    // The assert is required to for Dafny to verify that the provided witness
    // respects the constraint imposed by the existential quantifier
    type Uint8 = s:Uint |   assert  Equal<uint256>(0,0);
                            && exists x:uint8 :: Equal<uint256>(s.n.n, x as uint256)
                            && s.n.byteLength == 1
                            witness Uint(Uint256WithByteLength(0,1))

    type Uint16 = s:Uint |  assert  Equal<uint256>(0,0);
                            && exists x:uint16 :: Equal<uint256>(s.n.n, x as uint256)
                            && s.n.byteLength == 2
                            witness Uint(Uint256WithByteLength(0,2))   

    type Uint32 = s:Uint |  assert  Equal<uint256>(0,0);
                            && exists x:uint32 :: Equal<uint256>(s.n.n, x as uint256)
                            && s.n.byteLength == 4
                            witness Uint(Uint256WithByteLength(0,4))
 

    type Uint64 = s:Uint |  assert  Equal<uint256>(0,0);
                            // castUin64ToUint256 is probaly only required
                            // becaue uint256 is currently defined using power2
                            && exists x:uint64 :: Equal<uint256>(s.n.n, castUin64ToUint256(x))
                            && s.n.byteLength == 8
                            witness Uint(Uint256WithByteLength(castUin64ToUint256(0),8))

    type Uint128 = s:Uint | assert  Equal<uint256>(0,0);
                            // castUi1284ToUint256 is probaly only required
                            // becaue uint256 is currently defined using power2
                            && exists x:uint128 :: Equal<uint256>(s.n.n, castUin128ToUint256(x))
                            && s.n.byteLength == 16
                            witness Uint(Uint256WithByteLength(castUin128ToUint256(0),16))   

    type Uint256 = s:Uint |  assert  Equal<uint256>(0,0);
                            && exists x:uint256 :: Equal<uint256>(s.n.n, x as uint256)
                            && s.n.byteLength == 32
                            witness Uint(Uint256WithByteLength(0,32))                                                                                                           

    // Strangely, if the prefix "make" is dropped by the following functions,
    // then inside this module Dafny is still able to correctly associate when,
    // for example, Uint8 is used as a type or as function, however outside this
    // module Dafny appears to consider Uint8 only a type and not a function.
    function method makeUint8(a:uint8): Uint8
    ensures makeUint8(a).n.n == a as uint256;
    {
        assert Equal<uint256>(a as uint256, a as uint256);
        Uint(Uint256WithByteLength(a as uint256,1))
    }

    function method makeUint16(a:uint16): Uint16
    ensures makeUint16(a).n.n == a as uint256;
    {
        assert Equal<uint256>(a as uint256, a as uint256);
        assert a as nat < power2(16);
        Uint(Uint256WithByteLength(a as uint256,2))
    }    

    function method makeUint32(a:uint32): Uint32
    ensures makeUint32(a).n.n == a as uint256;
    {
        assert Equal<uint256>(a as uint256, a as uint256);
        assert a as nat < power2(32);
        Uint(Uint256WithByteLength(a as uint256,4))
    }

    function method makeUint64(a:uint64): Uint64
    ensures makeUint64(a).n.n == castUin64ToUint256(a);
    {
        assert Equal<uint256>(castUin64ToUint256(a),castUin64ToUint256(a));
        UpperBoundForUint64(a);
        Uint(Uint256WithByteLength(a as uint256,8))
    }  

    function method makeUint128(a:uint128): Uint128
    ensures makeUint128(a).n.n == castUin128ToUint256(a);
    {
        assert Equal<uint256>(castUin128ToUint256(a),castUin128ToUint256(a));
        UpperBoundForUint128(a);
        Uint(Uint256WithByteLength(a as uint256,16))
    } 

    function method makeUint256(a:uint256): Uint256
    ensures makeUint256(a).n.n == a;
    {
        assert Equal<uint256>(a as uint256, a as uint256);
        Uint(Uint256WithByteLength(a,32))
    }  

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
            // The Tipe Uint_ requires the byteLength parameter as Uint_ of
            // different lenght are different types
            Uint_(byteLength:nat)
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
        
                case Uint(n) => Uint_(n.byteLength)

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