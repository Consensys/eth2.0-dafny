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

    /** The serialisable objects. */
    datatype Serialisable = 
            Uint8(n: uint8, ghost tipe: Tipe)
        |   Bool(b: bool, ghost tipe: Tipe)

    /** Some type tags.
     * 
     *  In Dafny we cannot extract the type of a given object.
     *  In the proofs, we need to specify the type when deserialise is called
     *  and also to prove some lemmas.
     *  The `Tipe` tag should match the actual type of a serialisable.
     *  This can be enforced by invoking the predicate [[wellTyped]].
     */
    datatype Tipe =
            Uint8_
        |   Bool_

    /** Whether a serialisable has its Tipe field matching its type. 
     *
     *  @param  s   A serialisable.
     *  @returns    True iff s.tipe is s.tipe_.
     */
    predicate wellTyped(s : Serialisable) {
            match s 
                case Bool(_, b) => s.tipe == Bool_
        
                case Uint8(_, t) => s.tipe == Uint8_
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
    type Bytes = String 
    type Byte = uint8
    type BLSPubkey = String
    type BLSSignature = String      //a BLS12-381 signature.

    type Slot = int
    type Gwei = int

    /* syntax Fork ::= ".Fork"
    syntax BlockHeader ::= ".BlockHeader" | BeaconBlockHeader
    syntax Eth1Data ::= ".Eth1Data"
    syntax Checkpoint ::= ".Checkpoint"
    */

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