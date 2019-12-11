include "NativeTypes.dfy"

/** 
 * Define the types used in the Eth2.0 spec.
 * From types.k in the Eth2 spec.
 *
 */
module Eth2Types {

    import opened Native__NativeTypes_s

    /* A String type. */
    type String = seq<char>

   
    /* Option type */
    datatype Option<T> = Nil | Some(T)

    // Basic Python (SSZ) types.
    /* Hash. (Should probably be a fix-sized bytes. */
    type Hash = String

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
    datatype Fork = Fork(
        version: int,
        currentVersion : int,
        epoch: int
    )

    /** 
     *  A Checkpoint. 
     *
     *  @param  epoch   The epoch.
     *  @param  hash    The hash.
     */
    datatype CheckPoint = CheckPoint(
        epoch: int,
        hash: Hash
    )

 
   
   

    

    
   
}