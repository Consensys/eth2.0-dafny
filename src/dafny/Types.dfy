/** 
 * Define the types used in the Eth2.0 spec.
 * From types.k in the Eth2 spec.
 *
 */
module Eth2Types {
    /* A String type. */
    type String = seq<char>

   
    /* Option type */
    datatype Option<T> = Nil | Some(T)

    // Basic Python (SSZ) types.
    /* Hash. (Should probably be a fix-sized bytes. */
    type Hash = String

    type BLSPubkey = String

    /* syntax Fork ::= ".Fork"
    syntax BlockHeader ::= ".BlockHeader" | BeaconBlockHeader
    syntax Eth1Data ::= ".Eth1Data"
    syntax Checkpoint ::= ".Checkpoint"
    */

    // Custom types
    /* Validator registry index. */
    type ValidatorIndex = Option<int>

    // List types
    // Readily available in Dafny as List<T>

    // Containers

    /**
     *  A fork.
     *  @param  version         The version.
     *  @param  currentVersion  The current version.
     *  @param  epoch           The epoch of the latest fork.
     */
    class Fork {
        var version: int
        var currentVersion : int
        var epoch: int
    }

    /** 
    *   A Checkpoint. 
     *  @param  epoch   The epoch.
     *  @param  hash    The hash.
     */
    class CheckPoint {
        var epoch: int
        var hash: Hash
    }

    /**
     *  A Validator.
     *  @param  pubkey                          BLSPubkey
     *  @param  withdrawal_credentials          Commitment to pubkey for withdrawals
     *  @param  effective_balance               Balance at stake
     *  @param  slashed                         Status epochs    
     *  @param  activation_eligibility_epoch    When criteria for activation were met
     *  @param  activation_epoch
     *  @param  exit_epoch: Epoch
     *  @param  withdrawable_epoch              When validator can withdraw funds
     */
     class Validator {
        var pubkey: BLSPubkey
        var withdrawalCredentials: Hash
        var effectiveBalance: int
        var slashed: bool
        var activationEligibilityEpoch: int
        var activationEpoch: int
        var exitEpoch: int
        var withdrawableEpoch: int
     }
}