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
    type BLSSignature = String      //a BLS12-381 signature

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
     *
     *  @param  version         The version.
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

    /**
     *  A Validator.
     *
     *  @param  pubkey                          BLSPubkey
     *  @param  withdrawal_credentials          Commitment to pubkey for withdrawals
     *  @param  effective_balance               Balance at stake
     *  @param  slashed                         Status epochs    
     *  @param  activation_eligibility_epoch    When criteria for activation were met
     *  @param  activation_epoch
     *  @param  exit_epoch: Epoch
     *  @param  withdrawable_epoch              When validator can withdraw funds
     */
    datatype Validator = Validator(
        pubkey: BLSPubkey,
        withdrawalCredentials: Hash,
        effectiveBalance: int,
        slashed: bool,
        activationEligibilityEpoch: int,
        activationEpoch: int,
        exitEpoch: int,
        withdrawableEpoch: int
    )
    
    /**
     *  Attestation data (what is that?)
     *
     *  @param  slot
     *  @param  index               LMD GHOST vote (what is that?)
     *  @param  beacon_block_root   FFG vote (what is that?)
     *  @param  source
     *  @param  target
     */
    datatype AttestationData = AttestationData(
        slot: int,
        index: int,
        beacon_block_root: Hash,
        source: CheckPoint,
        target: CheckPoint
    )

    /**
     *  AttestationData and custody bit (what is that?)
     *  
     *  @param  data            The data.
     *  @param  custody_bit     Challengeable bit (SSZ-bool, 1 byte) for the custody 
     *                          of sharddata
     */
    datatype AttestationDataAndCustodyBit =  AttestationDataAndCustodyBit(
        data: AttestationData,
        custody_bit: bool
    )

    /**
     *  Indexed Attestation data. Should probably be inheriting from attestation data ...
     *
     *  @param  custody_bit_0_indices   Indices with custody bit equal to 0
     *  @param  custody_bit_1_indices:  Indices with custody bit equal to 1
     *  @param  data
     *  @param  signature
     */
    datatype IndexedAttestation = IndexedAttestation(
        custody_bit_0_indices: seq<ValidatorIndex>,
        custody_bit_1_indices: seq<ValidatorIndex>,
        data: AttestationData,
        signature: BLSSignature
    )

    /**
     *  Pending attestation (What is that?)
     *
     *  @param  aggregation_bits
     *  @param  data
     *  @param  inclusion_delay
     *  @param  proposer_index
     */
    datatype PendingAttestation = PendingAttestation(
        aggregation_bits: seq<bool>,
        data: AttestationData,
        inclusion_delay: int,
        proposer_index: ValidatorIndex
    )    

    /**
     *  Eth1Data
     */
}