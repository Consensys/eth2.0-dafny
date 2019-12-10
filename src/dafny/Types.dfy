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

    /**
     *  A Validator.
     *
     *  @param  pubkey                          BLSPubkey.
     *  @param  withdrawal_credentials          Commitment to pubkey for withdrawals.
     *  @param  effective_balance               Balance at stake.
     *  @param  slashed                         Status epochs.    
     *  @param  activation_eligibility_epoch    When criteria for activation were met.
     *  @param  activation_epoch
     *  @param  exit_epoch: Epoch
     *  @param  withdrawable_epoch              When validator can withdraw funds.
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
     *                          of sharddata.
     */
    datatype AttestationDataAndCustodyBit =  AttestationDataAndCustodyBit(
        data: AttestationData,
        custody_bit: bool
    )

    /**
     *  Indexed Attestation data. Should probably be inheriting from attestation data ...
     *
     *  @param  custody_bit_0_indices   Indices with custody bit equal to 0.
     *  @param  custody_bit_1_indices:  Indices with custody bit equal to 1.
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
     *  Pending attestation (What is that?).
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
     *  Eth1Data2.
     */
    datatype Eth1Data = Eth1Data(
        deposit_root: Hash,
        deposit_count: uint64,
        block_hash: Hash
    )

    /**
     * Historical Batch.
     * 
     *  @param      block_roots
     *  @paran      state_roots
     */
    datatype HistoricalBatch = HistoricalBatch(
        block_roots: array<Hash>,
        state_roots: array<Hash>
    )

    /**
     *  Deposit data.
     *
     *  @param  pubkey
     *  @param  withdrawal_credentials
     *  @param  amount
     *  @param  signature
     */
    datatype DepositData = DepositData(
        pubkey: BLSPubkey,
        withdrawal_credentials: Hash,
        amount: int,
        signature: BLSSignature
    )

    /**
     *  Beacon chain block header.
     *
     *  @param  slot
     *  @param  parent_root
     *  @param  state_root
     *  @param  body_root
     *  @param  signature
     */
    datatype BeaconBlockHeader = BeaconBlockHeader(
        slot: int,
        parent_root: Hash,
        state_root: Hash,
        body_root: Hash,
        signature: BLSSignature
    )

    /**
     *  Proposer slashing (what is that?)
     *  proposer_index
     *  header_1
     *  header_2
     *  
     */ 
    datatype ProposerSlashing = ProposerSlashing(
        proposer_index: ValidatorIndex,
        header_1: BeaconBlockHeader,
        header_2: BeaconBlockHeader
    )

    /**
     *  Attester slashing. (what is that?)
     *
     *  @param  attestation_1
     *  @param  attestation_2
     */
    datatype AttesterSlashing = AttesterSlashing(
        attestation_1: IndexedAttestation,
        attestation_2: IndexedAttestation
    )

    /**
     * Attestation.
     *
     *  @param  aggregation_bits
     *  @param  data
     *  @param  custody_bits
     *  @param  signature
     */
    datatype Attestation = Attestation(
        aggregation_bits: seq<bool>,
        data: AttestationData,
        custody_bits: seq<bool>,
        signature: BLSSignature
    )

    /**
     *  Deposit.
     *
     *  @param  proof   Merkle path to deposit data list root.
     *  @param  data
     */
    datatype Deposit = Deposit(
        proof: array<Hash>,  
        data: DepositData
    )

    /**
     *  Voluntary Exit (what is that?)
     *
     *  @param  epoch               Earliest epoch when voluntary exit can be processed
     *  @param  validator_index
     *  @paran  signature
     */
    datatype VoluntaryExit = VoluntaryExit(
        epoch: int,
        validator_index: ValidatorIndex,
        signature: BLSSignature
    )

    /**
     *  Beacon block body.
     *
     *  @param  randao_reveal
     *  @param  eth1_data           Eth1 data vote 
     *  @param  graffiti            Arbitrary data
     *  @param  proposer_slashings
     *  @param  attester_slashings
     *  @param  attestations
     *  @param  deposits
     *  @param  voluntary_exits
     */
    datatype BeaconBlockBody = BeaconBlockBody(
        randao_reveal: BLSSignature,
        eth1_data: Eth1Data,
        graffiti: uint32,                          //  In K: Bytes32
        proposer_slashings: seq<ProposerSlashing>,
        attester_slashings: seq<AttesterSlashing>,
        attestations: seq<Attestation>,
        deposits: seq<Deposit>,
        voluntary_exits: seq<VoluntaryExit>
    )

    /**
     *  Beacon block.
     *
     *  @param  slot
     *  @param  parent_root
     *  @param  state_root
     *  @param  body
     *  @param  signature
     */  
    datatype BeaconBlock = BeaconBlock(
        slot: int,
        parent_root: Hash,
        state_root: Hash,
        body: BeaconBlockBody,
        signature: BLSSignature
    )  

    /**
     *  Aggregate and proof (what is that?).
     *
     *  @param  index
     *  @param  selection_proof
     *  @param  aggregate
     */  
    datatype AggregateAndProof = AggregateAndProof(
        index: ValidatorIndex,
        selection_proof: BLSSignature,
        aggregate: Attestation
    )
}