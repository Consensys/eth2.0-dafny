/*
 * Copyright 2020 ConsenSys Software Inc.
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

include "../ssz/Constants.dfy"
include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "Validators.dfy"
include "Attestations.dfy"

/**
 *  Provide types used in the Beacon Chain.
 */
module BeaconChainTypes { 
    
    //  Import some constants and types
    import opened Constants
    import opened NativeTypes
    import opened Eth2Types
    import opened Helpers
    import opened Validators
    import opened Attestations
    
   /**
     *  Compute Root/Hash/Bytes32 for different types.
     *  
     *  @todo   Use the hash_tree_root from Merkle?.
     *  @note   The property of hash_tree_root below is enough for 
     *          proving some invariants. So we may use a module refinement
     *          to integrate the actual hash_tree_root from Merkle module.
     */
    function method hash_tree_root<T(==)>(t : T) : Bytes32 
        ensures hash_tree_root(t) != DEFAULT_BYTES32


    /** The historical roots type.  */
    type VectorOfHistRoots = x : seq<Root> |  |x| == SLOTS_PER_HISTORICAL_ROOT as int
        witness DEFAULT_HIST_ROOTS

    /** Empty vector of historical roots. */
    const DEFAULT_HIST_ROOTS := timeSeq<Bytes32>(DEFAULT_BYTES32, SLOTS_PER_HISTORICAL_ROOT as int)

    /**
     *  Beacon chain block header.
     *
     *  @param  slot
     *  @param  proposer_index
     *  @param  parent_root
     *  @param  state_root
     *  @param  body_root
     */
    datatype BeaconBlockHeader = BeaconBlockHeader(
        slot: Slot,
        // proposer_index: ValidatorIndex,
        parent_root: Root,
        state_root: Root
        // body_root: Root
    )

    /**
     *  Zeroed (default)  block header.
     */
    const DEFAULT_BLOCK_HEADER := BeaconBlockHeader(
        0 as Slot,
        DEFAULT_BYTES32,
        DEFAULT_BYTES32
    )

    /**
     *  Beacon block body.
     *
     *  @param  randao_reveal
     *  @param  eth1_data           Eth1 data vote 
     *  @param  graffiti            Arbitrary data
     *  @param  proposer_slashings  
     *                              The proposers that are slashed.
     *  @param  attester_slashings
     *  @param  attestations
     *  @param  deposits
     *  @param  voluntary_exits
     */
    datatype BeaconBlockBody = BeaconBlockBody(
        // randao_reveal: BLSSignature,
        // eth1_data: Eth1Data,
        // graffiti: uint32,                          //  In K: Bytes32
        // proposer_slashings: seq<ProposerSlashing>,
        // attester_slashings: seq<AttesterSlashing>,
        // attestations: seq<Attestation>,
        deposits: seq<Deposit>
        // voluntary_exits: seq<VoluntaryExit>
    )

    /**
     *  The zeroed (default) block body.
     */
    const DEFAULT_BLOCK_BODY := BeaconBlockBody([])

    /**
     *  Beacon block.
     * 
     *  BeaconBlock is the primary component of the beacon chain. Each block contains a 
     *  reference (parent_root) to the block root of its parent forming a chain of 
     *  ancestors ending with the parent-less genesis block. A BeaconBlock is composed 
     *  of an outer container with a limited set of “header” fields and a BeaconBlockBody 
     *  which contains fields specific to the action of the block on state. In optimal 
     *  operation, a single BeaconBlock is proposed during each slot by the selected 
     *  proposer from the current epoch’s active validator set.
     *
     *  Seems signed beacon block has merged into this one.
     *  Where is the message?
     *
     *  @note: Note that hash_tree_root(BeaconBlock) == hash_tree_root(BeaconBlockHeader) 
     *  and thus signatures of each are equivalent.
     *
     *  @param  slot            The slot for which this block is proposed for. Must be greater 
     *                          than the slot of the block defined by parent_root.
     *  @param  proposer_index  The index of the block proposer for the slot.
     *  @param  parent_root     The block root of the parent block, forming a block chain.
     *  @param  state_root      The hash root of the post state of running the state 
     *                          transition through this block.
     *  @param  body            A BeaconBlockBody which contains fields for each of the 
     *                          [beacon operation] objects as well as a few proposer 
     *                          input fields.
     */  
    datatype BeaconBlock = BeaconBlock( 
        slot: Slot,
        // proposer_index: ValidatorIndex,
        parent_root: Root,
        state_root: Root,
        body: BeaconBlockBody
    )  

    /**
     *  The zeroed (default) block.
     */
    const DEFAULT_BLOCK := BeaconBlock(
            0 as Slot, DEFAULT_BYTES32, DEFAULT_BYTES32, DEFAULT_BLOCK_BODY
    )

    type JustificationBitVector = x : seq<bool> | |x| == JUSTIFICATION_BITS_LENGTH as int witness DEFAULT_JUSTIFICATION_BITVECTOR

    /**
     *  Default bitvector of size 4 initialised with false.
     */
    const DEFAULT_JUSTIFICATION_BITVECTOR := [false, false, false, false]

    type ListOfAttestations = x : seq<PendingAttestation> | |x| == MAX_ATTESTATIONS * SLOTS_PER_EPOCH as int witness DEFAULT_LIST_ATTESTATIONS

    /**
     *  Default bitvector of size 4 initialised with false.
     */
    const DEFAULT_LIST_ATTESTATIONS := timeSeq(DEFAULT_PENDING_ATTESTATION, MAX_ATTESTATIONS * SLOTS_PER_EPOCH as int)

    type ListOfValidators = x : seq<Validator> | |x| == VALIDATOR_REGISTRY_LIMIT as int witness 
            DEFAULT_LIST_VALIDATORS
    /**
     *  Default bitvector of size 4 initialised with false.
     */
    const DEFAULT_LIST_VALIDATORS := timeSeq(DEFAULT_VALIDATOR,  VALIDATOR_REGISTRY_LIMIT as int)

    /** 
     *  The Beacon state type.
     *
     *  @link{https://notes.ethereum.org/@djrtwo/Bkn3zpwxB?type=view} 
     *  The beacon chain’s state (BeaconState) is the core object around 
     *  which the specification is built. The BeaconState encapsulates 
     *  all of the information pertaining to: 
     *      - who the validators are, 
     *      - in what state each of them is in, 
     *      - which chain in the block tree this state belongs to, and 
     *      - a hash-reference to the Ethereum 1 chain.
     *
     *  Beginning with the genesis state, the post state of a block is considered valid if 
     *  it passes all of the guards within the state transition function. Thus, the precondition 
     *  of a block is recursively defined as transition function on the previous block and its 
     *  state all the way back to the genesis state.
     *
     * @param   genesis_time        Tracks the Unix timestamp during which the genesis slot
     *                              occurred. 
     *                              This allows a client to calculate what the current slot 
     *                              should be according to wall-clock.
     *
     * @param   slot                Time is divided into “slots” of fixed length at which 
     *                              actions occur and state transitions happen. This field 
     *                              tracks the slot of the containing state, not necessarily 
     *                              the slot according to the local wall clock.
     *
     * @param   latest_block_header The latest block header seen in the chain defining this
     *                              state. This blockheader has During the slot transition of the
     *                              block, the header is stored without the real state root but 
     *                              instead with a stub of Root () (empty 0x00 bytes). At the start
     *                              of the next slot transition before anything has been modified
     *                              within state, the state root is calculated and added to the
     *                              latest_block_header. This is done to eliminate the circular 
     *                              dependency of the state root being embedded in the block header.
     *
     * @param   block_roots         Per-slot store of the recent block roots.The block root for a 
     *                              slot is added at the start of the next slot to avoid the 
     *                              circular dependency due to the state root being embedded in the
     *                              block. For slots that are skipped (no block in the chain for the
     *                              given slot), the most recent block root in the chain prior to 
     *                              the current slot is stored for the skipped slot. When 
     *                              validators attest to a given slot, they use this store of block
     *                              roots as an information source to cast their vote.
     *
     * @param   state_roots         Per-slot store of the recent state roots.The state root for a 
     *                              slot is stored at the start of the next slot to avoid a 
     *                              circular dependency.
     *
     * @param   eth1_deposit_index  Index of the next deposit to be processed. Deposits must be 
     *                              added to the next block and processed if 
     *                              state.eth1_data.deposit_count > state.eth1_deposit_index
     *
     * @param   validators          List of Validator records, tracking the current full registry. 
     *                              Each validator contains  relevant data such as pubkey, 
     *                              withdrawal credentials, effective balance, a slashed  boolean,
     *                              and status (pending, active, exited, etc)
     *
     * @param   previous_justified_checkpoint
     *                              The most recent justified Checkpoint as it was
     *                              during the previous epoch. 
     *                              Used to validate attestations from the previous epoch
     *
     * @param   current_justified_checkpoint
     *                              The most recent justified Checkpoint previous during 
     *                              the current epoch. epoch. Used to validate current epoch
     *                               attestations and fork choice purposes
     *
     * @param   justification_bits  4 bits used to track justification in last 4 epochs. 
     *                              Most recent epoch first bit.
     *  
     * @note                        Some fields are not integrated yet but a complete def can be
     *                              found in the archive branch.
     */
    datatype BeaconState = BeaconState(
        //  Versioning
        genesis_time: uint64,
        slot: Slot,
        //  History
        latest_block_header: BeaconBlockHeader,
        block_roots: VectorOfHistRoots,
        state_roots: VectorOfHistRoots,
        //  Eth1
        eth1_deposit_index : uint64,
        //  Registry
        validators: ListOfValidators,
        //  previous_epoch_attestations: seq<>,
        //  Attestations
        previous_epoch_attestations: ListOfAttestations,
        current_epoch_attestations: ListOfAttestations,
        //  Finality
        justification_bits: JustificationBitVector,
        previous_justified_checkpoint: CheckPoint,
        current_justified_checkpoint: CheckPoint,
        finalised_checkpoint: CheckPoint
    )

    /** Default value for BeaconState. */
    const DEFAULT_BEACON_STATE := 
        BeaconState(
            0,                  
            0 as Slot,
            DEFAULT_BLOCK_HEADER, 
            DEFAULT_HIST_ROOTS, 
            DEFAULT_HIST_ROOTS, 
            0,
            DEFAULT_LIST_VALIDATORS,
            DEFAULT_LIST_ATTESTATIONS,
            DEFAULT_LIST_ATTESTATIONS,
            DEFAULT_JUSTIFICATION_BITVECTOR,
            DEFAULT_CHECKPOINT,
            DEFAULT_CHECKPOINT,
            DEFAULT_CHECKPOINT
    )

    /**
     *  A ProposerSlashing is used to police potentially 
     *  nefarious validator block proposal activity. This 
     *  makes duplicate block proposals “expensive” to 
     *  disincentivize activity that might lead to forking 
     *  and conflicting views of the canonical chain. 
     *  Validators can be slashed if they signed two 
     *  different beacon blocks for the same slot.
     *
     *  The headers seem to correspond to different witness blocks signed 
     *  by the proposer_index which makes them slashable.
     * 
     *  @param  proposer_index  index of the validator to be slashed for double proposing
     *  @param  header_1        The signed header of the first of the two slashable beacon blocks 
     *  @param  header_2        The signed header of the second of the two slashable beacon blocks
     *  
     */ 
    datatype ProposerSlashing = ProposerSlashing(
        proposer_index: ValidatorIndex,
        header_1: BeaconBlockHeader,
        header_2: BeaconBlockHeader
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

 }