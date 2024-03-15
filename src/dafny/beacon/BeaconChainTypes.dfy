/*
 * Copyright 2021 ConsenSys Software Inc.
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

 //  @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /timeLimit:100 /noCheating:1


include "../ssz/Constants.dfy"
include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "validators/Validators.dfy"
include "attestations/AttestationsTypes.dfy"

/**
 *  Provide types (and their defaults) used in the Beacon Chain.
 */
module BeaconChainTypes { 
    
    //  Import some constants and types
    import opened Constants
    import opened NativeTypes
    import opened Eth2Types
    import opened Helpers
    import opened Validators
    import opened AttestationsTypes
    

    // Misc dependencies

    /**
     * Fork.
     *
     * @param        previous_version: Version
     * @param        current_version: Version
     * @param        epoch: Epoch
     */
     datatype Fork = Fork(
        previous_version: Version,
        current_version: Version,
        epoch: Epoch
     )
    
    /**
     * ForkData.
    
     * @param        current_version: Version
     * @param        genesis_validator_root: Root     
     */
    datatype ForkData = ForkData(
        current_version: Version,
        genesis_validators_root: Root
    )

    /**
     *  Eth1Data2.
     *
     *  @param      deposit_root
     *  @param      deposit_count
     *  @param      block_hash
     */
    datatype Eth1Data = Eth1Data(
        deposit_root: Hash,
        deposit_count: uint64,
        block_hash: Hash
    )

    /** The zeroed (default) Eth1 data. */
    const DEFAULT_ETH1DATA := Eth1Data(DEFAULT_BYTES32, 0, DEFAULT_BYTES32)

    /** The vector of historical roots type.  */
    type VectorOfHistRoots = x : seq<Root> |  |x| == SLOTS_PER_HISTORICAL_ROOT as int
        witness DEFAULT_HIST_ROOTS

    /** Empty vector of historical roots. */
    const DEFAULT_HIST_ROOTS := timeSeq<Bytes32>(DEFAULT_BYTES32, SLOTS_PER_HISTORICAL_ROOT as int)

    // /**
    //  * Historical Batch.
    //  * 
    //  *  @param      block_roots
    //  *  @paran      state_roots
    //  */
    // datatype HistoricalBatch = HistoricalBatch(
    //     block_roots: VectorOfHistRoots,
    //     state_roots: VectorOfHistRoots
    // )

    /**
     *  HistoricalSummary.
     *     
     *  Which will replace HistoricalBatch above.
     *
     *  @param        block_roots
     *  @param        state_roots
     */
    datatype HistoricalSummary = HistoricalSummary(
        block_roots: VectorOfHistRoots,
        state_roots: VectorOfHistRoots
    )

    /**
     *  Beacon chain block header.
     *
     *  @param  slot
     *  @param  proposer_index
     *  @param  parent_root
     *  @param  state_root
     *  @param  body_root       // Not implemented in the simplified model
     */
    datatype BeaconBlockHeader = BeaconBlockHeader(
        slot: Slot,
        proposer_index: ValidatorIndex,
        parent_root: Root,
        state_root: Root
        // body_root: Root
    )

    type VectorOfPubkeys = x: seq<BLSPubkey> | |x| == SYNC_COMMITTEE_SIZE as int
        witness *

    // const DEFAULT_VECTOR_OF_PUBKEYS := timeSeq<BLSPubkey>(DEFAULT_BYTES48, 0 as int)
    
    /**
        *  SyncCommittee.
        *
        *  @param  pubkeys
        *  @param  aggregate_pubkey
     */
    datatype SyncCommittee = SyncCommittee(
        pubkeys: VectorOfPubkeys,
        aggregate_pubkey: BLSPubkey
    )

    /** The zeroed (default) block header. */
    const DEFAULT_BLOCK_HEADER := BeaconBlockHeader(
        0 as Slot,
        0 as ValidatorIndex,
        DEFAULT_BYTES32,
        DEFAULT_BYTES32
    )


    // Beacon operations

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
     *  @param  header_1        The signed header of the first of the two slashable beacon blocks 
     *  @param  header_2        The signed header of the second of the two slashable beacon blocks
     *  
     */ 
    datatype ProposerSlashing = ProposerSlashing(
        header_1: BeaconBlockHeader,
        header_2: BeaconBlockHeader
    )


    // Beacon blocks

    /**
     *  Beacon block body.
     *
     *  @param  randao_reveal
     *  @param  eth1_data           Eth1 data vote 
     *  @param  graffiti            Arbitrary data
     *  @param  proposer_slashings  The proposers that are slashed.
     *  @param  attester_slashings
     *  @param  attestations
     *  @param  deposits
     *  @param  voluntary_exits
     *  @param  sync_aggregate
     *  @param  execution_payload
     *  @param  bls_to_execution_changes
     */
    datatype BeaconBlockBody = BeaconBlockBody(
        randao_reveal: Bytes32, // In spec: BLSSignature
        eth1_data: Eth1Data,
        graffiti: uint32,                          //  In K & spec: Bytes32
        proposer_slashings: seq<ProposerSlashing>,
        attester_slashings: seq<AttesterSlashing>,
        attestations: seq<Attestation>,
        deposits: seq<Deposit>,
        voluntary_exits: seq<VoluntaryExit>,
        sync_aggregate: seq<SyncAggregate>,
        execution_payload: seq<ExecutionPayload>,
        bls_to_execution_changes: seq<BLSToExecutionChange>
    )

    /** The zeroed (default) block body. */
    const DEFAULT_BLOCK_BODY := BeaconBlockBody(
        DEFAULT_BYTES32, DEFAULT_ETH1DATA, 0 as uint32, 
        [], [], [], [], [], [], [], []
    )

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
        proposer_index: ValidatorIndex,
        parent_root: Root,
        state_root: Root,
        body: BeaconBlockBody
    )  

    /** The zeroed (default) block. */
    const DEFAULT_BLOCK := BeaconBlock(
        0 as Slot, 0 as ValidatorIndex, DEFAULT_BYTES32, DEFAULT_BYTES32, DEFAULT_BLOCK_BODY
    )


    // Beacon state

    /** The list of historical roots type.  */
    type ListOfHistRoots = x : seq<Root> |  |x| <= HISTORICAL_ROOTS_LIMIT as int 
        witness DEFAULT_LIST_OF_HIST_ROOTS

    /** The default (empty) list of historical roots. */
    const DEFAULT_LIST_OF_HIST_ROOTS : seq<Root> := []

    /**
     *  A list of Eth1Data.  
     *  The maximum size of this list is EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH.
     */
    type ListOfEth1Data = x : seq<Eth1Data> | |x| <= EPOCHS_PER_ETH1_VOTING_PERIOD as int * SLOTS_PER_EPOCH as int 
        witness DEFAULT_LIST_ETH1DATA
            
    /** The default (empty) list of Eth1Data. */
     const DEFAULT_LIST_ETH1DATA : seq<Eth1Data> := []
    
    /**
     *  A list of validators.  
     *  The maximum size of this list is VALIDATOR_REGISTRY_LIMIT (which is 2^40).
     */
    type ListOfValidators = x : seq<Validator> | |x| <= VALIDATOR_REGISTRY_LIMIT as int 
        witness DEFAULT_LIST_VALIDATORS

    /** The default (empty) list of Validators. */
    const DEFAULT_LIST_VALIDATORS : seq<Validator> := []

    /**
     *  A list of balances.  
     *  The maximum size of this list is VALIDATOR_REGISTRY_LIMIT (which is 2^40).
     */
    type ListOfBalances = x : seq<Gwei> | |x| <= VALIDATOR_REGISTRY_LIMIT as int 
        witness DEFAULT_LIST_BALANCES
    
    /** The default (empty) list of Balances. */
    const DEFAULT_LIST_BALANCES : seq<Gwei> := []

    /** The randao mixes type.  */
    type VectorOfRandaoMix = x : seq<Bytes32> |  |x| == EPOCHS_PER_HISTORICAL_VECTOR as int 
        witness DEFAULT_RANDAO_MIX

    /** The default (empty) vector of randao mixes. */
    const DEFAULT_RANDAO_MIX := timeSeq<Bytes32>(DEFAULT_BYTES32, EPOCHS_PER_HISTORICAL_VECTOR as int)

    /** The slashings type.  */
    type VectorOfSlashings = x : seq<Gwei> |  |x| == EPOCHS_PER_SLASHINGS_VECTOR as int
        witness *

    /** Empty vector of slashings. */
    const DEFAULT_SLASHINGS := timeSeq<Gwei>(0 as Gwei, 0 as int)

    type JustificationBitVector = x : seq<bool> | |x| == JUSTIFICATION_BITS_LENGTH as int 
        witness DEFAULT_JUSTIFICATION_BITVECTOR

    /** The default bitvector of size 4 initialised with false. */
    const DEFAULT_JUSTIFICATION_BITVECTOR := [false, false, false, false]

    /** A list of inactivity scores */
    type ListOfInactivityScores = x : seq<uint64> | |x| <= VALIDATOR_REGISTRY_LIMIT as int 
        witness DEFAULT_LIST_INACTIVITY_SCORES

    const DEFAULT_LIST_INACTIVITY_SCORES := timeSeq<uint64>(0 as uint64, 0 as int)
    
    /** A list of historical summaries */
    type ListOfHistoricalSummaries = x : seq<HistoricalSummary> | |x| <= HISTORICAL_ROOTS_LIMIT as int 
        witness DEFAULT_LIST_OF_HISTORICAL_SUMMARIES

    const DEFAULT_HISTORICAL_SUMMARY := HistoricalSummary(DEFAULT_HIST_ROOTS, DEFAULT_HIST_ROOTS)

    const DEFAULT_LIST_OF_HISTORICAL_SUMMARIES : seq<HistoricalSummary> := []


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
     *                              Attestations from blocks are converted to PendingAttestations *                              and stored in state for bulk accounting at epoch boundaries. 
     *                              They are stored in two separate lists:
     *  
     * @param   previous_epoch_attestations
     *                              Attestations targeting the previous epoch of the slot.
     *                              This is an archive of current_epoch_attestations that happend
     *                              at the end of an epoch.
     *                              Last epoch's current_epoch_attestations plus any new ones 
     *                              received that target the previous epoch.
     *
     *                              List of PendingAttestations for slots from the previous epoch. *                              Note: these are attestations attesting to slots in the previous *                              epoch, not necessarily those included in blocks during the 
     *                              previous epoch.

     * @param   current_epoch_attestations
     *                              Attestations targeting the epoch of the slot 
     *                              (i.e. epoch we are in).
     *
     *                              List of PendingAttestations for slots from the current epoch. 
     *                              Copied over to previous_epoch_attestations and then emptied at 
     *                              the end of the current epoch processing
     *
     * @param   previous_justified_checkpoint
     *                              The most recent justified Checkpoint as it was
     *                              during the previous epoch. 
     *                              Used to validate attestations from the previous epoch
     *
     * @param   current_justified_checkpoint
     *                              The most recent justified Checkpoint during 
     *                              the current epoch. epoch. Used to validate current epoch
     *                              attestations and fork choice purposes
     *
     * @param   justification_bits  4 bits used to track justification in last 4 epochs before
     *                              current epoch. 
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
        historical_roots: ListOfHistRoots,
        //  Eth1
        eth1_data: Eth1Data,
        eth1_data_votes:  ListOfEth1Data, //List[Eth1Data, EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH]
        eth1_deposit_index : uint64,
        //  Registry
        validators: ListOfValidators,
        balances: ListOfBalances,
        //  Randomness
        randao_mixes: VectorOfRandaoMix,
        // slashings
        slashings: VectorOfSlashings,
        //  previous_epoch_attestations: seq<>,
        //  Attestations
        previous_epoch_attestations: ListOfAttestations,
        current_epoch_attestations: ListOfAttestations,
        //  Participation

        //  Finality
        justification_bits: JustificationBitVector,
        previous_justified_checkpoint: CheckPoint,
        current_justified_checkpoint: CheckPoint,
        finalised_checkpoint: CheckPoint,
        //  Inactivity
        inactivity_score: ListOfInactivityScores,
        //  Sync
        current_sync_committee: SyncCommittee,
        next_sync_committee: SyncCommittee,
        //  Execution
        latest_execution_payload_header: ExecutionPayloadHeader,
        //  Withdrawals
        next_withdrawal_index: WithdrawalIndex,
        next_withdrawal_validator_index: ValidatorIndex,
        //  Deep history valid from Capella onwards
        historical_summaries: ListOfHistoricalSummaries
    )
    

    type ByteList = x : seq<byte> | |x| <= MAX_EXTRA_DATA_BYTES as int 

    /** 
        *  A list of Transactions
        *  The maximum size of this list is MAX_TRANSACTIONS_PER_PAYLOAD (which is 2^16).
     */
    type ListOfTransactions = x : seq<transaction> | |x| <= MAX_TRANSACTIONS_PER_PAYLOAD as int 

    /**
        *  A list of Withdrawals
        *  The maximum size of this list is MAX_WITHDRAWALS_PER_PAYLOAD (which is 2^16).
     */
    type ListOfWithdrawals = x : seq<Withdrawal> | |x| <= MAX_WITHDRAWALS_PER_PAYLOAD as int 


    /**
     * The ExecutionPayload type.
     *
     * @link{https://eth2book.info/capella/part3/containers/execution/} 
     * The ExecutionPayload is a key component of the merge between Ethereum's
     * execution layer and consensus layer. It encapsulates all the information
     * necessary for the execution of transactions, including:
     *     - the state before transaction execution,
     *     - the transactions themselves,
     *     - the state after transaction execution, and
     *     - various elements necessary for proof-of-stake consensus.
     *
     * The ExecutionPayload is created by the execution client and provided to
     * the consensus client. It is used to propose a new block and contains all
     * the necessary data for the consensus client to validate and agree upon
     * the block contents without needing to execute transactions itself.
     *
     * @param parent_hash          Hash of the parent block, ensuring continuity in the blockchain.
     * @param fee_recipient        The address to which transaction fees are paid.
     * @param state_root           The post-transaction state root.
     * @param receipts_root        The root of the receipts trie, summarizing the effect of transactions.
     * @param logs_bloom           A bloom filter for the logs contained in the block, aiding in log retrieval.
     * @param prev_randao          The RANDAO value of the previous block, used in randomness generation.
     * @param block_number         The height of the block in the blockchain.
     * @param gas_limit            The current limit of gas expenditure per block.
     * @param gas_used             The total gas used by all transactions in this block.
     * @param timestamp            The timestamp at which the block was proposed.
     * @param extra_data           Additional data included by the proposer of the block.
     * @param base_fee_per_gas     The minimum fee per gas required for a transaction to be included in this block.
     * @param block_hash           The hash of the execution block, ensuring block uniqueness.
     * @param transactions         The list of transactions included in the block.
     * @param withdrawals          The list of withdrawals in the block, new in Capella upgrade.
     *
     * This datatype is essential in the post-merge Ethereum ecosystem, where the
     * consensus layer relies on the execution layer to provide it with succinct
     * proofs of the correct execution of transactions.
     */
    datatype ExecutionPayload = ExecutionPayload(
        // Execution block header fields
        parent_hash: hash32,
        fee_recipient: ExecutionAddress,
        state_root: Hash,
        receipts_root: Hash,
        logs_bloom: ByteVector,
        prev_randao: Hash,
        block_number: uint64,
        gas_limit: uint64,
        gas_used: uint64,
        timestamp: uint64,
        extra_data: ByteList,
        base_fee_per_gas: uint64,
        // Extra payload fields
        block_hash: hash32,
        transactions: ListOfTransactions,
        withdrawals: ListOfWithdrawals
    )


    /**
     * The ExecutionPayloadHeader type.
     *
     * @link{https://eth2book.info/capella/part3/containers/execution/}
     * The ExecutionPayloadHeader represents a condensed version of the ExecutionPayload,
     * containing all the critical header information of an execution block without the full
     * transaction and withdrawals data. This header is crucial for the consensus layer to
     * validate and agree upon block contents efficiently. It includes hashes of the transaction
     * and withdrawals data, allowing for a compact proof of the full payload.
     *
     * The ExecutionPayloadHeader is used within the consensus layer to maintain a light
     * reference to execution blocks, enabling validators to perform their duties without
     * processing the entire content of the execution layer's data, thus optimizing the
     * overall system performance.
     *
     * @param parent_hash          Hash of the parent block, establishing a link in the blockchain.
     * @param fee_recipient        The address credited with transaction fees from this block.
     * @param state_root           The root of the state trie after transaction execution.
     * @param receipts_root        The root of the trie containing receipts of all transactions.
     * @param logs_bloom           A bloom filter summarizing the event logs of the block.
     * @param prev_randao          The previous block's RANDAO value, used for entropy.
     * @param block_number         The sequential number of the block in the chain.
     * @param gas_limit            The maximum gas allowed in this block for executing transactions.
     * @param gas_used             The total gas used by transactions in this block.
     * @param timestamp            The time at which the block was proposed.
     * @param extra_data           Additional information provided by the block proposer.
     * @param base_fee_per_gas     The base fee per gas in the block, part of EIP-1559.
     * @param block_hash           The unique identifier of the block.
     *
     * Below are the main difference between ExecutionPayload and ExecutionPayloadHeader:
     *     - ExecutionPayloadHeader contains the Merkle root of the transactions and withdrawals.
     *
     * @param transactions_root    The Merkle root of the transactions trie, representing all transactions.
     * @param withdrawals_root     The Merkle root of the withdrawals trie, representing all withdrawals.
     */
    datatype ExecutionPayloadHeader = ExecutionPayloadHeader(
        // Execution block header fields
        parent_hash: hash32,
        fee_recipient: ExecutionAddress,
        state_root: Hash,
        receipts_root: Hash,
        logs_bloom: ByteVector,
        prev_randao: Hash,
        block_number: uint64,
        gas_limit: uint64,
        gas_used: uint64,
        timestamp: uint64,
        extra_data: ByteList,
        base_fee_per_gas: uint64,
        // Extra payload fields
        block_hash: hash32,
        transactions_root: Root,
        withdrawals_root: Root
    )

 }