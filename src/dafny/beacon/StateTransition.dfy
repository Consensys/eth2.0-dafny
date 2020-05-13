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

include "BeaconChain.dfy"
include "../ssz/Constants.dfy"
include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "../ssz/Constants.dfy"
include "../utils/Helpers.dfy"
// include "Attestations.dfy"
include "Validators.dfy"

/**
 * State transition function for the Beacon Chain.
 */
module StateTransition {
    
    //  Import some constants and types
    import opened NativeTypes
    import opened Eth2Types
    import opened Constants
    // import opened Attestations
    import opened BeaconChain
    import opened Validators
    import opened Helpers

    /** The default zeroed Bytes32.  */
    const SEQ_EMPTY_32_BYTES := timeSeq<Byte>(0,32)
    
    const EMPTY_BYTES32 := Bytes32(SEQ_EMPTY_32_BYTES)

    const EMPTY_HIST_ROOTS := timeSeq<Bytes32>(EMPTY_BYTES32, SLOTS_PER_HISTORICAL_ROOT + 1)

    type VectorOfHistRoots = x : seq<Bytes32> | |x| == SLOTS_PER_HISTORICAL_ROOT + 1
        witness EMPTY_HIST_ROOTS

    function method hash_tree_root(s: BeaconState) : Bytes32 
    function method hash_tree_root_block(s: BeaconBlock) : Bytes32 
    function method hash_tree_root_block_header(s: BeaconBlockHeader) : Bytes32 

    /** From config.k.
     * @link{https://notes.ethereum.org/@djrtwo/Bkn3zpwxB?type=view} 
     * The beacon chain’s state (BeaconState) is the core object around 
     * which the specification is built. The BeaconState encapsulates 
     * all of the information pertaining to: 
     *  - who the validators are, 
     *  - in what state each of them is in, 
     *  - which chain in the block tree this state belongs to, and 
     *  - a hash-reference to the Ethereum 1 chain.

     * Beginning with the genesis state, the post state of a block is 
     * considered valid if it passes all of the guards within the state 
     * transition function. Thus, the precondition of a block is 
     * recursively defined as being a valid postcondition of running 
     * the state transition function on the previous block and its state 
     * all the way back to the genesis state.
     *
     * @param   genesis_time                    The Unix timestamp of when the genesis slot 
     *                                          occurred. This allows a client to calculate 
     *                                          what the current slot should be according to 
     *                                          wall clock time
     * @param   slot                            Time is divided into “slots” of fixed length 
     *                                          at which actions occur and state transitions 
     *                                          happen. This field tracks the slot of the 
     *                                          containing state, not necessarily the slot 
     *                                          according to the local wall clock
     * @param   fork                            A mechanism for handling forking (upgrading) 
     *                                          the beacon chain. The main purpose here is to
     *                                          handle versioning of signatures and handle 
     *                                          objects of different signatures across fork 
     *                                          boundaries
     * @param   latest_block_header             The latest block header seen in the chain 
     *                                          defining this state. During the slot transition 
     *                                          of the block, the header is stored without the 
     *                                          real state root but instead with a stub of Root
     *                                          () (empty 0x00 bytes). At the start of the next 
     *                                          slot transition before anything has been 
     *                                          modified within state, the state root is 
     *                                          calculated and added to the 
     *                                          latest_block_header. This is done to eliminate 
     *                                          the circular dependency of the state root 
     *                                          being embedded in the block header
     * @param   block_roots                     Per-slot store of the recent block roots. 
     *                                          The block root for a slot is added at the start 
     *                                          of the next slot to avoid the circular 
     *                                          dependency due to the state root being embedded 
     *                                          in the block. For slots that are skipped (no 
     *                                          block in the chain for the given slot), the 
     *                                          most recent block root in the chain prior to 
     *                                          the current slot is stored for the skipped 
     *                                          slot. When validators attest to a given slot, 
     *                                          they use this store of block roots as an 
     *                                          information source to cast their vote.
     * @param   state_roots                     Per-slot store of the recent state roots. 
     *                                          The state root for a slot is stored at the 
     *                                          start of the next slot to avoid a circular 
     *                                          dependency
     * @param   historical_roots                A double batch merkle accumulator of the latest
     *                                          block and state roots defined by 
     *                                          HistoricalBatch to make historic merkle 
     *                                          proofs against. Note that although this field 
     *                                          grows unbounded, it grows at less than ___ MB 
     *                                          per ___ years
     * @param   eth1_data                       The most recent Eth1Data that validators have 
     *                                          come to consensus upon and stored in state. 
     *                                          Validator deposits from eth1 can be processed 
     *                                          up through the latest deposit contained within 
     *                                          the eth1_data root
     * @param   eth1_data_votes                 Running list of votes on new Eth1Data to be 
     *                                          stored in state. If any Eth1Data achieves > 50% 
     *                                          proposer votes in a voting period, this 
     *                                          majority data is stored in state and new 
     *                                          deposits can be processed
     * @param   eth1_deposit_index              Index of the next deposit to be processed. 
     *                                          Deposits must be added to the next block and 
     *                                          processed if state.eth1_data.deposit_count > 
     *                                          state.eth1_deposit_index
     * @param   validators                      List of Validator records, tracking the current
     *                                          full registry. Each validator contains 
     *                                          relevant data such as pubkey, withdrawal 
     *                                          credentials, effective balance, a slashed 
     *                                          boolean, and status (pending, active, exited, 
     *                                          etc)
     * @param   balances                        List mapping 1:1 with the validator_registry. 
     *                                          The granular/frequently changing balances are 
     *                                          pulled out of the validators list to reduce the 
     *                                          amount of re-hashing (in a cache optimized SSZ 
     *                                          implementation) that needs to be performed at 
     *                                          each epoch transition
     * @param   randao_mixes                    The randao mix from each epoch for the past 
     *                                          EPOCHS_PER_HISTORICAL_VECTOR epochs. At the 
     *                                          start of every epoch, the randao_mix from the 
     *                                          previous epoch is copied over as the base of 
     *                                          the current epoch. At each block, the hash of 
     *                                          the block.randao_reveal is xor’d into the 
     *                                          running mix of the current epoch
     * @param   slashings                       per-epoch store of the total slashed GWEI 
     *                                          during that epoch. The sum of this list at any 
     *                                          time gives the “recent slashed balance” and is 
     *                                          used to calculate the proportion of balance 
     *                                          that should be slashed for slashable validators
     * @param   previous_epoch_attestations     Attestations from blocks are converted to 
     *                                          PendingAttestations and stored in state for 
     *                                          bulk accounting at epoch boundaries. We store 
     *                                          two separate lists.
     *                                          List of PendingAttestations for slots from the 
     *                                          previous epoch. note: these are attestations 
     *                                          attesting to slots in the previous epoch, not
     *                                          necessarily those included in blocks during 
     *                                          the previous epoch.
     * @param   current_epoch_attestations      List of PendingAttestations for slots from the 
     *                                          current epoch. Copied over to 
     *                                          previous_epoch_attestations and then emptied at
     *                                          the end of the current epoch processing
     * @param   justification_bits              4 bits used to track justification during the 
     *                                          last 4 epochs to aid in finality calculations
     * @param   previous_justified_checkpoint   The most recent justified Checkpoint as it 
     *                                          was during the previous epoch. Used to validate 
     *                                          attestations from the previous epoch
     * @param   current_justified_checkpoint    The most recent justified Checkpoint during the 
     *                                          current epoch. Used to validate current epoch 
     *                                          attestations and for fork choice purposes
     * @param   finalized_checkpoint            The most recent finalized Checkpoint, prior to
     *                                           which blocks are never reverted.
     */
    datatype BeaconState = BeaconState(
        // genesis_time: uint64,
        slot: Slot,
        // fork: Fork,
        latest_block_header: BeaconBlockHeader
        // block_roots: array<Hash>, 
        // state_roots: array<Hash>,
        // block_roots: VectorOfHistRoots
        // state_roots: VectorOfHistRoots
        // historical_roots: seq<Hash>,
        // eth1_data: Eth1Data,
        // eth1_data_votes: seq<Eth1Data>,
        // eth1_deposit_index: uint64,
        // validators: seq<Validator>,
        // balances: seq<Gwei>
        // randao_mixes: array<Hash>,
        // slashings: array<Gwei>, 
        // previous_epoch_attestations: seq<PendingAttestation>,
        // current_epoch_attestations: seq<PendingAttestation>,
        // justification_bits: array<bool>,  
        // previous_justified_checkpoint: CheckPoint,
        // current_justified_checkPoint: CheckPoint,
        // finalized_checkPoint: CheckPoint
    )

    method state_transition(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState )
        requires s.slot <= b.slot
        requires b.parent_root == s.latest_block_header.parent_root
        // requires s.state_roots : VectorOfHistRoots
        // requires |s.state_roots| == SLOTS_PER_HISTORICAL_ROOT 
        // ensures false
    {
        // assert(|s.state_roots| == SLOTS_PER_HISTORICAL_ROOT );
        //  Process slots
        var s1 := process_slots(s, b.slot);

        assert(b.parent_root == s1.latest_block_header.parent_root);
        //  Process block
        s' := process_block(s1, b);
        
        //  Validate state block
    }

    /**
     * 
     */
   method process_slots(s: BeaconState, slot: Slot) returns (s' : BeaconState)
        requires s.slot <= slot
        // requires |s.state_roots| == SLOTS_PER_HISTORICAL_ROOT 
        ensures  s'.slot == slot 
        ensures s.latest_block_header.parent_root == s'.latest_block_header.parent_root

        // ensures  |s'.state_roots| == SLOTS_PER_HISTORICAL_ROOT
        // ensures  |s'.block_roots| == SLOTS_PER_HISTORICAL_ROOT
        decreases slot - s.slot
    {
        s' := s;
        while (s'.slot < slot)  
            invariant s'.slot <= slot
            invariant s.latest_block_header.parent_root == s'.latest_block_header.parent_root
            decreases slot - s'.slot 
        {
            s':= process_slot(s');
            s':= s'.(slot := s'.slot + 1) ;
        }
    }

    method process_slot(s: BeaconState) returns (s' : BeaconState)
        // requires |s.state_roots| == SLOTS_PER_HISTORICAL_ROOT 
        ensures s'.slot == s.slot
        ensures s.latest_block_header.parent_root == s'.latest_block_header.parent_root
        // ensures |s'.state_roots| == SLOTS_PER_HISTORICAL_ROOT
        // ensures |s'.block_roots| == SLOTS_PER_HISTORICAL_ROOT
        // ensures b.parent_root == hash_tree_root_block_header(s.latest_block_header)

    {
        s' := s;
        var previous_state_root := hash_tree_root(s);
        // s' := s'.( 
        //         state_roots := 
        //             s'.state_roots[s.slot as nat % SLOTS_PER_HISTORICAL_ROOT as nat := previous_state_root][..SLOTS_PER_HISTORICAL_ROOT] + [EMPTY_BYTES32]
        //         );  
        
        if ( s'.latest_block_header.state_root == EMPTY_BYTES32) {
            s' := s'.(latest_block_header :=
                s'.latest_block_header.(state_root := previous_state_root));
        }

        //  functional version 
        // s.(
        //     slot := s.slot + 1,
        //     state_roots := 
        //         s.state_roots[s.slot % SLOTS_PER_HISTORICAL_ROOT := previous_state_root],
        //     block_roots := 
        //         s.block_roots[s.slot % SLOTS_PER_HISTORICAL_ROOT := 
        //         if (s.latest_block_header.state_root] == EMPTY_BYTES32) previous_state_root
        //         else 
        // )
    }

    /*
    def process_slot(state: BeaconState) -> None:
    # Cache state root
    previous_state_root = hash_tree_root(state)
    state.state_roots[state.slot % SLOTS_PER_HISTORICAL_ROOT] = previous_state_root
    # Cache latest block header state root
    if state.latest_block_header.state_root == Bytes32():
        state.latest_block_header.state_root = previous_state_root
    # Cache block root
    previous_block_root = hash_tree_root(state.latest_block_header)
    state.block_roots[state.slot % SLOTS_PER_HISTORICAL_ROOT] = previous_block_root
    */

    /*
    def process_slots(state: BeaconState, slot: Slot) -> None:
    assert state.slot <= slot
    while state.slot < slot:
        process_slot(state)
        # Process epoch on the start slot of the next epoch
        if (state.slot + 1) % SLOTS_PER_EPOCH == 0:
            process_epoch(state)
        state.slot += Slot(1)
    */

    /**
     * 
     */
    method process_block(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState) 
        requires b.slot == s.slot
        requires b.parent_root == hash_tree_root_block_header(s.latest_block_header)
    {
        s' := process_block_header(s, b);
    }

    method process_block_header(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState) 
        requires b.slot == s.slot
        requires b.parent_root == hash_tree_root_block_header(s.latest_block_header)
    {
        s':= s.(
            latest_block_header := BeaconBlockHeader(
                b.slot,
                b.parent_root,
                EMPTY_BYTES32,
                hash_tree_root_block(b)
            )
        );
    }


    // def process_block(state: BeaconState, block: BeaconBlock) -> None:
    // process_block_header(state, block)

    /*
    def process_block_header(state: BeaconState, block: BeaconBlock) -> None:
    # Verify that the slots match
    assert block.slot == state.slot
    # Verify that proposer index is the correct index
    assert block.proposer_index == get_beacon_proposer_index(state)
    # Verify that the parent matches
    assert block.parent_root == hash_tree_root(state.latest_block_header)
    # Cache current block as the new latest block
    state.latest_block_header = BeaconBlockHeader(
        slot=block.slot,
        proposer_index=block.proposer_index,
        parent_root=block.parent_root,
        state_root=Bytes32(),  # Overwritten in the next process_slot call
        body_root=hash_tree_root(block.body),
    )

    # Verify proposer is not slashed
    proposer = state.validators[block.proposer_index]
    assert not proposer.slashed
    */

}