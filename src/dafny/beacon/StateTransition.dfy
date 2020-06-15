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
include "Validators.dfy"

/**
 * State transition function for the Beacon Chain.
 */
module StateTransition {
    
    //  Import some constants and types
    import opened NativeTypes
    import opened Eth2Types
    import opened Constants
    import opened BeaconChain
    import opened Helpers

    /** The default zeroed Bytes32.  */
    const SEQ_EMPTY_32_BYTES := timeSeq<Byte>(0,32)
    
    const EMPTY_BYTES32 := Bytes32(SEQ_EMPTY_32_BYTES)

    /** The historical roots type.  */
    const EMPTY_HIST_ROOTS := timeSeq<Bytes32>(EMPTY_BYTES32, SLOTS_PER_HISTORICAL_ROOT as int)

    type VectorOfHistRoots = x : seq<Bytes32> |  |x| == SLOTS_PER_HISTORICAL_ROOT as int
        witness EMPTY_HIST_ROOTS

    /**
     *  Compute Root/Hash/Bytes32 for different types.
     *  
     *  @todo   Use the hash_tree_root from Merkle.
     */
    function method hash_tree_root<T(==)>(t : T) : Bytes32 
        ensures hash_tree_root(t) != EMPTY_BYTES32

    /** Collision free hasj function. */
    lemma {:axiom} foo<T(==)>(t1: T, t2: T) 
        ensures t1 == t2 <==> hash_tree_root(t1) == hash_tree_root(t2)

   
    /** 
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
     * @param   slot                            Time is divided into “slots” of fixed length 
     *                                          at which actions occur and state transitions 
     *                                          happen. This field tracks the slot of the 
     *                                          containing state, not necessarily the slot 
     *                                          according to the local wall clock
     * @param   latest_block_header             The latest block header seen in the chain 
     *                                          defining this state. This blockheader has
     *                                          During the slot transition 
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
     */
    datatype BeaconState = BeaconState(
        slot: Slot,
        latest_block_header: BeaconBlockHeader
        // block_roots: VectorOfHistRoots,
        // state_roots: VectorOfHistRoots
    )
    
    /**
     *  Compute the state obtained after adding a block.
     */
    method stateTransition(s: BeaconState, b: BeaconBlockHeader) returns (s' : BeaconState)
        //  make sure the last state was one right after addition of new block
        // requires s.latest_block_header.state_root == EMPTY_BYTES32
        //  a new block must be proposed for a slot that is later than s.slot
        requires s.slot < b.slot
        requires b.parent_root == hash_tree_root(forwardStateToSlot(resolveStateRoot(s), b.slot).latest_block_header) //    Req1

        /** The store is not modified. */
        // ensures store == old(store)

        /** The set of already ccepted blocks is not modified. */
        // ensures acceptedBlocks == old(acceptedBlocks)

        /** The next state latest_block_header is same as b except for state_root that is 0. */
        ensures s'.latest_block_header == b.(state_root := EMPTY_BYTES32)

        ensures s'.slot == b.slot

        // modifies this
    {
        //  finalise slots before b.slot
        var s1 := processSlots(s, b.slot);

        //  Process block
        s' := processBlock(s1, b);  

        //  Validate state block
    }  

/**
    *  Advance current state to a given slot.
    *
    *  This mainly consists in advancing the slot number to
    *  a target future `slot` number and updating/recording the history of intermediate
    *  states (and block headers). 
    *  Under normal circumstances, where a block is received at each slot,
    *  this involves only one iteration of the loop.
    *  Otherwise, the first iteration of the loop `finalises` the block header
    *  of the previous slot before recortding it, 
    *  and subsequent rounds advance the slot number and record the history of states
    *  and blocks for each slot.
    *
    *  @param  s       A state
    *  @param  slot    The slot to advance to. This is usually the slot of newly
    *                  proposed block.
    *  @returns        The state obtained after advancing the history to slot.
    *      
    *   @note          The specs have the the first processSlot integrated
    *                  in the while loop. However, because s.slot < slot,
    *                  the while bdoy must be executed at least one time.
    *                  To simplify the proof, we have taken this first iteration
    *                  outside of the loop. It does not change the semantics
    *                  but enables us to use the state obtained after the first
    *                  iteration the loop and prove it is the same as 
    *                  resolveStateRoot(s); 
    *
    */
    method processSlots(s: BeaconState, slot: Slot) returns (s' : BeaconState)
        requires s.slot < slot  //  update in 0.12.0 (was <= before)

        ensures s' == forwardStateToSlot( resolveStateRoot(s), slot)
        // ensures store == old(store)
        ensures s.latest_block_header.parent_root == s'.latest_block_header.parent_root  
        
        /** The store is not modified. */
        // ensures store == old(store)

        //  Termination ranking function
        decreases slot - s.slot
    {
        //  Start from the current state and update it with processSlot.
        //  First iteration of the loop in process_slots (Eth2)
        s' := processSlot(s);
        s':= s'.(slot := s'.slot + 1) ;
        //  The following asserts are not needed for the proof but provided for readability. 
        assert(s' == resolveStateRoot(s));  
        //  s'.block header state_root should now be resolved
        assert(s'.latest_block_header.state_root != EMPTY_BYTES32);

        //  Now fast forward to slot
        //  Next iterations of process_slot (Eth2)
        while (s'.slot < slot)  
            invariant s'.slot <= slot
            invariant s'.latest_block_header.state_root != EMPTY_BYTES32
            invariant s' == forwardStateToSlot(resolveStateRoot(s), s'.slot) // Inv1
            decreases slot - s'.slot 
        {
            s':= processSlot(s');

            //  s'.slot is now processed: history updated and block header resolved
            //  The state's slot is processed and we can advance to the next slot.
            s':= s'.(slot := s'.slot + 1) ;
        }
    }

    /** 
     *  Cache data for a slot.
     *
     *  This function also finalises the block header of the last block
     *  so that it records the hash of the state `s`. 
     *
     *  @param  s   A state.
     *  @returns    A new state where `s` has been added/cached to the history and
     *              the block header tracks the hash of the most recent received
     *              block.
     *
     *  @note       This function method could be a method (as per the Eth2 specs).
     *              However, this requires to expose the properties of the computation
     *              as methods are not inlined. 
     *  @note       Matches eth2.0 specs, need to uncomment update of state/block_roots.
     *
     *  @todo       Make this a method to have a def closer to Eth2 implementation.  
     */
    method processSlot(s: BeaconState) returns (s' : BeaconState)
        requires s.slot as nat + 1 < 0x10000000000000000 as nat

        ensures  s.latest_block_header.state_root == EMPTY_BYTES32 ==>
            s' == resolveStateRoot(s).(slot := s.slot)
        ensures  s.latest_block_header.state_root != EMPTY_BYTES32 ==>
            s' == nextSlot(s).(slot := s.slot)
        ensures s.latest_block_header.parent_root == s'.latest_block_header.parent_root

        /** The store is not modified. */
        // ensures store == old(store)
    {
        s' := s;

        // Cache state root
        //  Record the hash of the previous state in the history.
        var previous_state_root := hash_tree_root(s); 

        // s' := s'.(state_roots := s'.state_roots[(s'.slot % SLOTS_PER_HISTORICAL_ROOT) as int := previous_state_root]);

        //  Cache latest block header state root
        if (s'.latest_block_header.state_root == EMPTY_BYTES32) {
            s' := s'.(latest_block_header := s'.latest_block_header.(state_root := previous_state_root));
        }

        //  Cache block root
        var previous_block_root := hash_tree_root(s'.latest_block_header);

        // s' := s'.(block_roots := s'.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := previous_block_root]);
    }

    /**
     *  Verify that a block is valid.
     *
     *  @note   Matches eth2.0 specs, need to implement randao, eth1, operations. 
     */
    method processBlock(s: BeaconState, b: BeaconBlockHeader) returns (s' : BeaconState) 
        requires b.slot == s.slot
        requires b.parent_root == hash_tree_root(s.latest_block_header)

        ensures s'.latest_block_header.parent_root == b.parent_root
        ensures s'.latest_block_header == b.(state_root := EMPTY_BYTES32)
        ensures s'.slot == s.slot

        /** The store is not modified. */
        // ensures store == old(store)
    {
        //  Start by creating a block header from the ther actual block.
        s' := processBlockHeader(s, b); 
        
        //  process_randao(s, b.body)
        //  process_eth1_data(s, b.body)
        //  process_operations(s, b.body)
    }

    /**
     *  Check whether a block is valid and prepare and initialise new state
     *  with a corresponding block header. 
     *
     *  @note   Matches eth2.0 specs except proposer slashing verification
     */
    method processBlockHeader(s: BeaconState, b: BeaconBlockHeader) returns (s' : BeaconState) 
        //  Verify that the slots match
        requires b.slot == s.slot  
        // Verify that the parent matches
        requires b.parent_root == hash_tree_root(s.latest_block_header) 

        ensures s'.latest_block_header == b.(state_root := EMPTY_BYTES32)
        ensures s'.latest_block_header.parent_root == b.parent_root
        ensures s'.slot == s.slot

        /** The store is not modified. */
        // ensures store == old(store)
    {
        s':= s.(
            latest_block_header := BeaconBlockHeader(
                b.slot,
                b.parent_root,
                EMPTY_BYTES32
            )
        );
    }
    
    //  Specifications of finalisation of a state and forward to future slot.

    /**
     *  Complete the current slot.
     *
     *  @param  s   A beacon state.
     *  @returns    A new state `s' such that:
     *              1. a new latest_block_header' state_root set to the hash_tree_root(s) 
     *              2. the hash_tree_root(s) archived in the s'.state_roots for the slot
     *              3. the hash_tree_root of the new_block_header is archived 
     *              in s'.block_roots
     */
    function resolveStateRoot(s: BeaconState): BeaconState 
        //  Make sure s.slot does not  overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        //  parent_root of the state block header is preserved
        ensures s.latest_block_header.parent_root == resolveStateRoot(s).latest_block_header.parent_root
    {
        // var new_latest_block_header := s.latest_block_header.(state_root := hash_tree_root(s));
        BeaconState(
            // slot unchanged
            s.slot + 1,
            if (s.latest_block_header.state_root == EMPTY_BYTES32 ) then 
                s.latest_block_header.(state_root := hash_tree_root(s))
            else 
                s.latest_block_header
            //  add new block_header root to block_roots history.
            // s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(new_latest_block_header)],
            //  add previous state root to state_roots history
            // s.state_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s)]
        )
    }

    /**
     *  Finalise a state and forward to slot in the future.
     *  
     *  @param  s       A state
     *  @param  slot    A slot. 
     *  @returns        A new state obtained by  archiving roots and incrementing slot.
     *                  slot.
     */
    function forwardStateToSlot(s: BeaconState, slot: Slot) : BeaconState 
        requires s.slot <= slot

        ensures forwardStateToSlot(s, slot).slot == slot
        ensures forwardStateToSlot(s, slot).latest_block_header ==  s.latest_block_header

        //  termination ranking function
        decreases slot - s.slot
    {
        if (s.slot == slot) then 
            s
        else
            nextSlot(forwardStateToSlot(s, slot - 1))
    }

    /**
     *  Advance a state by one slot.
     *
     *  @param  s   A beacon state.
     *  @returns    The successor state for `slot + 1`.
     *
     *  @note       This function increment the slot number and archives 
     *              the previous state_root and block_root, and copy verbatim the 
     *              latest_block_header.
     */
    function nextSlot(s : BeaconState) : BeaconState 
        //  Make sure s.slot does not overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        // ensures nextSlot(s).latest_block_header ==  s.latest_block_header
    {
        //  Add header root to history of block_roots
        // var new_block_roots := s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s.latest_block_header)];
        //  Add state root to history of state roots
        // var new_state_roots := s.state_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s)];
        //  Increment slot and copy latest_block_header
        // BeaconState(s.slot + 1, s.latest_block_header, new_block_roots, new_state_roots)
        s.(slot := s.slot + 1)
    }
}