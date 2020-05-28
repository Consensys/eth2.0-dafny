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
    function method hash_tree_root(s: BeaconState) : Bytes32 
    // function method hash_tree_root_block(s: BeaconBlock) : Bytes32 
    function method hash_tree_root_block_header(b: BeaconBlockHeader) : Bytes32 
        ensures hash_tree_root_block_header(b) == EMPTY_BYTES32 <==> isGenesisBlockHeader(b)

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
        latest_block_header: BeaconBlockHeader,
        block_roots: VectorOfHistRoots,
        state_roots: VectorOfHistRoots
    )

    /**
     *  The history of blocks
     */
    datatype History = History(
        blocks: map<Slot,BeaconBlock>,
        chain: map<BeaconBlock, BeaconBlockHeader>
    )

    /**
     *  The default block header.
     */
    const EMPTY_BLOCK_HEADER := BeaconBlockHeader(0, EMPTY_BYTES32, EMPTY_BYTES32)
    
    const GENESIS_BLOCK_HEADER := EMPTY_BLOCK_HEADER

    /**
     *  Initial beacon state.
     */
    const initState := BeaconState(0, EMPTY_BLOCK_HEADER, EMPTY_HIST_ROOTS, EMPTY_HIST_ROOTS)

    /**
     *  Consistency of a state.
     */
    predicate isConsistent(s: BeaconState, h: History) 
    {
        true
        // forall i :: 0 < i < s.slot ==> h.chain()
    }

    /**
     */
    predicate isGenesisBlock(b : BeaconBlock) 
    {
        b == BeaconBlock(
            0 as Slot,
            EMPTY_BYTES32,
            EMPTY_BYTES32
        )
    }

    /**
     *  Whether a block header is a genesis block header.
     */
    predicate isGenesisBlockHeader(b : BeaconBlockHeader) 
    {
        //  Genesis block header must be for slot 0 and have a default parent_root
        //  and state root Bytes32()
        b == BeaconBlockHeader(
            0 as Slot,
            EMPTY_BYTES32,
            EMPTY_BYTES32
        )
    }

    /**
     *  A Beacon Chain environement i.e. with Store etc
     */
    class Env {

        /**
         *  The record of blocks that have been accepted.
         */
        var store : map<Bytes32, BeaconBlockHeader> 

        predicate isConsistent() 
            reads this
        {
            forall b :: b in store.Values && !isGenesisBlockHeader(b) ==>  
                b.parent_root != EMPTY_BYTES32 && b.parent_root in store.Keys && store[b.parent_root].slot < b.slot
            &&
            // exists k :: k in store.Keys && store[k] == s.latest_block_header 
            forall k :: k in store.Keys && !isGenesisBlockHeader(store[k]) ==>  
                store[k].parent_root != EMPTY_BYTES32 && store[k].parent_root in store.Keys && store[b.parent_root].slot < b.slot
        }

        /**
        *  Compute the state obtained after adding a block.
        */
        method stateTransition(s: BeaconState, b: BeaconBlockHeader, ghost h: History) returns (s' : BeaconState )
            // requires isReachableFromGenesis(s.latest_block_header)
            // requires !isGenesisBlock(b)
            requires s.latest_block_header in store.Values
            requires isConsistent()
            requires hash_tree_root_block_header(b) !in store.Keys
            requires s.slot <= b.slot
            requires b.parent_root == s.latest_block_header.parent_root
            // ensures isConsistent()
            modifies this
        {
            //  finalise slots before b.slot
            var s1 := processSlots(s, b.slot);
            assert(s1.latest_block_header.parent_root ==  s.latest_block_header.parent_root); 
            assert(isConsistent());

            // assert(b.parent_root == hash_tree_root_block_header(s.latest_block_header));
            //  Process block
            s' := processBlock(s1, b);
            // assert(s'.latest_block_header.parent_root !=  EMPTY_BYTES32); 
            // assert(s'.latest_block_header.parent_root ==  b.parent_root); 
            // assert(isConsistent());

            // assert(s'.latest_block_header in store.Values); 
            // assert(hash_tree_root_block_header(b) !in store.Keys);
            //  the key for the s.latest_block_header cannot be hash_tree_root_block_header(b)
            // assert(exists k:: k in store.Keys && store[k] == s'.latest_block_header);
            // var k :| k in store.Keys && store[k] == s.latest_block_header;
            // assert( k != hash_tree_root_block_header(b));
            //  Add the block to the global Store
            store := store[hash_tree_root_block_header(b) := b];
            // assert(b.slot > store[b.parent_root].slot);
            // assert(b.parent_root != EMPTY_BYTES32);
            // assert(forall i :: i in store.Keys && i != hash_tree_root_block_header(b) ==> 
                // store[i] == old(store)[i]);
            // assert(s.latest_block_header in store.Values); 
            // assert(s.latest_block_header.parent_root in store.Keys); 
            // assert(b.parent_root in store.Keys);
            // assert(isConsistent());

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
        */
    method processSlots(s: BeaconState, slot: Slot) returns (s' : BeaconState)
            requires s.slot <= slot
            ensures  s'.slot == slot 
            ensures s.latest_block_header.parent_root == s'.latest_block_header.parent_root
            // ensures s'.latest_block_header.parent_root != EMPTY_BYTES32
            ensures store == old(store)
            decreases slot - s.slot
        {
            //  start from thr current state
            s' := s;
            while (s'.slot < slot)  
                invariant s'.slot <= slot
                invariant s.latest_block_header.parent_root == s'.latest_block_header.parent_root
                decreases slot - s'.slot 
            {
                //  s'.slot < slot. Complete processing of s'.slot 
                //  The slot number s'.slot is incremented after as
                //  process_slot 
                s':= processSlot(s');
                //  s'.slot is now processed: history updates and block header resolved
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
        */
        function method processSlot(s: BeaconState) : BeaconState
            ensures processSlot(s).slot == s.slot
            ensures s.latest_block_header.parent_root == processSlot(s).latest_block_header.parent_root
        {
            //  Let definitions for readability.

            //  Record the hash of the previous state in the history.
            var previous_state_root := hash_tree_root(s); 
            //  The block header in the state may be empty if a new block
            //  was received in the previous slot. It is fixed when finalising a slot.
            var real_latest_block_header := 
                if (s.latest_block_header.state_root == EMPTY_BYTES32) then
                    s.latest_block_header.(state_root := previous_state_root)
                else 
                    s.latest_block_header
                ;     
            //  The fixed block header root.
            var real_latest_block_root := hash_tree_root_block_header(real_latest_block_header);

            //  Define the new state   
            BeaconState(
                // slot unchanged
                s.slot,
                //  block header fixed if there was a new block in previous slot
                real_latest_block_header,
                //  add block roots to history
                s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := real_latest_block_root],
                //  add previous state roots to history
                s.state_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := previous_state_root]
            )
        }

        /**
        *  Verify that a block is valid.
        */
        method processBlock(s: BeaconState, b: BeaconBlockHeader) returns (s' : BeaconState) 
            requires b.slot == s.slot
            // requires b.parent_root == hash_tree_root_block_header(s.latest_block_header)
            ensures s'.latest_block_header.parent_root == b.parent_root
        {
            //  Start by creating a block header from the ther actual block.
            s' := processBlockHeader(s, b);
        }

        /**
        *  Check whether a block is valid and prepare and initialise new state
        *  with a corresponding block header. 
        */
        method processBlockHeader(s: BeaconState, b: BeaconBlockHeader) returns (s' : BeaconState) 
            requires b.slot == s.slot
            // requires b.parent_root == hash_tree_root_block_header(s.latest_block_header)
            ensures s'.latest_block_header.parent_root == b.parent_root
        {
            s':= s.(
                latest_block_header := BeaconBlockHeader(
                    b.slot,
                    b.parent_root,
                    EMPTY_BYTES32
                )
            );
        }
    }

    //  Specifications of finalisation of a state and forward to future slot.

    /**
        *  Complete the current slot.
        *
        *  @param  s   A beacon state.
        *  @returns    A new state `s'` such that:
        *              1. a new latest_block_header' state_root set to the hash_tree_root(s) 
        *              2. the hash_tree_root(s) archived in the s'.state_roots for the slot
        *              3. the hash_tree_root of the new_block_header is archived 
        *              in s'.block_roots
        */
    function resolveStateRoot(s: BeaconState): BeaconState 
    {
        var new_latest_block_header := s.latest_block_header.(state_root := hash_tree_root(s));
        var latest_block_header_root :=  hash_tree_root_block_header(new_latest_block_header);
        BeaconState(
            // slot unchanged
            s.slot,
            //  block header fixed if there was a new block in previous slot
            s.latest_block_header.(state_root := latest_block_header_root),
            //  add new block_header root to block_roots history.
            s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := latest_block_header_root],
            //  add previous state root to state_roots history
            s.state_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s)]
        )
    }

    /**
        *  Finalise a state and forward to slot.
        *  
        *  @param  s       A state
        *  @param  slot    A slot. 
        *  @returns        A new state obtained by  archiving roots and incrementing slot.
        *  slot.
        */
    function forwardStateToSlot(s: BeaconState, slot: Slot) : BeaconState 
        requires s.slot <= slot
        ensures forwardStateToSlot(s, slot).slot == slot
        decreases slot - s.slot
    {
        if (s.slot == slot) then 
            s
        else
            nextSlot(forwardStateToSlot(s, slot - 1))
    }

    function nextSlot(s : BeaconState) : BeaconState 
        //  No overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
    {
        //  Add header root to history of block_roots
        var new_block_roots := s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root_block_header(s.latest_block_header)];
        //  Add state root to history of state roots
        var new_state_roots := s.state_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s)];
        //  Increment slot and copy latest_block_header
        BeaconState(s.slot + 1, s.latest_block_header, new_block_roots, new_state_roots)
    }
}