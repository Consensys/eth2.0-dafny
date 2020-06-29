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

include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "../ssz/Constants.dfy"
include "BeaconConstants.dfy"
include "BeaconChain.dfy"
include "../ssz/Eth2TypeDependentConstants.dfy"
include "../merkle/Merkleise.dfy"

/**
 * State transition function for the Beacon Chain.
 */
module StateTransition {
    
    //  Import some constants and types
    import opened Eth2Types
    import opened Constants
    import opened BeaconChain
    import opened Helpers
    import opened BeaconConstants
    import opened Eth2TypeDependentConstants
    import opened SSZ_Merkleise




    function method castToBeaconState(s:RawSerialisable): BeaconState
    requires s.BeaconState?
    requires wellTypedContainer(s)
    {
        s
    }    

    /**
     *  Whether a block is valid in a given state.
     *
     *  @param  s   A beacon state.
     *  @param  b   A block.
     *
     *  @returns    true iff `b` can be successfully added to the state `s`.
     */
    predicate isValid(s : BeaconState, b : BeaconBlockHeader) 
    {
        s.slot.n < b.slot.n
        //  Fast forward s to b.slot and check `b` can be attached to the
        //  resulting state's latest_block_header.
        && b.parent_root == 
            getHashTreeRootBytes32(
                forwardStateToSlot(resolveStateRoot(s), 
                b.slot.n as Slot
            ).latest_block_header) 
        &&  b.state_root == getHashTreeRootBytes32(
                addBlockToState(
                    forwardStateToSlot(resolveStateRoot(s), b.slot.n as Slot), 
                    b
                )
            )
            
    }

    /**
     *  Compute the state obtained after adding a block.
     */
    method stateTransition(s: BeaconState, b: BeaconBlockHeader) returns (s' : BeaconState)
        //  make sure the last state was one right after addition of new block
        requires isValid(s, b)

        /** The next state latest_block_header is same as b except for state_root that is 0. */
        ensures s'.latest_block_header == b.(state_root := EMPTY_BYTES32)
        /** s' slot is now adjusted to the slot of b. */
        ensures s'.slot.n == b.slot.n
        /** s' parent_root is the hash of the state obtained by resolving/forwarding s to
            the slot of b.  */
        ensures s'.latest_block_header.parent_root  == 
            getHashTreeRootBytes32(
                forwardStateToSlot(resolveStateRoot(s), b.slot.n as Slot)
                .latest_block_header
            )
    {
        //  finalise slots before b.slot.
        var s1 := processSlots(s, b.slot.n as Slot);

        //  Process block and compute the new state.
        s' := processBlock(s1, b);  

        // Verify state root (from eth2.0 specs)
        // A proof that this assert statement is never violated when isValid() is true.
        // if validate_result:
        assert (b.state_root == getHashTreeRootBytes32(s'));

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
     *  @note          The specs have the the first processSlot integrated
     *                  in the while loop. However, because s.slot < slot,
     *                  the while bdoy must be executed at least one time.
     *                  To simplify the proof, we have taken this first iteration
     *                  outside of the loop. It does not change the semantics
     *                  but enables us to use the state obtained after the first
     *                  iteration the loop and prove it is the same as 
     *                  resolveStateRoot(s); 
     *
     */
    method {:fuel wellTypedContainer,2}  processSlots(s: BeaconState, slot: Slot) returns (s' : BeaconState)    
        requires s.slot.n < slot as nat  //  update in 0.12.0 (was <= before)

        ensures s' == forwardStateToSlot( resolveStateRoot(s), slot)
        ensures s.latest_block_header.parent_root == s'.latest_block_header.parent_root  
        
        //  Termination ranking function
        decreases slot as nat - s.slot.n
    {
        //  Start from the current state and update it with processSlot.
        //  First iteration of the loop in process_slots (Eth2)
        s' := processSlot(s);
        s':= castToBeaconState(s'.(slot := Uint64(s'.slot.n + 1))) ;
        //  The following asserts are not needed for the proof but provided for readability. 
        assert(s' == resolveStateRoot(s));  
        //  s'.block header state_root should now be resolved
        assert(s'.latest_block_header.state_root != EMPTY_BYTES32);

        //  Now fast forward to slot
        //  Next iterations of process_slot (Eth2)
        while (s'.slot.n < slot as nat) 
            invariant s'.slot.n <= slot as nat
            invariant s'.latest_block_header.state_root != EMPTY_BYTES32
            invariant s' == forwardStateToSlot(resolveStateRoot(s), s'.slot.n as Slot) // Inv1
            decreases slot as nat - s'.slot.n
        {
            s':= processSlot(s');

            //  s'.slot is now processed: history updated and block header resolved
            //  The state's slot is processed and we can advance to the next slot.
            s':= castToBeaconState(s'.(slot := Uint64(s'.slot.n + 1))) ;
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
    method {:fuel wellTypedContainer,3} {:fuel getHashTreeRootBytes32,0,0} processSlot(s: BeaconState) returns (s' : BeaconState)   
        requires s.slot.n as nat + 1 < 0x10000000000000000 as nat

        ensures  s.latest_block_header.state_root == EMPTY_BYTES32 ==>
            s' == resolveStateRoot(s).(slot := s.slot)
        ensures  s.latest_block_header.state_root != EMPTY_BYTES32 ==>
            s' == nextSlot(s).(slot := s.slot)
        ensures s.latest_block_header.parent_root == s'.latest_block_header.parent_root
    {
        s' := s;

        //  Cache state root
        //  Record the hash of the previous state in the history.
        var previous_state_root := getHashTreeRootBytes32(s); 

        s' := castToBeaconState(s'.(state_roots :=  Vector(s'.state_roots.v[(s'.slot.n % SLOTS_PER_HISTORICAL_ROOT as nat) as int := previous_state_root])));

        //  Cache latest block header state root
        if (s'.latest_block_header.state_root == EMPTY_BYTES32) {
            s' := castToBeaconState(s'.(latest_block_header := s'.latest_block_header.(state_root := previous_state_root)));
        }

        //  Cache block root
        var previous_block_root := getHashTreeRootBytes32(s'.latest_block_header);

        s' := castToBeaconState(s'.(block_roots := Vector(s'.block_roots.v[(s.slot.n % SLOTS_PER_HISTORICAL_ROOT as nat) as int := previous_block_root])));
    }

    /**
     *  Verify that a block is valid.
     *
     *  @note   Matches eth2.0 specs, need to implement randao, eth1, operations. 
     */
    method processBlock(s: BeaconState, b: BeaconBlockHeader) returns (s' : BeaconState) 
        requires b.slot == s.slot
        requires b.parent_root == getHashTreeRootBytes32(s.latest_block_header)

        ensures s' == addBlockToState(s, b)

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
    method {:fuel wellTypedContainer,3} processBlockHeader(s: BeaconState, b: BeaconBlockHeader) returns (s' : BeaconState) 
        //  Verify that the slots match
        requires b.slot == s.slot  
        // Verify that the parent matches
        requires b.parent_root == getHashTreeRootBytes32(s.latest_block_header) 

        ensures s' == addBlockToState(s, b)
    {
        s' :=
        castToBeaconState(
                s.(
                latest_block_header := BeaconBlockHeader(
                    b.slot,
                    b.parent_root,
                    EMPTY_BYTES32
                )
            )
        );
    }
    
    //  Specifications of finalisation of a state and forward to future slot.

    /**
     *  Result of processing a block.
     *  
     *  @param  s   A state.
     *  @param  b   A block to add to the state `s`.
     *  @returns    The state `s` updated to point to `b` with state_root set to 0.
     */
    function {:fuel wellTypedContainer,3} addBlockToState(s: BeaconState, b: BeaconBlockHeader) :  BeaconState 
        //  Verify that the slots match
        requires b.slot == s.slot  
        // Verify that the parent matches
        requires b.parent_root == getHashTreeRootBytes32(s.latest_block_header) 
    {
        castToBeaconState(
            s.(
                latest_block_header := BeaconBlockHeader(
                    b.slot,
                    b.parent_root,
                    EMPTY_BYTES32
                )
            )
        )
    }

    /**
     *  Complete the current slot.
     *
     *  @param  s   A beacon state.
     *  @returns    A new state `s' such that:
     *              1. a new latest_block_header' state_root set to the getHashTreeRootBytes32(s) 
     *              2. the getHashTreeRootBytes32(s) archived in the s'.state_roots for the slot
     *              3. the getHashTreeRootBytes32 of the new_block_header is archived 
     *              in s'.block_roots
     */
    function {:fuel wellTypedContainer,3} {:fuel getHashTreeRootBytes32,0,0} resolveStateRoot(s: BeaconState): BeaconState 
        //  Make sure s.slot does not  overflow
        // requires wellTyped(s)
        requires s.slot.n as nat + 1 < 0x10000000000000000 as nat
        //  parent_root of the state block header is preserved
        ensures s.latest_block_header.parent_root == resolveStateRoot(s).latest_block_header.parent_root
    {
        var new_latest_block_header := 
            if (s.latest_block_header.state_root == EMPTY_BYTES32 ) then 
                s.latest_block_header.(state_root := getHashTreeRootBytes32(s))
            else 
                s.latest_block_header
            ;

        assert wellTypedContainer(new_latest_block_header);
        
        castToBeaconState(
            BeaconState(
                // slot unchanged
                Uint64(s.slot.n + 1),
                new_latest_block_header,
                //  add new block_header root to block_roots history.
                Vector(s.block_roots.v[(s.slot.n % SLOTS_PER_HISTORICAL_ROOT as nat) as int := getHashTreeRootBytes32(new_latest_block_header)]),
                //  add previous state root to state_roots history
                Vector(s.state_roots.v[(s.slot.n % SLOTS_PER_HISTORICAL_ROOT as nat) as int := getHashTreeRootBytes32(s)])
            )
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
    function {:fuel wellTypedContainer,2} forwardStateToSlot(s: BeaconState, slot: Slot) : BeaconState 
        requires s.slot.n <= slot as nat

        ensures forwardStateToSlot(s, slot).slot.n == slot as nat
        ensures forwardStateToSlot(s, slot).latest_block_header ==  s.latest_block_header

        //  termination ranking function
        decreases slot as nat - s.slot.n
    {
        if (s.slot.n == slot as nat) then 
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
    function {:fuel wellTypedContainer,3} nextSlot(s : BeaconState) : BeaconState 
        //  Make sure s.slot does not overflow
        requires s.slot.n as nat + 1 < 0x10000000000000000 as nat
    {
        //  Add header root to history of block_roots
        var new_block_roots := s.block_roots.v[(s.slot.n % SLOTS_PER_HISTORICAL_ROOT as nat) as int := getHashTreeRootBytes32(s.latest_block_header)];
        //  Add state root to history of state roots
        var new_state_roots := s.state_roots.v[(s.slot.n % SLOTS_PER_HISTORICAL_ROOT as nat) as int := getHashTreeRootBytes32(s)];
        //  Increment slot and copy latest_block_header
        castToBeaconState(
            s.(
                slot := Uint64(s.slot.n + 1),
                block_roots := Vector(new_block_roots),
                state_roots := Vector(new_state_roots)
            )
        )
    }
}