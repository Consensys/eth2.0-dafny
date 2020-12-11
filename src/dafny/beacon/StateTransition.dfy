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

include "../utils/NativeTypes.dfy"
include "../utils/NonNativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "forkchoice/ForkChoiceTypes.dfy"
include "../utils/Helpers.dfy"
include "../ssz/Constants.dfy"
include "BeaconChainTypes.dfy"
include "Validators.dfy"
include "attestations/AttestationsTypes.dfy"
include "Helpers.dfy"
include "StateTransition.s.dfy"

/**
 * State transition function for the Beacon Chain.
 */
module StateTransition {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NativeTypes
    import opened NonNativeTypes
    import opened Eth2Types
    import opened ForkChoiceTypes
    import opened Constants
    import opened BeaconChainTypes
    import opened Validators
    import opened AttestationsTypes
    import opened Helpers
    import opened BeaconHelpers
    import opened StateTransitionSpec

// # Attestations
//     previous_epoch_attestations: List[PendingAttestation, MAX_ATTESTATIONS * SLOTS_PER_EPOCH]
//     current_epoch_attestations: List[PendingAttestation, MAX_ATTESTATIONS * SLOTS_PER_EPOCH]
//     # Finality
//     justification_bits: Bitvector[JUSTIFICATION_BITS_LENGTH]  # Bit set for every recent justified epoch
//     previous_justified_checkpoint: Checkpoint  # Previous epoch snapshot
//     current_justified_checkpoint: Checkpoint
//     finalized_checkpoint: Checkpoint

    /**
     *  Whether a block is valid in a given state.
     *
     *  @param  s   A beacon state.
     *  @param  b   A block.
     *
     *  @returns    true iff `b` can be successfully added to the state `s`.
     */
    predicate isValidBlock(s : BeaconState, b : BeaconBlock) 
    {
        //  The block slot should be in the future.
        s.slot < b.slot 
        //  Fast forward s to b.slot and check `b` can be attached to the
        //  resulting state's latest_block_header.
        //  Check that number of deposits in b.body can be processed
        && s.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000  
        && |s.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        // note that |b.body.deposits| is larger than required, only existing + new validators need to obey this bound
        && total_balances(s.balances) + total_deposits(b.body.deposits) < 0x10000000000000000
        // note that the |b.body.deposits| and total_deposits should refer to valid deposits
        && |s.validators| == |s.balances|
        && b.parent_root == 
            hash_tree_root(
                forwardStateToSlot(nextSlot(s), 
                b.slot
            ).latest_block_header) 
        //  Check that the block provides the correct hash for the state.
        &&  b.state_root == hash_tree_root(
                updateDeposits(
                    addBlockToState(
                        forwardStateToSlot(nextSlot(s), b.slot), 
                        b
                    ),
                    b.body.deposits
                )
            )
    }

    /**
     *  Compute the state obtained after adding a block.
     *  
     *  @param      s   A beacon state.
     *  @param      b   A block.
     *  @returns        The state obtained after adding `b` to the current state.
     *                  
     */
     method stateTransition(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState)
        //  make sure the last state was one right after addition of new block
        requires isValidBlock(s, b)

        requires s.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000 
        requires |s.validators| == |s.balances| 

        /** The next state latest_block_header is same as b except for state_root that is 0. */
        ensures s'.latest_block_header == BeaconBlockHeader(b.slot, b.parent_root, DEFAULT_BYTES32)
        /** s' slot is now adjusted to the slot of b. */
        ensures s'.slot == b.slot
        /** s' parent_root is the hash of the state obtained by resolving/forwarding s to
            the slot of b.  */
        ensures s'.latest_block_header.parent_root  == 
            hash_tree_root(
                forwardStateToSlot(nextSlot(s), b.slot)
                .latest_block_header
            )
        ensures s'.eth1_deposit_index as int == s.eth1_deposit_index as int + |b.body.deposits|
        ensures s'.validators == updateDeposits(addBlockToState(forwardStateToSlot(nextSlot(s), b.slot),b),b.body.deposits).validators
        ensures s'.balances == updateDeposits(addBlockToState(forwardStateToSlot(nextSlot(s), b.slot),b),b.body.deposits).balances
        ensures |s'.validators| == |s'.balances|
    {
        //  finalise slots before b.slot.
        var s1 := processSlots(s, b.slot);

        assert (s1.slot == forwardStateToSlot(nextSlot(s), b.slot).slot );
        assert (s1.slot == b.slot);
        assert (s1.balances == s.balances);

        //  Process block and compute the new state.
        s' := processBlock(s1, b);  
        assert (s'.slot == b.slot);  

        // Verify state root (from eth2.0 specs)
        // A proof that this function is correct establishes that this assert statement 
        // is never violated (i.e. when isValidBlock() is true.)
        // In the Eth2.0 specs this check is conditional but enabled by default.
        assert (b.state_root == hash_tree_root(s'));
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
     *  @returns        The state obtained after advancing the histories to slot.
     *      
     *  @note           The specs have the the first processSlot integrated in the while loop. 
     *                  However, because s.slot < slot, the while bdoy must be executed at least 
     *                  one time. To simplify the proof, we have taken this first iteration 
     *                  outside of the loop. It does not change the semantics but enables us to 
     *                  use the state obtained after the first iteration the loop and prove it 
     *                  is the same as resolveStateRoot(s).
     *
     */
    method {:timeLimitMultiplier 10} processSlots(s: BeaconState, slot: Slot) returns (s' : BeaconState)
        requires s.slot < slot  //  update in 0.12.0 (was <= before)
        requires |s.validators| == |s.balances|
        
        ensures s' == forwardStateToSlot(nextSlot(s), slot)   //  I1
        // The next one is a direct consequence of I1
        ensures s'.slot == slot
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|

        //  Termination ranking function
        decreases slot - s.slot
    {
        //  Start from the current state and update it with processSlot.
        //  This is the first iteration of the loop in process_slots (Eth2-specs)
        s' := processSlot(s);
        if (s'.slot + 1) % SLOTS_PER_EPOCH  == 0 {
            s' := process_epoch(s');
        } 
        s':= s'.(slot := s'.slot + 1) ;
        assert(s' == nextSlot(s));
        //  s'.block header state_root should now be resolved
        assert(s'.latest_block_header.state_root != DEFAULT_BYTES32);

        //  Now fast forward state to `slot`
        while (s'.slot < slot)  
            invariant s'.slot <= slot
            invariant s'.latest_block_header.state_root != DEFAULT_BYTES32
            invariant s' == forwardStateToSlot(nextSlot(s), s'.slot) 
            invariant s'.eth1_deposit_index == s.eth1_deposit_index
            invariant s'.validators == s.validators
            invariant s'.balances == s.balances
            invariant |s'.validators| == |s'.balances|
            decreases slot - s'.slot 
        {     
            s':= processSlot(s');
            //  Process epoch on the start slot of the next epoch
            if (s'.slot + 1) % SLOTS_PER_EPOCH  == 0 {
                var k := s'; 
                s' := process_epoch(s');
            }
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
     */
    method processSlot(s: BeaconState) returns (s' : BeaconState)
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        requires |s.validators| == |s.balances|

        ensures  s.latest_block_header.state_root == DEFAULT_BYTES32 ==>
            s' == resolveStateRoot(s).(slot := s.slot)
        ensures  s.latest_block_header.state_root != DEFAULT_BYTES32 ==>
            s' == advanceSlot(s).(slot := s.slot)
        ensures s.latest_block_header.parent_root == s'.latest_block_header.parent_root
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
    {
        s' := s;

        //  Cache state root. Record the hash of the previous state in the history.
        var previous_state_root := hash_tree_root(s); 

        s' := s'.(state_roots := s'.state_roots[(s'.slot % SLOTS_PER_HISTORICAL_ROOT) as int := previous_state_root]);

        //  Cache latest block header state root
        if (s'.latest_block_header.state_root == DEFAULT_BYTES32) {
            s' := s'.(latest_block_header := s'.latest_block_header.(state_root := previous_state_root));
        }

        //  Cache block root
        var previous_block_root := hash_tree_root(s'.latest_block_header);

        //  Compute the final value of the new state.
        s' := s'.(block_roots := s'.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := previous_block_root]);
    }

    /**
     *  Verify that a block is valid.
     *  
     *  @param      s   A beacon state.   
     *  @param      b   A block header.
     *  @returns        The state obtained after processing `b`.
     *
     *  @note   Matches eth2.0 specs, need to implement randao, eth1, operations. 
     */
     method processBlock(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState) 
        requires b.slot == s.slot
        requires b.parent_root == hash_tree_root(s.latest_block_header)
        requires s.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000  
        requires |s.validators| == |s.balances|
        requires |s.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        requires total_balances(s.balances) + total_deposits(b.body.deposits) < 0x10000000000000000


        ensures s' == updateDeposits(addBlockToState(s, b), b.body.deposits)
        ensures s'.slot == b.slot
        ensures s'.latest_block_header == BeaconBlockHeader(b.slot, b.parent_root, DEFAULT_BYTES32)
        ensures |s'.validators| == |s'.balances|
    {
        //  Start by creating a block header from the ther actual block.
        s' := processBlockHeader(s, b); 
        assert (s'.balances == s.balances);
        
        //  process_randao(s, b.body)
        //  process_eth1_data(s, b.body)
        s' := process_operations(s', b.body);
    }

    /**
     *  Check whether a block is valid and prepare and initialise new state
     *  with a corresponding block header. 
     *
     *  @param  s   A beacon state.
     *  @param  b   A block.
     *  @returns    The state obtained processing the block.
     *
     *  @note   Matches eth2.0 specs except proposer slashing verification.
     */
    method processBlockHeader(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState) 
        //  Verify that the slots match
        requires b.slot == s.slot  
        //  Verify that the parent matches
        requires b.parent_root == hash_tree_root(s.latest_block_header) 

        requires |s.validators| == |s.balances|
        requires |s.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        

        requires s.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000 

        ensures s' == addBlockToState(s, b)
        ensures s'.slot == b.slot
        ensures s'.latest_block_header == BeaconBlockHeader(b.slot, b.parent_root, DEFAULT_BYTES32)
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
        //ensures |s'.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
    {
        s':= s.(
            latest_block_header := BeaconBlockHeader(
                b.slot,
                b.parent_root,
                DEFAULT_BYTES32
            )
        );
    }
    
    /**
     *  At epoch boundaries, update justifications, rewards, penalities,
     *  resgistry, slashing, and final updates.
     *
     *  @param  s   A beacon state.
     *  @returns    
     *  @todo       To be specified and implemented. currently returns s.
     */
    method process_epoch(s: BeaconState) returns (s' : BeaconState) 
        //  Make sure s.slot does not overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        //  And we should only execute this method when:
        requires (s.slot + 1) % SLOTS_PER_EPOCH == 0
        // ensures s' == updateFinalisedCheckpoint(updateJustification(s))
        ensures s' == finalUpdates(updateFinalisedCheckpoint(updateJustification(s)))
        requires |s.validators| == |s.balances|

        // ensures s' == updateFinalisedCheckpoint(updateJustification(s))

        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
    {
        assert(s.slot % SLOTS_PER_EPOCH != 0);
        s' := process_justification_and_finalization(s);
        // process_rewards_and_penalties(state)
        // process_registry_updates(state)
        // process_slashings(state)
        s' := process_final_updates(s');
        // assert(s' == finalUpdates(s2));
        // assume(s' == forwardStateToSlot(s, s.slot));
        // assume(s' == resolveStateRoot(s));
        return s';
    }

    /**
     *  Rotate the attestations.
     *  @param  s   A state.
     *  @returns    `s` with attestations rotated.
     *
     *  @todo       This is a partial implementation capturing only
     *              the attestations updates.
     */
    method process_final_updates(s: BeaconState)  returns (s' : BeaconState)
        ensures s' == finalUpdates(s)
    {
        s' := s.(
            previous_epoch_attestations := s.current_epoch_attestations,
            current_epoch_attestations := []
        );
    }

    /**
     *  Update justification and finalisation status.
     *
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#justification-and-finalization}
     */
    method process_justification_and_finalization(s : BeaconState) returns (s' : BeaconState) 
        requires s.slot % SLOTS_PER_EPOCH != 0
        requires |s.validators| == |s.balances|

        ensures s' == updateFinalisedCheckpoint(updateJustification(s))
        
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
    {
        //  epoch in state s is given by s.slot

        if get_current_epoch(s) <= GENESIS_EPOCH + 1 {
            //  Initial FFG checkpoint values have a `0x00` stub for `root`.
            //  Skip FFG updates in the first two epochs to avoid corner cases 
            //  that might result in modifying this stub.
            return s;   
        } else {
            assert(get_current_epoch(s) >= 2);
            //  Process justifications and finalisations
            var previous_epoch := get_previous_epoch(s);
            var current_epoch := get_current_epoch(s);
            assert(previous_epoch == current_epoch - 1);
            assert(previous_epoch as int * SLOTS_PER_EPOCH as int  < s.slot as int);
            assert(s.slot as int - (previous_epoch as int *  SLOTS_PER_EPOCH as int) 
                        <=  SLOTS_PER_HISTORICAL_ROOT as int );
            // old_previous_justified_checkpoint = state.previous_justified_checkpoint
            // old_current_justified_checkpoint = state.current_justified_checkpoint

            //  Process justifications and update justification bits
            // state.previous_justified_checkpoint = state.current_justified_checkpoint
            s' := s.(previous_justified_checkpoint := s.current_justified_checkpoint);

            // state.justification_bits[1:] = state.justification_bits[:JUSTIFICATION_BITS_LENGTH - 1]
            // state.justification_bits[0] = 0b0

            //  Right-Shift of justification bits and initialise first to false
            s' := s'.(justification_bits := [false] + (s.justification_bits)[..JUSTIFICATION_BITS_LENGTH - 1]); 
            //  Determine whether ??
            assert(get_previous_epoch(s') <= previous_epoch <= get_current_epoch(s'));
            assert(s'.slot == s.slot);
            assert(previous_epoch as int * SLOTS_PER_EPOCH as int  < s'.slot as int);
            //  slot of previous epoch is not too far in the past
            assert(s'.slot as int - (previous_epoch as int *  SLOTS_PER_EPOCH as int) 
                        <=  SLOTS_PER_HISTORICAL_ROOT as int );
            assert(s'.block_roots == s.block_roots);
            assert(get_block_root(s', previous_epoch) == get_block_root(s, previous_epoch));
            assert(|s'.validators| == |s.validators|);
            var matching_target_attestations_prev := get_matching_target_attestations(s', previous_epoch) ;  
            // Previous epoch
            if get_attesting_balance(s', matching_target_attestations_prev) as uint128 * 3 >=       
                                get_total_active_balance(s') as uint128 * 2 {
                //  shift the justified checkpoint
                //  @todo   Why is current_justified_checkpoint field updated and not 
                //          previous?
                s' := s'.(current_justified_checkpoint := 
                            CheckPoint(previous_epoch,
                                        get_block_root(s', previous_epoch)));
                s' := s'.(justification_bits := s'.justification_bits[1 := true]);
            }
            // assert(s'.justification_bits == updateJustificationPrevEpoch(s).justification_bits);
            assert(s'.slot == updateJustificationPrevEpoch(s).slot);
            assert(s'.current_justified_checkpoint == updateJustificationPrevEpoch(s).current_justified_checkpoint);
            assert(s'.previous_justified_checkpoint == updateJustificationPrevEpoch(s).previous_justified_checkpoint);
            assert(s' == updateJustificationPrevEpoch(s)); 

            ghost var s2 := s';
            //  Current epoch
            var matching_target_attestations_cur := get_matching_target_attestations(s', current_epoch) ;
            if get_attesting_balance(s', matching_target_attestations_cur) as nat * 3 >=       
                                    get_total_active_balance(s') as nat * 2 {
                //  shift the justified checkpoint
                // s' := s'.(current_justified_checkpoint := 
                //             CheckPoint( current_epoch,
                //                         get_block_root(s', previous_epoch)));
                s' := s'.(
                        justification_bits := s'.justification_bits[0 := true],
                        current_justified_checkpoint := 
                            CheckPoint(current_epoch,
                                        get_block_root(s', current_epoch)));
            }
            assert(s' == updateJustificationCurrentEpoch(s2));
            // if get_attesting_balance(state, matching_target_attestations) * 3 >= get_total_active_balance(state) * 2:
    //     state.current_justified_checkpoint = Checkpoint(epoch=current_epoch,
    //                                                     root=get_block_root(state, current_epoch))
    //     state.justification_bits[0] = 0b1

            // assume(s' == updateJustification(s1));
            //  Process finalizations
            /*
             *  Epochs layout
             *
             *  | ............ | ........... | .......... | 
             *  | ............ | ........... | .......... | 
             *  e1             e2            e3           e4
             *  bit[0]        bit[1]        bit[2]        bit[3]
             *  current       previous
             *
             *  Python slice a[k:l] means: a[k] ... a[l -1]
             */
            ghost var s3 := s';

            var bits : seq<bool> := s'.justification_bits;
            //  The 2nd/3rd/4th most recent epochs are justified, the 2nd using the 4th as source
            // assume(s.previous_justified_checkpoint.epoch as nat + 3 < 0x10000000000000000 );
            //  if current_epoch == 2, s.previous_justified_checkpoint.epoch + 3 >= 3 so the 
            //  following condition is false. As a result we do not need to compute 
            //  s.previous_justified_checkpoint.epoch + 3 and can avoid a possible overflow.
            //  We assume here that the target language is such that AND conditions are evaluated ///   short-circuit i.e. unfolded as nested ifs
            //  
            if (all(bits[1..4]) && current_epoch >= 3 && s'.previous_justified_checkpoint.epoch  == current_epoch - 3) {
                s' := s'.(finalised_checkpoint := s'.previous_justified_checkpoint) ;
            }
            //  The 2nd/3rd most recent epochs are justified, the 2nd using the 3rd as source
            if (all(bits[1..3]) && s'.previous_justified_checkpoint.epoch == current_epoch - 2) {
                s' := s'.(finalised_checkpoint := s'.previous_justified_checkpoint) ;
            }
            //  The 1st/2nd/3rd most recent epochs are justified, the 1st using the 3rd as source
            if (all(bits[0..3]) && s'.current_justified_checkpoint.epoch == current_epoch - 2) {
                s' := s'.(finalised_checkpoint := s'.current_justified_checkpoint) ;
            }
            //  The 1st/2nd most recent epochs are justified, the 1st using the 2nd as source
            if (false && all(bits[0..2]) && s'.current_justified_checkpoint.epoch == current_epoch - 1) {
                s' := s'.(finalised_checkpoint := s'.current_justified_checkpoint) ;
            }
            assert(s' == updateFinalisedCheckpoint(s3));
            return s';
        }

    //  previous_epoch = get_previous_epoch(state)
    // current_epoch = get_current_epoch(state)
    // old_previous_justified_checkpoint = state.previous_justified_checkpoint
    // old_current_justified_checkpoint = state.current_justified_checkpoint
    //  Process justifications
    // state.previous_justified_checkpoint = state.current_justified_checkpoint
    // state.justification_bits[1:] = state.justification_bits[:JUSTIFICATION_BITS_LENGTH - 1]
    // state.justification_bits[0] = 0b0
    // matching_target_attestations = get_matching_target_attestations(state, previous_epoch)  # Previous epoch
    // if get_attesting_balance(state, matching_target_attestations) * 3 >= get_total_active_balance(state) * 2:
    //     state.current_justified_checkpoint = Checkpoint(epoch=previous_epoch,
    //                                                     root=get_block_root(state, previous_epoch))
    //     state.justification_bits[1] = 0b1
    // matching_target_attestations = get_matching_target_attestations(state, current_epoch)  # Current epoch
    // if get_attesting_balance(state, matching_target_attestations) * 3 >= get_total_active_balance(state) * 2:
    //     state.current_justified_checkpoint = Checkpoint(epoch=current_epoch,
    //                                                     root=get_block_root(state, current_epoch))
    //     state.justification_bits[0] = 0b1

    //  Process finalizations
    // bits = state.justification_bits
    //  The 2nd/3rd/4th most recent epochs are justified, the 2nd using the 4th as source
    // if all(bits[1:4]) and old_previous_justified_checkpoint.epoch + 3 == current_epoch:
    //     state.finalized_checkpoint = old_previous_justified_checkpoint
    //  The 2nd/3rd most recent epochs are justified, the 2nd using the 3rd as source
    // if all(bits[1:3]) and old_previous_justified_checkpoint.epoch + 2 == current_epoch:
    //     state.finalized_checkpoint = old_previous_justified_checkpoint
    //  The 1st/2nd/3rd most recent epochs are justified, the 1st using the 3rd as source
    // if all(bits[0:3]) and old_current_justified_checkpoint.epoch + 2 == current_epoch:
    //     state.finalized_checkpoint = old_current_justified_checkpoint
    //  The 1st/2nd most recent epochs are justified, the 1st using the 2nd as source
    // if all(bits[0:2]) and old_current_justified_checkpoint.epoch + 1 == current_epoch:
    //     state.finalized_checkpoint = old_current_justified_checkpoint


        return s;
    }


    

    /**
     *  Process the operations defined by a block body.
     *  
     *  @param  s   A state.
     *  @param  bb  A block body.
     *  @returns    The state obtained after applying the operations of `bb` to `s`.
     */
        method process_operations(s: BeaconState, bb: BeaconBlockBody)  returns (s' : BeaconState) 
        requires s.eth1_deposit_index as int +  |bb.deposits| < 0x10000000000000000 
        requires |s.validators| + |bb.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        requires |s.validators| == |s.balances|
        requires total_balances(s.balances) + total_deposits(bb.deposits) < 0x10000000000000000 
        
        //ensures |s'.validators| == |s'.balances|
        ensures s' == updateDeposits(s, bb.deposits)
        ensures s'.slot == s.slot
        ensures s'.latest_block_header == s.latest_block_header
        //ensures s'.validators == s.validators + get_new_validators(s, [], bb.deposits)
        //ensures false
    {
        //  process deposits in the beacon block body.
        s':= s;

        var i := 0;
        assert s' == updateDeposits(s, bb.deposits[..i]);
        assert total_balances(s'.balances) + total_deposits(bb.deposits[..i]) < 0x10000000000000000 ;
        
        while i < |bb.deposits| 
            decreases |bb.deposits| - i

            invariant 0 <= i <= |bb.deposits|
            invariant s'.eth1_deposit_index == s.eth1_deposit_index + i as uint64
            
            invariant total_balances(s.balances) + total_deposits(bb.deposits[..i]) < 0x10000000000000000 
            //invariant s'.validators == updateDeposits(s, bb.deposits[..i]).validators
            //invariant s'.balances == updateDeposits(s, bb.deposits[..i]).balances
            
            //invariant total_balances(updateDeposits(s,bb.deposits[..i]).balances) == total_balances(s.balances) + total_deposits(bb.deposits[..i]) < 0x10000000000000000
            
            //invariant s'.slot == s.slot 
            //invariant s'.latest_block_header == s.latest_block_header
            //invariant s'.block_roots == s.block_roots
            //invariant s'.state_roots == s.state_roots

            //invariant |s'.validators| == |s'.balances| 
            //invariant |s'.validators| <= |s.validators| + i
            //invariant |s.validators| + i <= VALIDATOR_REGISTRY_LIMIT as int
            invariant s' == updateDeposits(s, bb.deposits[..i])
            invariant s'.slot == s.slot
            invariant s'.latest_block_header == s.latest_block_header
            //invariant |bb.deposits[..i]| == i

            //invariant |s'.validators| <= |updateDeposits(s,bb.deposits[..i]).validators| <= |s'.validators| + i 
        {
            assert bb.deposits[..i+1] == bb.deposits[..i] + [bb.deposits[i]];
            //assert total_balances(updateDeposits(s, bb.deposits[..i]).balances) + bb.deposits[i].data.amount as int == total_balances(s.balances) + total_deposits(bb.deposits[..i]) + bb.deposits[i].data.amount as int;
            //assert total_deposits(bb.deposits[..i]) + bb.deposits[i].data.amount as int == total_deposits(bb.deposits[..i+1]);
            //assert total_balances(updateDeposits(s, bb.deposits[..i]).balances) + bb.deposits[i].data.amount as int == total_balances(s.balances) + total_deposits(bb.deposits[..i+1]);
            //assert i + 1  <= |bb.deposits|;
            subsetDepositSumProp(bb.deposits, i+1);
            //assert total_deposits(bb.deposits[..i+1]) <= total_deposits(bb.deposits);
            //assert total_balances(updateDeposits(s, bb.deposits[..i]).balances) + bb.deposits[i].data.amount as int < 0x10000000000000000;

            //assert updateDeposit(updateDeposits(s, bb.deposits[..i]),bb.deposits[i]) == updateDeposits(s, bb.deposits[..i+1]);
            
            s':= process_deposit(s', bb.deposits[i]); 
            i := i+1;

        }
        assert bb.deposits[..i] == bb.deposits;

    }

    /**
     *  Process a deposit operation.
     *
     *  @param  s   A state.
     *  @param  d   A deposit.  
     *  @returns    The state obtained depositing of `d` to `s`.
     *  @todo       Finish implementation of this function.
     */
    method process_deposit(s: BeaconState, d : Deposit)  returns (s' : BeaconState)  
        requires |s.validators| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
        requires s.eth1_deposit_index as int + 1 < 0x10000000000000000 
        requires |s.validators| == |s.balances|
        requires total_balances(s.balances) + d.data.amount as int < 0x10000000000000000

        ensures s'.eth1_deposit_index == s.eth1_deposit_index + 1
        //ensures d.data.pubkey !in seqKeysInValidators(s.validators) ==> s'.validators == s.validators + [get_validator_from_deposit(d)]
        //ensures d.data.pubkey in seqKeysInValidators(s.validators) ==> s'.validators == s.validators 
        ensures s' == updateDeposit(s,d)

        //ensures |s'.validators| == |s'.balances|        // maybe include in property lemmas
        //ensures |s.validators| <= |s'.validators| <= |s.validators| + 1 // maybe include in property lemmas
        //ensures |s.balances| <= |s'.balances| <= |s.balances| + 1 // maybe include in property lemmas
        //ensures |s'.validators| <= VALIDATOR_REGISTRY_LIMIT
        
    {
        // note that it is assumed that all new validator deposits are verified
        // ie the step # Verify the deposit signature (proof of possession) which is not checked by the deposit contract
        // is not performed
        var pk := seqKeysInValidators(s.validators);
        s' := s.(
                eth1_deposit_index := (s.eth1_deposit_index as int + 1) as uint64,
                validators := if d.data.pubkey in pk then 
                                    s.validators // unchanged validator members
                                else 
                                    (s.validators + [get_validator_from_deposit(d)]),
                balances := if d.data.pubkey in pk then 
                                    individualBalanceBoundMaintained(s.balances,d);
                                    increase_balance(s,get_validator_index(pk, d.data.pubkey),d.data.amount).balances
                                else 
                                    s.balances + [d.data.amount]
        );
    }

    
}