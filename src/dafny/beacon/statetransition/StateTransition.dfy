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

//  @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /timeLimit:100 /noCheating:1

include "../../utils/Eth2Types.dfy"
include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../Helpers.dfy"
include "../Helpers.s.dfy"
include "StateTransition.s.dfy"
include "EpochProcessing.dfy"
include "ProcessOperations.dfy"
include "ProcessOperations.s.dfy"

/**
 * State transition function for the Beacon Chain.
 */
module StateTransition {
    
    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened Constants
    import opened BeaconChainTypes
    import opened BeaconHelpers
    import opened BeaconHelperSpec
    import opened StateTransitionSpec
    import opened EpochProcessing
    import opened ProcessOperations
    import opened ProcessOperationsSpec
    

    /**
     *  Compute the state obtained after adding a block.
     *  
     *  @param      s   A beacon state.
     *  @param      b   A block.
     *  @returns        The state obtained after adding `b` to the current state.
     *                  
     */
     method state_transition(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState)
        // A valid state to proceed
        requires |s.validators| == |s.balances| 
        requires is_valid_state_epoch_attestations(s)

        // Make sure the last state was one right after addition of new block
        requires isValidBlock(s, b)

        // The next state is defined by the functional equivalent of process_slots i.e.
        // forwardStateToSlot(nextSlot(s), b.slot), followed by application of the 
        // functional equivalent of process_block:
        // i.e. updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b)
        ensures s' == updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b)
        // /** The next state latest_block_header is same as b except for state_root that is 0. */
        ensures s'.latest_block_header 
            == BeaconBlockHeader(b.slot, b.proposer_index, b.parent_root, DEFAULT_BYTES32)
        // /** s' slot is now adjusted to the slot of b. */
        ensures s'.slot == b.slot
        // /** s' parent_root is the hash of the state obtained by resolving/forwarding s to
        //     the slot of b.  */
        ensures s'.latest_block_header.parent_root  == 
            hash_tree_root(
                forwardStateToSlot(nextSlot(s), b.slot)
                .latest_block_header
            )
        ensures |s'.validators| == |s'.balances|

        ensures s'
                == s.(slot := forwardStateToSlot(nextSlot(s), b.slot).slot,
                      latest_block_header := updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b).latest_block_header,
                      block_roots := forwardStateToSlot(nextSlot(s), b.slot).block_roots,
                      state_roots := forwardStateToSlot(nextSlot(s), b.slot).state_roots,
                      validators := updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b).validators,
                      balances := updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b).balances,
                      slashings := updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b).slashings,
                      eth1_deposit_index := updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b).eth1_deposit_index,
                      eth1_data_votes := updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b).eth1_data_votes,
                      eth1_data := updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b).eth1_data,
                      randao_mixes := updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b).randao_mixes,
                      historical_roots := forwardStateToSlot(nextSlot(s), b.slot).historical_roots,
                      previous_epoch_attestations := updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b).previous_epoch_attestations,
                      current_epoch_attestations := updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b).current_epoch_attestations,
                      current_justified_checkpoint := forwardStateToSlot(nextSlot(s), b.slot).current_justified_checkpoint,
                      previous_justified_checkpoint := forwardStateToSlot(nextSlot(s), b.slot).previous_justified_checkpoint,
                      justification_bits := forwardStateToSlot(nextSlot(s), b.slot).justification_bits,
                      finalised_checkpoint := forwardStateToSlot(nextSlot(s), b.slot).finalised_checkpoint
                     )
    {
        // Finalise slots before b.slot.
        s' := process_slots(s, b.slot);

        // Preconditions for process_block
        // assert s'.slot == forwardStateToSlot(nextSlot(s), b.slot).slot;
        // assert s'.slot == b.slot;
        // assert b.parent_root == hash_tree_root(s'.latest_block_header);
        // assert s'.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000  ;
        // assert |s'.eth1_data_votes| < EPOCHS_PER_ETH1_VOTING_PERIOD as int * SLOTS_PER_EPOCH as int;
        // assert |s'.validators| == |s'.balances|;
        // assert |s'.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int;
        // assert total_balances(s'.balances) + total_deposits(b.body.deposits) < 0x10000000000000000;
        // assert minimumActiveValidators(s');
        // assert isValidBeaconBlockBody(updateEth1Data(updateRandao(addBlockToState(s', b), b.body), b.body), b.body);
        
        //  Process block and compute the new state.
        s' := process_block(s', b);  

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
    method process_slots(s: BeaconState, slot: Slot) returns (s' : BeaconState)  
        requires s.slot as nat < slot as nat < 0x10000000000000000 as nat
        //  update in 0.12.0 (was <= before)
        requires |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)
        
        // The next one is a direct consequence of I1
        ensures s'.slot == slot
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures |s'.validators| == |s'.balances|
        ensures s' == forwardStateToSlot(nextSlot(s), slot)   //  I1
        ensures is_valid_state_epoch_attestations(s')

        //  Termination ranking function
        decreases slot - s.slot
    {
        //  Start from the current state and update it with processSlot.
        //  This is the first iteration of the loop in process_slots (Eth2-specs)
        var i : nat := s.slot as nat;
        s' := process_slot(s);
        if (s'.slot + 1) % SLOTS_PER_EPOCH  == 0 {
            assert |s'.validators| == |s'.balances|;
            assert is_valid_state_epoch_attestations(s');
            s' := process_epoch(s');
        } 
        assert i == s'.slot as nat;
        s':= s'.(slot := s'.slot + 1) ;

        i := i + 1;
        assert s'.slot as nat == i;
        assert(s' == nextSlot(s));
        //  s'.block header state_root should now be resolved
        assert(s'.latest_block_header.state_root != DEFAULT_BYTES32);
        //assert s' == forwardStateToSlot(nextSlot(s), s'.slot);
        assert s' == forwardStateToSlot(nextSlot(s), i as Slot);

        // //  Now fast forward state to `slot`
        while (i < slot as nat)  
            invariant i == s'.slot as nat
            invariant nextSlot(s).slot as nat <= i;
            invariant i <= slot as nat < 0x10000000000000000 as nat
            invariant s'.latest_block_header.state_root != DEFAULT_BYTES32
            invariant s'.eth1_deposit_index == s.eth1_deposit_index
            invariant |s'.validators| == |s'.balances|

            invariant is_valid_state_epoch_attestations(s')
            invariant s' == forwardStateToSlot(nextSlot(s), i as Slot);
            
            decreases slot as nat - i 
        {     
            var orig := s';
            assert orig == forwardStateToSlot(nextSlot(s), i as Slot);

            s' := process_slots_iteration(orig);
            calc == {
                s' == nextSlot(orig);
                {assert orig == forwardStateToSlot(nextSlot(s), i as Slot);}
                s' == nextSlot(forwardStateToSlot(nextSlot(s), i as Slot));
                {helperForwardStateToSlotLemma(nextSlot(s), i);}
                s' == forwardStateToSlot(nextSlot(s), (i+1) as Slot);
            }
            
            i := i + 1;
            assert s' == forwardStateToSlot(nextSlot(s), i as Slot);
            assert(s'.latest_block_header.state_root != DEFAULT_BYTES32);
        }
        assert s' == forwardStateToSlot(nextSlot(s), slot); 
    }

    /**
     *  Helper function for process_slots to implement one iternation of
     *  process_slot and, if at an epoch boundary, process_epoch.
     *  
     *  @param      s   A beacon state.   
     *  @returns        The state obtained after processing processing a
     *                  slot and then, if an epoch boundary, an epoch.
     */
    method process_slots_iteration(s: BeaconState) returns (s' : BeaconState)  
        requires s.slot as nat + 1 < 0x10000000000000000 as nat 
        //  update in 0.12.0 (was <= before)
        requires |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)

        ensures s'  == nextSlot(s)
    {
        s' := process_slot(s);
        //  Process epoch on the start slot of the next epoch
        if (s'.slot + 1) % SLOTS_PER_EPOCH  == 0 {
            assert |s'.validators| == |s'.balances|;
            assert is_valid_state_epoch_attestations(s');
            s' := process_epoch(s');
        }
        //  s'.slot is now processed: history updated and block header resolved
        //  The state's slot is processed and we can advance to the next slot.
        s' := s'.(slot := s'.slot + 1) ;
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
    method process_slot(s: BeaconState) returns (s' : BeaconState)
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        requires |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)

        ensures  s.latest_block_header.state_root == DEFAULT_BYTES32 ==>
            s' == resolveStateRoot(s).(slot := s.slot)
        ensures  s.latest_block_header.state_root != DEFAULT_BYTES32 ==>
            s' == advanceSlot(s).(slot := s.slot)
        ensures s.latest_block_header.parent_root == s'.latest_block_header.parent_root
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
        ensures s'.latest_block_header.state_root != DEFAULT_BYTES32
        ensures is_valid_state_epoch_attestations(s')
    {
        s' := s;

        //  Cache state root. Record the hash of the previous state in the history.
        var previous_state_root := hash_tree_root(s); 

        s' := s'.(state_roots 
                    := s'.state_roots[(s'.slot % SLOTS_PER_HISTORICAL_ROOT) as int := previous_state_root]);

        //  Cache latest block header state root
        if (s'.latest_block_header.state_root == DEFAULT_BYTES32) {
            s' := s'.(latest_block_header := s'.latest_block_header.(state_root := previous_state_root));
        }

        //  Cache block root
        var previous_block_root := hash_tree_root(s'.latest_block_header);

        //  Compute the final value of the new state.
        s' := s'.(block_roots 
                    := s'.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := previous_block_root]);
    }

    /**
     *  Verify that a block is valid.
     *  
     *  @param      s   A beacon state.   
     *  @param      b   A block header.
     *  @returns        The state obtained after processing `b`.
     */
     method process_block(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState) 
        requires b.slot == s.slot
        requires b.parent_root == hash_tree_root(s.latest_block_header)
        requires s.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000  
        requires |s.eth1_data_votes| < EPOCHS_PER_ETH1_VOTING_PERIOD as int * SLOTS_PER_EPOCH as int
        requires |s.validators| == |s.balances|
        requires |s.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        requires total_balances(s.balances) + total_deposits(b.body.deposits) < 0x10000000000000000
        //requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires minimumActiveValidators(s)
        requires isValidBeaconBlockBody(updateEth1Data(
                                            updateRandao(addBlockToState(s, b), 
                                                        b.body), 
                                            b.body),
                                        b.body)

        ensures s'.slot == b.slot
        ensures s'.latest_block_header 
                == BeaconBlockHeader(b.slot, b.proposer_index, b.parent_root, DEFAULT_BYTES32)
        ensures |s'.validators| == |s'.balances|
        ensures s' == updateBlock(s, b)
    {
        //  Start by creating a block header from the ther actual block.
        s' := process_block_header(s, b); 
        assert s' == addBlockToState(s, b);
        assert (s'.balances == s.balances);
        assert (s'.validators == s.validators);
        //assert s'.latest_block_header 
        //      == BeaconBlockHeader(b.slot, b.proposer_index, b.parent_root, DEFAULT_BYTES32);
        
        s' := process_randao(s', b.body);
        assert s' == updateRandao(addBlockToState(s, b), b.body);
        assert (s'.balances == s.balances);
        assert (s'.validators == s.validators);
        
        // assert |s'.validators| == |s'.balances|;
        // assert |s'.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int;
        // assert |s'.eth1_data_votes| < EPOCHS_PER_ETH1_VOTING_PERIOD as int * SLOTS_PER_EPOCH as int;
        // assert s'.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000 ;
        s' := process_eth1_data(s', b.body);
        assert (s'.balances == s.balances);
        assert (s'.validators == s.validators);
        assert |s'.validators| == |s'.balances|;
        assert s' == updateEth1Data(updateRandao(addBlockToState(s, b), b.body), b.body);

        assert minimumActiveValidators(s);
        assert isValidBeaconBlockBody(s', b.body);
        
        s' := process_operations(s', b.body);
        assert s' == updateOperations(updateEth1Data(updateRandao(addBlockToState(s, b), b.body), b.body), b.body);
        assert s' == updateBlock(s, b);
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
    method process_block_header(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState) 
        //  Verify that the slots match
        requires b.slot == s.slot  
        //  Verify that the parent matches
        requires b.parent_root == hash_tree_root(s.latest_block_header) 
        requires |s.validators| == |s.balances|
        requires |s.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        requires s.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000 
        requires minimumActiveValidators(s)

        ensures s' == addBlockToState(s, b)
        ensures s'.slot == b.slot
        ensures s'.latest_block_header == BeaconBlockHeader(b.slot, b.proposer_index, b.parent_root, DEFAULT_BYTES32)
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
        ensures minimumActiveValidators(s)
        //ensures |s'.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
    {
        s':= s.(
            latest_block_header := BeaconBlockHeader(
                b.slot,
                b.proposer_index,
                b.parent_root,
                DEFAULT_BYTES32
            )
        );
    }

    /**
     *  Update randao_mixes. 
     *
     *  @param  s   A beacon state.
     *  @param  b   A block.
     *  @returns    The state obtained updating the randao mixes entry at position
     *              epoch % EPOCHS_PER_HISTORICAL_VECTOR.
     */
    method process_randao(s: BeaconState, b: BeaconBlockBody) returns (s' : BeaconState) 
        requires |s.validators| == |s.balances|
        requires minimumActiveValidators(s)

        ensures |s'.validators| == |s'.balances|
        ensures s' == s.(randao_mixes := s'.randao_mixes)
        ensures s'.latest_block_header == s.latest_block_header
        ensures s' == updateRandao(s,b);
        ensures minimumActiveValidators(s')
    {
        var epoch := get_current_epoch(s);

        // Verify RANDAO reveal not implemented
        //var proposer := s.validators[get_beacon_proposer_index(s)];
        // signing_root = compute_signing_root(epoch, get_domain(state, DOMAIN_RANDAO))
        // assert bls.Verify(proposer.pubkey, signing_root, body.randao_reveal)

        // # Mix in RANDAO reveal (use simplified mix value)
        var mix := DEFAULT_BYTES32; //var mix := xor(get_randao_mix(s, epoch), hash(b.randao_reveal));
        s' := s.(randao_mixes := s.randao_mixes[(epoch % EPOCHS_PER_HISTORICAL_VECTOR) as nat := mix]);
    }
    

    /**
     *  Update eth1 data. 
     *
     *  @param  s   A beacon state.
     *  @param  b   A block.
     *  @returns    The state obtained by appending the block eth1 data to eth1_data_votes and
     *              also (if state.eth1_data_votes.count(body.eth1_data) * 2 > 
     *              EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH) by setting eth1_data to
     *              the block eth1 data.
     */
    method process_eth1_data(s: BeaconState, b: BeaconBlockBody) returns (s' : BeaconState) 
        requires |s.validators| == |s.balances|
        requires |s.validators| + |b.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        requires |s.eth1_data_votes| < EPOCHS_PER_ETH1_VOTING_PERIOD as int * SLOTS_PER_EPOCH as int
        requires s.eth1_deposit_index as int + |b.deposits| < 0x10000000000000000 
        requires minimumActiveValidators(s)
        
        ensures s' == updateEth1Data(s,b)
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
        ensures s'.latest_block_header == s.latest_block_header
        //ensures |s'.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        ensures minimumActiveValidators(s')
    {
        //state.eth1_data_votes.append(body.eth1_data)
        s' := s.(eth1_data_votes := s.eth1_data_votes + [b.eth1_data]);

        //if state.eth1_data_votes.count(body.eth1_data) * 2 > EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH:
        if count_eth1_data_votes(s'.eth1_data_votes, b.eth1_data) * 2 > (EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH) as int{
            //state.eth1_data = body.eth1_data
            s' := s'.(eth1_data := b.eth1_data);
        }
    }   
    
}