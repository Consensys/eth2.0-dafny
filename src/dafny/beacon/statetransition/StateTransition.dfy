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

//  @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /trace /noCheating:1

include "../../utils/NativeTypes.dfy"
include "../../utils/NonNativeTypes.dfy"
include "../../utils/Eth2Types.dfy"
include "../forkchoice/ForkChoiceTypes.dfy"
include "../../utils/Helpers.dfy"
include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../validators/Validators.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../Helpers.dfy"
include "StateTransition.s.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "EpochProcessing.dfy"
include "ProcessOperations.dfy"
include "ProcessOperations.s.dfy"
include "../helpers/Math.dfy"

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
    import opened AttestationsHelpers
    import opened EpochProcessing
    import opened ProcessOperations
    import opened ProcessOperationsSpec
    import opened Math

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
        && |s.eth1_data_votes| < EPOCHS_PER_ETH1_VOTING_PERIOD as int * SLOTS_PER_EPOCH as int
        // && b.parent_root == 
        //     hash_tree_root(
        //         forwardStateToSlot(nextSlot(s), 
        //         b.slot
        //     ).latest_block_header) 
        // //  Check that the block provides the correct hash for the state.
        // &&  b.state_root == hash_tree_root(
        //         updateDeposits(
        //             updateEth1Data(
        //                 addBlockToState(
        //                     forwardStateToSlot(nextSlot(s), b.slot), 
        //                     b
        //                 ),
        //                 b.body),
        //             b.body.deposits
        //         )
        //     )
    }

    /**
     *  Compute the state obtained after adding a block.
     *  
     *  @param      s   A beacon state.
     *  @param      b   A block.
     *  @returns        The state obtained after adding `b` to the current state.
     *                  
     */
     method state_transition(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState)
        //  make sure the last state was one right after addition of new block
        requires isValidBlock(s, b)

        requires s.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000 
        
        // i.e. valid state to proceed
        requires |s.validators| == |s.balances| 

        // Note: An alternative is to use a propoerty lemma that ensures the following three preconditions are always true
        //       This property lemma should be proved by linking to the process of creating PendingAttestations
        requires forall a :: a in s.previous_epoch_attestations ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6 
        requires forall a :: a in s.previous_epoch_attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in s.previous_epoch_attestations ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 

        requires minimumActiveValidators(s) //requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires isValidBeaconBlockBody(forwardStateToSlot(nextSlot(s), b.slot), b.body)
        
        // /** The next state latest_block_header is same as b except for state_root that is 0. */
        // ensures s'.latest_block_header == BeaconBlockHeader(b.slot, b.proposer_index, b.parent_root, DEFAULT_BYTES32)
        // /** s' slot is now adjusted to the slot of b. */
        // ensures s'.slot == b.slot
        // /** s' parent_root is the hash of the state obtained by resolving/forwarding s to
        //     the slot of b.  */
        // ensures s'.latest_block_header.parent_root  == 
        //     hash_tree_root(
        //         forwardStateToSlot(nextSlot(s), b.slot)
        //         .latest_block_header
        //     )
        // ensures s'.eth1_deposit_index as int == s.eth1_deposit_index as int + |b.body.deposits|
        // ensures s'.validators == updateDeposits(updateEth1Data(addBlockToState(forwardStateToSlot(nextSlot(s), b.slot),b), b.body),b.body.deposits).validators
        // ensures s'.balances == updateDeposits(updateEth1Data(addBlockToState(forwardStateToSlot(nextSlot(s), b.slot),b), b.body),b.body.deposits).balances
        ensures |s'.validators| == |s'.balances|
        //ensures s' == updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b)
    {
        //  finalise slots before b.slot.
        var s1 := process_slots(s, b.slot);

        assert (s1.slot == forwardStateToSlot(nextSlot(s), b.slot).slot );
        assert (s1.slot == b.slot);
        //assert (s1.balances == s.balances);

        //  Process block and compute the new state.
        assume |get_active_validator_indices(s1.validators, get_current_epoch(s1))| > 0;
        assert |s1.validators| == |s1.balances|;
        assume b.parent_root == hash_tree_root(s1.latest_block_header);
        assert s1.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000 ; 
        assume |s1.eth1_data_votes| < EPOCHS_PER_ETH1_VOTING_PERIOD as int * SLOTS_PER_EPOCH as int;
        assume |s1.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int;
        assume total_balances(s1.balances) + total_deposits(b.body.deposits) < 0x10000000000000000;
        assert |get_active_validator_indices(s1.validators, get_current_epoch(s1))| > 0;

        assert isValidBeaconBlockBody(s1, b.body);

        s' := process_block(s1, b);  
        assert (s'.slot == b.slot);  
        assert s' == updateBlock(forwardStateToSlot(nextSlot(s), b.slot), b);

        // // Verify state root (from eth2.0 specs)
        // // A proof that this function is correct establishes that this assert statement 
        // // is never violated (i.e. when isValidBlock() is true.)
        // // In the Eth2.0 specs this check is conditional but enabled by default.
        // assert (b.state_root == hash_tree_root(s'));
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
    method {:timeLimitMultiplier 10} process_slots(s: BeaconState, slot: Slot) returns (s' : BeaconState)
        requires s.slot < slot  //  update in 0.12.0 (was <= before)
        requires |s.validators| == |s.balances|

        requires forall a :: a in s.previous_epoch_attestations ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6 
        requires forall a :: a in s.previous_epoch_attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in s.previous_epoch_attestations ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
       
        
        ensures s' == forwardStateToSlot(nextSlot(s), slot)   //  I1
        // // The next one is a direct consequence of I1
        ensures s'.slot == slot
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        // ensures s'.validators == s.validators
        // ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|

        //  Termination ranking function
        decreases slot - s.slot
    {
        //  Start from the current state and update it with processSlot.
        //  This is the first iteration of the loop in process_slots (Eth2-specs)
        s' := process_slot(s);
        if (s'.slot + 1) % SLOTS_PER_EPOCH  == 0 {
            assert |s'.validators| == |s'.balances|;
            assert forall a :: a in s'.previous_epoch_attestations ==> a.data.index < get_committee_count_per_slot(s', compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6 ;
            assert forall a :: a in s'.previous_epoch_attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s'.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat ;
            assert forall a :: a in s'.previous_epoch_attestations ==> 0 < |get_beacon_committee(s', a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat ;
       
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
            //invariant s'.validators == s.validators
            //invariant s'.balances == s.balances
            invariant |s'.validators| == |s'.balances|
            decreases slot - s'.slot 
        {     
            s':= process_slot(s');
            //  Process epoch on the start slot of the next epoch
            if (s'.slot + 1) % SLOTS_PER_EPOCH  == 0 {
                var k := s'; 
                PreviousEpochAttestationsProperties(s');
                s' := process_epoch(s');
            }
            //  s'.slot is now processed: history updated and block header resolved
            //  The state's slot is processed and we can advance to the next slot.
            s':= s'.(slot := s'.slot + 1) ;
            //assert(s' == nextSlot(s));
            //  s'.block header state_root should now be resolved
            assert(s'.latest_block_header.state_root != DEFAULT_BYTES32);
        }
        assert s' == forwardStateToSlot(nextSlot(s), slot); 
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
    method process_slot(s: BeaconState) returns (s' : BeaconState)
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
     method process_block(s: BeaconState, b: BeaconBlock) returns (s' : BeaconState) 
        requires b.slot == s.slot
        requires b.parent_root == hash_tree_root(s.latest_block_header)
        requires s.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000  
        requires |s.eth1_data_votes| < EPOCHS_PER_ETH1_VOTING_PERIOD as int * SLOTS_PER_EPOCH as int
        requires |s.validators| == |s.balances|
        requires |s.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        requires total_balances(s.balances) + total_deposits(b.body.deposits) < 0x10000000000000000
        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires isValidBeaconBlockBody(s, b.body)

        ensures s'.slot == b.slot
        ensures s'.latest_block_header == BeaconBlockHeader(b.slot, b.proposer_index, b.parent_root, DEFAULT_BYTES32)
        ensures |s'.validators| == |s'.balances|
        ensures s' == updateBlock(s, b)
        //ensures s' == updateOperations(updateEth1Data(updateRandao(addBlockToState(s, b), b.body), b.body), b.body)
    {
        //  Start by creating a block header from the ther actual block.
        s' := process_block_header(s, b); 
        assert s' == addBlockToState(s, b);
        assert (s'.balances == s.balances);
        assert (s'.validators == s.validators);
        //assert s'.latest_block_header == BeaconBlockHeader(b.slot, b.proposer_index, b.parent_root, DEFAULT_BYTES32);
        
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

        assert |get_active_validator_indices(s'.validators, get_current_epoch(s'))| > 0;
        // TODO: change to assert or create property lemma to ensure the following holds
        assume isValidBeaconBlockBody(s', b.body);
        
        s' := process_operations(s', b.body);
        assert s' == updateOperations(updateEth1Data(updateRandao(addBlockToState(s, b), b.body), b.body), b.body);
        assert s' == updateBlock(s, b);
    }

    /** */
    function updateBlock(s: BeaconState, b: BeaconBlock): BeaconState
        requires b.slot == s.slot
        requires b.parent_root == hash_tree_root(s.latest_block_header)
        requires s.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000  
        requires |s.eth1_data_votes| < EPOCHS_PER_ETH1_VOTING_PERIOD as int * SLOTS_PER_EPOCH as int
        requires |s.validators| == |s.balances|
        requires |s.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        requires total_balances(s.balances) + total_deposits(b.body.deposits) < 0x10000000000000000
        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires isValidBeaconBlockBody(s, b.body)

        // ensures updateBlock(s,b).slot == b.slot
        // ensures updateBlock(s,b).latest_block_header == BeaconBlockHeader(b.slot, b.proposer_index, b.parent_root, DEFAULT_BYTES32)
        // ensures |updateBlock(s,b).validators| == |updateBlock(s,b).balances|
        //ensures updateBlock(s,b) == updateOperations(updateEth1Data(updateRandao(addBlockToState(s, b), b.body), b.body), b.body)
        
    {
        //  Start by creating a block header from the ther actual block.
        var s1 := addBlockToState(s, b); 
        assert s1 == addBlockToState(s, b);
        assert (s1.balances == s.balances);
        assert (s1.validators == s.validators);
        
        var s2 := updateRandao(s1, b.body);
        assert s2 == updateRandao(addBlockToState(s, b), b.body);
        assert (s2.balances == s.balances);
        assert (s2.validators == s.validators);
        
        var s3 := updateEth1Data(s2, b.body);
        assert (s3.balances == s.balances);
        assert (s3.validators == s.validators);
        assert |s3.validators| == |s3.balances|;
        assert s3 == updateEth1Data(updateRandao(addBlockToState(s, b), b.body), b.body);

        assert |get_active_validator_indices(s3.validators, get_current_epoch(s3))| > 0;
        assume isValidBeaconBlockBody(s3, b.body);
        
        var s4 := updateOperations(s3, b.body);
        assert s4 == updateOperations(updateEth1Data(updateRandao(addBlockToState(s, b), b.body), b.body), b.body);
        s4
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

        ensures s' == addBlockToState(s, b)
        ensures s'.slot == b.slot
        ensures s'.latest_block_header == BeaconBlockHeader(b.slot, b.proposer_index, b.parent_root, DEFAULT_BYTES32)
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
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

    /** */
    method process_randao(s: BeaconState, b: BeaconBlockBody) returns (s' : BeaconState) 
        requires |s.validators| == |s.balances|
        ensures |s'.validators| == |s'.balances|
        ensures s' == s.(randao_mixes := s'.randao_mixes)
        ensures s'.latest_block_header == s.latest_block_header
        ensures s' == updateRandao(s,b);
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
     *  Check whether a block is valid and prepare and initialise new state
     *  with a corresponding block header. 
     *
     *  @param  s   A beacon state.
     *  @param  b   A block.
     *  @returns    The state obtained processing the block.
     *
     *  @note   Matches eth2.0 specs except proposer slashing verification.
     */
    method process_eth1_data(s: BeaconState, b: BeaconBlockBody) returns (s' : BeaconState) 
        requires |s.validators| == |s.balances|
        requires |s.validators| + |b.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        requires |s.eth1_data_votes| < EPOCHS_PER_ETH1_VOTING_PERIOD as int * SLOTS_PER_EPOCH as int
        requires s.eth1_deposit_index as int + |b.deposits| < 0x10000000000000000 

        ensures s' == updateEth1Data(s,b)
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
        ensures s'.latest_block_header == s.latest_block_header
        //ensures |s'.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
    {
        //state.eth1_data_votes.append(body.eth1_data)
        s' := s.(eth1_data_votes := s.eth1_data_votes + [b.eth1_data]);

        //if state.eth1_data_votes.count(body.eth1_data) * 2 > EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH:
        if count_eth1_data_votes(s'.eth1_data_votes, b.eth1_data) * 2 > (EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH) as int{
            //state.eth1_data = body.eth1_data
            s' := s'.(eth1_data := b.eth1_data);
        }
            

    }
    

    // // /**
    // //  *  Process the operations defined by a block body.
    // //  *  
    // //  *  @param  s   A state.
    // //  *  @param  bb  A block body.
    // //  *  @returns    The state obtained after applying the operations of `bb` to `s`.
    // //  */
    // // method process_operations(s: BeaconState, bb: BeaconBlockBody)  returns (s' : BeaconState) 
    // //     requires s.eth1_deposit_index as int +  |bb.deposits| < 0x10000000000000000 
    // //     requires |s.validators| + |bb.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
    // //     requires |s.validators| == |s.balances|
    // //     requires total_balances(s.balances) + total_deposits(bb.deposits) < 0x10000000000000000 
        
    // //     //ensures |s'.validators| == |s'.balances|
    // //     ensures s' == updateDeposits(s, bb.deposits)
    // //     ensures s'.slot == s.slot
    // //     ensures s'.latest_block_header == s.latest_block_header
    // //     //ensures s'.validators == s.validators + get_new_validators(s, [], bb.deposits)
    // //     //ensures false
    // // {
    // //     //  process deposits in the beacon block body.
    // //     s':= s;

    // //     var i := 0;
    // //     assert s' == updateDeposits(s, bb.deposits[..i]);
    // //     assert total_balances(s'.balances) + total_deposits(bb.deposits[..i]) < 0x10000000000000000 ;
        
    // //     while i < |bb.deposits| 
    // //         decreases |bb.deposits| - i

    // //         invariant 0 <= i <= |bb.deposits|
    // //         invariant s'.eth1_deposit_index == s.eth1_deposit_index + i as uint64
            
    // //         invariant total_balances(s.balances) + total_deposits(bb.deposits[..i]) < 0x10000000000000000 
    // //         //invariant s'.validators == updateDeposits(s, bb.deposits[..i]).validators
    // //         //invariant s'.balances == updateDeposits(s, bb.deposits[..i]).balances
            
    // //         //invariant total_balances(updateDeposits(s,bb.deposits[..i]).balances) == total_balances(s.balances) + total_deposits(bb.deposits[..i]) < 0x10000000000000000
            
    // //         //invariant s'.slot == s.slot 
    // //         //invariant s'.latest_block_header == s.latest_block_header
    // //         //invariant s'.block_roots == s.block_roots
    // //         //invariant s'.state_roots == s.state_roots

    // //         //invariant |s'.validators| == |s'.balances| 
    // //         //invariant |s'.validators| <= |s.validators| + i
    // //         //invariant |s.validators| + i <= VALIDATOR_REGISTRY_LIMIT as int
    // //         invariant s' == updateDeposits(s, bb.deposits[..i])
    // //         invariant s'.slot == s.slot
    // //         invariant s'.latest_block_header == s.latest_block_header
    // //         //invariant |bb.deposits[..i]| == i

    // //         //invariant |s'.validators| <= |updateDeposits(s,bb.deposits[..i]).validators| <= |s'.validators| + i 
    // //     {
    // //         assert bb.deposits[..i+1] == bb.deposits[..i] + [bb.deposits[i]];

    // //         s':= process_attestation(s', bb.attestations);

    // //         //assert total_balances(updateDeposits(s, bb.deposits[..i]).balances) + bb.deposits[i].data.amount as int == total_balances(s.balances) + total_deposits(bb.deposits[..i]) + bb.deposits[i].data.amount as int;
    // //         //assert total_deposits(bb.deposits[..i]) + bb.deposits[i].data.amount as int == total_deposits(bb.deposits[..i+1]);
    // //         //assert total_balances(updateDeposits(s, bb.deposits[..i]).balances) + bb.deposits[i].data.amount as int == total_balances(s.balances) + total_deposits(bb.deposits[..i+1]);
    // //         //assert i + 1  <= |bb.deposits|;
    // //         subsetDepositSumProp(bb.deposits, i+1);
    // //         //assert total_deposits(bb.deposits[..i+1]) <= total_deposits(bb.deposits);
    // //         //assert total_balances(updateDeposits(s, bb.deposits[..i]).balances) + bb.deposits[i].data.amount as int < 0x10000000000000000;

    // //         //assert updateDeposit(updateDeposits(s, bb.deposits[..i]),bb.deposits[i]) == updateDeposits(s, bb.deposits[..i+1]);
            
    // //         s':= process_deposit(s', bb.deposits[i]); 
    // //         i := i+1;

    // //     }
    // //     assert bb.deposits[..i] == bb.deposits;

    // // }

    // /**
    //  *  Process a deposit operation.
    //  *
    //  *  @param  s   A state.
    //  *  @param  d   A deposit.  
    //  *  @returns    The state obtained depositing of `d` to `s`.
    //  *  @todo       Finish implementation of this function.
    //  */
    // method process_deposit(s: BeaconState, d : Deposit)  returns (s' : BeaconState)  
    //     requires |s.validators| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
    //     requires s.eth1_deposit_index as int + 1 < 0x10000000000000000 
    //     requires |s.validators| == |s.balances|
    //     requires total_balances(s.balances) + d.data.amount as int < 0x10000000000000000

    //     ensures s'.eth1_deposit_index == s.eth1_deposit_index + 1
    //     //ensures d.data.pubkey !in seqKeysInValidators(s.validators) ==> s'.validators == s.validators + [get_validator_from_deposit(d)]
    //     //ensures d.data.pubkey in seqKeysInValidators(s.validators) ==> s'.validators == s.validators 
    //     ensures s' == updateDeposit(s,d)

    //     //ensures |s'.validators| == |s'.balances|        // maybe include in property lemmas
    //     //ensures |s.validators| <= |s'.validators| <= |s.validators| + 1 // maybe include in property lemmas
    //     //ensures |s.balances| <= |s'.balances| <= |s.balances| + 1 // maybe include in property lemmas
    //     //ensures |s'.validators| <= VALIDATOR_REGISTRY_LIMIT
        
    // {
    //     // note that it is assumed that all new validator deposits are verified
    //     // ie the step # Verify the deposit signature (proof of possession) which is not checked by the deposit contract
    //     // is not performed
    //     var pk := seqKeysInValidators(s.validators);
    //     s' := s.(
    //             eth1_deposit_index := (s.eth1_deposit_index as int + 1) as uint64,
    //             validators := if d.data.pubkey in pk then 
    //                                 s.validators // unchanged validator members
    //                             else 
    //                                 (s.validators + [get_validator_from_deposit(d)]),
    //             balances := if d.data.pubkey in pk then 
    //                                 individualBalanceBoundMaintained(s.balances,d);
    //                                 increase_balance(s,get_validator_index(pk, d.data.pubkey),d.data.amount).balances
    //                             else 
    //                                 s.balances + [d.data.amount]
    //     );
    // }

    // /**
    //  *  
    //  *  @note       This method uses PendingAttestations instead of attestations in the 
    //  *              input parameter `xa`.The difference is in the signature field which 
    //  *              we omit in this foirst-cut.
    //  */
    //  method process_attestations(s: BeaconState, xa: ListOfAttestations)  returns (s' : BeaconState)
    //     // requires 
    //     ensures s' == s  
    //  {
    //      return s;
    //  }
     

    // predicate isValidAttestationInState(s: BeaconState, a: PendingAttestation)
    // {
    //     && get_previous_epoch(s) <= a.data.target.epoch <= get_current_epoch(s)
    //     && a.data.target.epoch == compute_epoch_at_slot(a.data.slot)
    //     //  attestation is not too recent
    //     && a.data.slot as nat + MIN_ATTESTATION_INCLUSION_DELAY as nat <= s.slot as nat  
    //     //  attestation is not old
    //     && a.data.slot as nat + SLOTS_PER_EPOCH as nat >= s.slot as nat 
    //     //  if attestation target is current epoch, then the source must
    //     //  be the current justified checkpoint
    //     && (a.data.target.epoch == get_current_epoch(s) ==> 
    //         a.data.source == s.current_justified_checkpoint)
    //     //  if attestation target is previous epoch, then the source must
    //     //  be the the previous justified checkpoint
    //     && (a.data.target.epoch == get_previous_epoch(s) ==> 
    //         a.data.source == s.previous_justified_checkpoint)
        
    // }
    
    
}