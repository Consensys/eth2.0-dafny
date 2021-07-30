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

//  @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /trace /vcsCores:12   /verifySeparately /noCheating:0

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
include "EpochProcessing.s.dfy"
include "ProcessOperations.s.dfy"
include "../gasper/GasperJustification.dfy"

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
    import opened EpochProcessingSpec
    import opened ProcessOperationsSpec
    import opened GasperJustification


    /**
     *  Whether a block is valid in a given state.
     *
     *  @param  s   A beacon state.
     *  @param  b   A block.
     *
     *  @returns    true iff `b` can be successfully added to the state `s`.
     */
    predicate isValidBlock(s : BeaconState, b : BeaconBlock, store: Store) 
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        requires foo606(s, store)

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
        && b.parent_root == 
            hash_tree_root(
                forwardStateToSlot(nextSlot(s, store), 
                b.slot,
                store
            ).latest_block_header) 
        //  Check that the block provides the correct hash for the state.
        &&  b.state_root == hash_tree_root(
                updateDeposits(
                    updateEth1Data(
                        addBlockToState(
                            forwardStateToSlot(nextSlot(s, store), b.slot, store), 
                            b
                        ),
                        b.body),
                    b.body.deposits
                )
            )
        // &&  // assume(s.eth1_deposit_index as int +  1 < 0x10000000000000000);
        //     b.state_root == hash_tree_root(
        //         updateDeposits(
        //             updateEth1Data(
        //                 addBlockToState(
        //                     forwardStateToSlot(nextSlot(s, store), b.slot, store),
        //                     // nextSlot(s, store), 
        //                     b
        //                 ),
        //                 b.body
        //             ),
        //             b.body.deposits
        //         )
        //     )
    }

    /**
     *  THe validity of a block does solely depends on the reference state.
     */
    // lemma isValidBlockIsNotStoreDependent(s: BeaconState, b : BeaconBlock, store1: Store, store2 : Store)
    //     /** Store is well-formed. */
    //     requires isClosedUnderParent(store1)
    //     requires isClosedUnderParent(store2)
    //     /**  The decreasing property guarantees that this function terminates. */
    //     requires isSlotDecreasing(store1)
    //     requires isSlotDecreasing(store2)

    //     requires foo606(s, store1)
    //     requires foo606(s, store2)

    //     requires isValidBlock(s, b, store1)
    //     ensures isValidBlock(s, b, store2)
    // {
    //     nextSlotIsNotStoreDependent(s, store1, store2);
    //     assert(nextSlot(s, store1) == nextSlot(s, store2));
    //     forwardStateIsNotStoreDependent(nextSlot(s, store1), b.slot, store1, store2);
    // }

    /**
     *  Compute the state obtained after adding a block.
     *  
     *  @param      s   A beacon state.
     *  @param      b   A block.
     *  @returns        The state obtained after adding `b` to the current state.
     *                  
     */
     method stateTransition(s: BeaconState, b: BeaconBlock, store: Store) returns (s' : BeaconState)
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        requires foo606(s, store)
        //  make sure the last state was one right after addition of new block
        requires isValidBlock(s, b, store)

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
                forwardStateToSlot(nextSlot(s, store), b.slot, store)
                .latest_block_header
            )
        ensures s'.eth1_deposit_index as int == s.eth1_deposit_index as int + |b.body.deposits|
        ensures s'.validators == updateDeposits(updateEth1Data(addBlockToState(forwardStateToSlot(nextSlot(s, store), b.slot, store),b), b.body),b.body.deposits).validators
        ensures s'.balances == updateDeposits(updateEth1Data(addBlockToState(forwardStateToSlot(nextSlot(s, store), b.slot, store),b), b.body),b.body.deposits).balances
        ensures |s'.validators| == |s'.balances|

    {
        //  finalise slots before b.slot.
        var s1 := processSlots(s, b.slot, store);

        assume forwardStateToSlot.requires(nextSlot(s, store), b.slot, store);

        assert (s1.slot == forwardStateToSlot(nextSlot(s,store), b.slot, store).slot );
        assert (s1.slot == b.slot);
        assert (s1.balances == s.balances);

        // assume b.slot == s1.slot;
        // assume b.parent_root == hash_tree_root(s1.latest_block_header);
        // assume s1.eth1_deposit_index as int + |b.body.deposits| < 0x10000000000000000  ;
        // assume |s1.eth1_data_votes| < EPOCHS_PER_ETH1_VOTING_PERIOD as int * SLOTS_PER_EPOCH as int;
        // assume |s1.validators| == |s1.balances|;
        // assume |s1.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int;
        // assume total_balances(s1.balances) + total_deposits(b.body.deposits) < 0x10000000000000000;

        // assume processBlock.requires(s1, b);
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
    method {:timeLimitMultiplier 15} processSlots(s: BeaconState, slot: Slot, store: Store) returns (s' : BeaconState)
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        // requires foo606(s, store)

        requires s.slot < slot  //  update in 0.12.0 (was <= before)
        requires |s.validators| == |s.balances|
        
        // requires validCurrentAttestations(updateJustificationPrevEpoch(s, store), store)

        ensures  foo606(s, store)
        ensures forwardStateToSlot.requires(nextSlot(s, store), slot, store)
        ensures s' == forwardStateToSlot(nextSlot(s,store), slot, store)   //  I1
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
        assume blockRootsValidWeak(s, store);
        s' := processSlot(s, store);
        // assert(s'.slot == s.slot);
        // assert blockRootsValidWeak(s'.(slot := s.slot + 1), store);
        // assert s' == resolveStateRoot(s, store).(slot := s.slot);

        // ensures blockRootsValidWeak(s'.(slot := s.slot + 1), store)
        if (s'.slot + 1) % SLOTS_PER_EPOCH  == 0 {
            assume foo606(s', store);
            assume validCurrentAttestations(updateJustificationPrevEpoch(s', store), store);

            s' := process_epoch(s', store);
        } 
        s':= s'.(slot := s'.slot + 1) ;
        // assume foo606(s', store);
        // assume s' == forwardStateToSlot(nextSlot(s, store), s'.slot, store);

        //  s'.block header state_root should now be resolved
        assert(s'.latest_block_header.state_root != DEFAULT_BYTES32);

        //  Now fast forward state to `slot`
        while (s'.slot < slot)  
            invariant s'.slot <= slot
            invariant s'.latest_block_header.state_root != DEFAULT_BYTES32
            // invariant foo606(s', store)
            // invariant s' == forwardStateToSlot(nextSlot(s, store), s'.slot, store) 
            invariant s'.eth1_deposit_index == s.eth1_deposit_index
            invariant s'.validators == s.validators
            invariant s'.balances == s.balances
            invariant |s'.validators| == |s'.balances|
            decreases slot - s'.slot 
        {     
            assume blockRootsValidWeak(s', store);
            s':= processSlot(s', store);
            // //  Process epoch on the start slot of the next epoch
            if (s'.slot + 1) % SLOTS_PER_EPOCH  == 0 {
                assume foo606(s', store);
                // assume updateJustificationPrevEpoch.requires(s', store);
                assume validCurrentAttestations(updateJustificationPrevEpoch(s', store), store);
                s' := process_epoch(s', store);
            }
            //  s'.slot is now processed: history updated and block header resolved
            //  The state's slot is processed and we can advance to the next slot.
            s':= s'.(slot := s'.slot + 1) ;
        }
        assume foo606(s, store);
        // assume 
        assume forwardStateToSlot.requires(nextSlot(s, store), slot, store);
        assume s' == forwardStateToSlot(nextSlot(s, store), slot, store);
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
    method processSlot(s: BeaconState, store: Store) returns (s' : BeaconState)
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        requires blockRootsValidWeak(s, store)

        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        requires |s.validators| == |s.balances|

        ensures  s.latest_block_header.state_root == DEFAULT_BYTES32 ==>
            s' == resolveStateRoot(s,store).(slot := s.slot)
        ensures  s.latest_block_header.state_root != DEFAULT_BYTES32 ==>
            s' == advanceSlot(s).(slot := s.slot)
        ensures s.latest_block_header.parent_root == s'.latest_block_header.parent_root
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|

        ensures s' == resolveStateRoot(s,store).(slot := s.slot)
        ensures blockRootsValidWeak(s'.(slot := s.slot + 1), store)
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
        requires |s.eth1_data_votes| < EPOCHS_PER_ETH1_VOTING_PERIOD as int * SLOTS_PER_EPOCH as int
        requires |s.validators| == |s.balances|
        requires |s.validators| + |b.body.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        requires total_balances(s.balances) + total_deposits(b.body.deposits) < 0x10000000000000000

        ensures s' == updateDeposits(updateEth1Data(addBlockToState(s, b), b.body), b.body.deposits)
        ensures s'.slot == b.slot
        ensures s'.latest_block_header == BeaconBlockHeader(b.slot, b.parent_root, DEFAULT_BYTES32)
        ensures |s'.validators| == |s'.balances|
    {
        //  Start by creating a block header from the ther actual block.
        s' := processBlockHeader(s, b); 
        assert (s'.balances == s.balances);
        
        //  process_randao(s, b.body)
        s' := process_eth1_data(s', b.body);
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

            s':= process_attestations(s', bb.attestations);

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

    /**
     *  
     *  @note       This method uses PendingAttestations instead of attestations in the 
     *              input parameter `xa`.The difference is in the signature field which 
     *              we omit in this foirst-cut.
     */
    method process_attestations(s: BeaconState, xa: ListOfAttestations)  returns (s' : BeaconState)
        // requires 
        ensures s' == s  
    {
        return s;
    }
     
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

    /**
     *  Process attestation section of a block.
     *  @param  s   A beacon state.
     *  @param  a   An attestation.
     *  @returns    ?? s new state
     *
     *  Example.
     *  epoch   0            1                  k                 k + 1       
     *          |............|....         .....|.................|.....................
     *  state                                                      s
     *  slot    0          12  .....                               s.slot 
     *                                            <-SLOTS_PER_EPOCH->
     *  slot         s.slot - SLOTS_PER_EPOCH = x1                x2 = s.slot - 1
     *  slot(a)                                   *****************     
     *                          =======a======>tgt1
     *                                            =======a======>tgt2
     *     
     *  
     *  epoch(s) = k + 1, and previous epoch is k.
     *  source and target are checkpoints.
     *  Target must have an epoch which is k (tgt1, case1) or k + 1 (tgt2, case2).
     *  a.data.slot (slot(a))is the slot in which ther validator makes the attestation.
     *  x1 <= slot(a) <= x2.
     *  Two cases arise: 
     *      1. compute_epoch_at_slot(a.data.slot) is previous_epoch k 
     *          in this case the target's epoch must be  previous-epoch k
     *      2. compute_epoch_at_slot(a.data.slot) is current_epoch k + 1 
     *          in this case the target's epoch must be  current-epoch k + 1
     *
     *  MIN_ATTESTATION_INCLUSION_DELAY is 1.
     *
     *  Question: what is the invariant for the attestations in a state?
     *  @note   In the actual eth2.0 specs, the input is an Attestation. Here we
     *          use a PendingAttestation.
     */
    method process_attestation(s: BeaconState, a: PendingAttestation) returns (s' : BeaconState)
        // requires forall a :: a in s.current_epoch_attestations ==> 
        requires attestationIsWellFormed(s, a)
        requires |s.current_epoch_attestations| < MAX_ATTESTATIONS * SLOTS_PER_EPOCH as int 
        requires |s.previous_epoch_attestations| < MAX_ATTESTATIONS * SLOTS_PER_EPOCH as int 
        // ensures 

    {
        // data = attestation.data
        assert get_previous_epoch(s) <= a.data.target.epoch <=  get_current_epoch(s);
        assert a.data.target.epoch == compute_epoch_at_slot(a.data.slot);
        assert a.data.slot as nat + MIN_ATTESTATION_INCLUSION_DELAY as nat <= s.slot as nat <= a.data.slot as nat + SLOTS_PER_EPOCH as nat;
        // assert data.index < get_committee_count_per_slot(state, data.target.epoch)

        // committee = get_beacon_committee(state, data.slot, data.index)
        // assert len(attestation.aggregation_bits) == len(committee)

        // pending_attestation = PendingAttestation(
        //     data=data,
        //     aggregation_bits=attestation.aggregation_bits,
        //     inclusion_delay=state.slot - data.slot,
        //     proposer_index=get_beacon_proposer_index(state),
        // )

        if a.data.target.epoch == get_current_epoch(s) {
            //  Add a to current attestations
            assert a.data.source == s.current_justified_checkpoint;
            s' := s.(
                current_epoch_attestations := s.current_epoch_attestations + [a]
            );
            // s.current_epoch_attestations.append(pending_attestation)
        }
        else {
            assert a.data.source == s.previous_justified_checkpoint;
            s' := s.(
                previous_epoch_attestations := s.previous_epoch_attestations + [a]
            );
        }
            // s.previous_epoch_attestations.append(pending_attestation)
            
        // # Verify signature
        // assert is_valid_indexed_attestation(state, get_indexed_attestation(state, attestation))
        // s'
    }

    /**
     *  Whether an attestation is acceptable.
     *
     *  @todo   Fix that definition and align it with validPrevAttestations and
     *  validCurrentAttestations. 
     */
    predicate attestationIsWellFormed(s: BeaconState, a: PendingAttestation)
    {
        && get_previous_epoch(s) <= a.data.target.epoch <= get_current_epoch(s)  
        /** Epoch of target matches epoch of the slot the attestation is made. */
        && a.data.target.epoch == compute_epoch_at_slot(a.data.slot)
        /** Attestation is not too old and not too recent. */
        && a.data.slot as nat + MIN_ATTESTATION_INCLUSION_DELAY as nat <= s.slot as nat <= a.data.slot as nat + SLOTS_PER_EPOCH as nat
        && if a.data.target.epoch == get_current_epoch(s) then  
            a.data.source == s.current_justified_checkpoint
           else 
            a.data.source == s.previous_justified_checkpoint
    }
    
}