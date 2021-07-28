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

include "../../utils/NativeTypes.dfy"
include "../../utils/Eth2Types.dfy"
include "../../utils/Helpers.dfy"
include "../../utils/MathHelpers.dfy"
include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../validators/Validators.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../Helpers.dfy"
include "EpochProcessing.s.dfy"
include "../forkchoice/ForkChoiceTypes.dfy"
include "../gasper/GasperJustification.dfy"

/**
 * State transition functional specification for the Beacon Chain.
 */
module StateTransitionSpec {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NativeTypes
    import opened Eth2Types
    import opened Constants
    import opened BeaconChainTypes
    import opened Validators
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened BeaconHelpers
    import opened MathHelpers
    import opened EpochProcessingSpec
    import opened ForkChoiceTypes
    import opened GasperJustification

    /**
     *  Collect pubkey in a list of validators.
     *
     *  @param  xv  A list of validators,
     *  @returns    The set of keys helpd byt the validators in `xv`.
     */
    function keysInValidators(xv : seq<Validator>) : set<BLSPubkey>
        decreases xv
    {
        if |xv| == 0 then  
            {}
        else 
            { xv[0].pubkey } + keysInValidators(xv[1..])
    }

    //  Specifications of finalisation of a state and forward to future slot.

    /**
     *  Result of processing eth1Data.
     *  
     *  @param  s   A state.
     *  @param  b   A block body to process.
     *  @returns    The state `s` updated to include b.eth1_data in the list of votes
     *              and state `s` eth1_data field set to b.eth1_data if b.eth1_data has
     *              received more than 1/2 * (EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH) votes.
     */
    function updateEth1Data(s: BeaconState, b: BeaconBlockBody) :  BeaconState 
        requires |s.validators| == |s.balances| 
        requires |s.eth1_data_votes| < EPOCHS_PER_ETH1_VOTING_PERIOD as int * SLOTS_PER_EPOCH as int
        ensures |updateEth1Data(s,b).validators| == |updateEth1Data(s,b).balances|
        ensures updateEth1Data(s,b).eth1_deposit_index == s.eth1_deposit_index
        ensures updateEth1Data(s,b).validators == s.validators
        ensures updateEth1Data(s,b).balances == s.balances
    {
        s.( eth1_data_votes := s.eth1_data_votes + [b.eth1_data],
            eth1_data := if (count_eth1_data_votes(s.eth1_data_votes + [b.eth1_data], b.eth1_data) * 2) > (EPOCHS_PER_ETH1_VOTING_PERIOD * SLOTS_PER_EPOCH) as int 
                then b.eth1_data 
                else s.eth1_data
            )
    }

    /**
     *  Result of processing a block.
     *  
     *  @param  s   A state.
     *  @param  b   A block to add to the state `s`.
     *  @returns    The state `s` updated to point to `b` with state_root set to 0.
     */
    function addBlockToState(s: BeaconState, b: BeaconBlock) :  BeaconState 
        //  Verify that the slots match
        requires b.slot == s.slot  
        //  Verify that the parent matches
        requires b.parent_root == hash_tree_root(s.latest_block_header) 
        requires |s.validators| == |s.balances| 
        ensures |addBlockToState(s,b).validators| == |addBlockToState(s,b).balances|
        ensures addBlockToState(s,b).eth1_data_votes == s.eth1_data_votes
        //  ensures |addBlockToState(s,b).eth1_data_votes| == |s.eth1_data_votes|
        ensures addBlockToState(s,b).eth1_deposit_index == s.eth1_deposit_index
        ensures addBlockToState(s,b).validators == s.validators
        ensures addBlockToState(s,b).balances == s.balances
    {
        s.(
            latest_block_header := BeaconBlockHeader(
                b.slot,
                b.parent_root,
                DEFAULT_BYTES32
            )
        )
    }

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
    function resolveStateRoot(s: BeaconState, store: Store): (s': BeaconState)
         /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        //  Make sure s.slot does not  overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat

        requires blockRootsValidWeak(s, store)

        // requires s.latest_block_header.state_root != DEFAULT_BYTES32 

        //  parent_root of the state block header is preserved
        ensures s.latest_block_header.parent_root == s'.latest_block_header.parent_root
        //  eth1_deposit_index is left unchanged
        ensures s.eth1_deposit_index == s'.eth1_deposit_index
        //  eth1_data_votes unchanged
        ensures s.eth1_data_votes == s'.eth1_data_votes

        ensures  s.latest_block_header.state_root != DEFAULT_BYTES32 ==>
            s' == advanceSlot(s)

        ensures blockRootsValidWeak(s', store)
    {
        var new_latest_block_header := 
            if (s.latest_block_header.state_root == DEFAULT_BYTES32 ) then 
                s.latest_block_header.(state_root := hash_tree_root(s))
            else 
                s.latest_block_header
            ;
        //  new state
        var s' := s.(
            slot := s.slot + 1,
            latest_block_header := new_latest_block_header,
            block_roots := s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(new_latest_block_header)],
            state_roots := s.state_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s)]
        );
        assert(blockRootsValidWeak(s', store));
        s'
        // store' := store + s'.latest_block_header
        // store' := store.(blocks := store.blocks[hash_tree_root(s'.latest_block_header) := b] );
    }

    predicate foo606(s: BeaconState, store: Store)
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        // requires 
    {
        (forall k :: k in s.block_roots ==> k in store.blocks.Keys) // P0
        // // && get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        // && get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys
        // && ((s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> s.current_justified_checkpoint.epoch < get_current_epoch(s))
        && s.current_justified_checkpoint.epoch < get_current_epoch(s)      // P1
        && (get_previous_epoch(s) >= 1 ==> s.current_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store))  //   P2 
        // && ((s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> s.previous_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store)) // P3
        && (get_current_epoch(s) >= 1 ==> s.previous_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store)) // P3
        // && ((s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> s.previous_justified_checkpoint.epoch < get_previous_epoch(s))
        && s.previous_justified_checkpoint.epoch < get_previous_epoch(s)    // P4
        // &&  ((s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> 
        && validPrevAttestations(s, store) // P5
        // && (get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot 
        // && ((s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> 
        && validCurrentAttestations(s, store)  // P6
        && s.previous_justified_checkpoint.root in store.blocks.Keys  // P7
        && s.current_justified_checkpoint.root in store.blocks.Keys     // P8
        
        // && ((s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0 ==> 
        && blockRootsValidWeak(s, store) // P9

        // && s.previous_justified_checkpoint.root in store.blocks.Keys 
        // && s.current_justified_checkpoint.root in store.blocks.Keys 
        
        && isJustified(s.previous_justified_checkpoint, store)  // P10
        && isJustified(s.current_justified_checkpoint, store)   //  P11

        // && ((s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0 ==> validCurrentAttestations(updateJustificationPrevEpoch(s, store), store))
    }

    lemma foo707(s: BeaconState, store: Store)
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        requires get_current_epoch(s) * SLOTS_PER_EPOCH < s.slot
        requires foo606(s, store)
        // ensures foo606(s, store)
        // ensures s.previous_justified_checkpoint.root in store.blocks.Keys 
        // ensures isJustified(s.previous_justified_checkpoint, store)
        // ensures get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
    {
        assume(foo606(s, store));
        // reveal_foo606();
        assert(s.current_justified_checkpoint.root in store.blocks.Keys);
        
        // assert(foo606(s,store) ==> isJustified(s.previous_justified_checkpoint, store));
    }

    /**
     *  Finalise a state and forward to slot in the future.
     *  
     *  @param  s       A state
     *  @param  slot    A slot. 
     *  @returns        A new state obtained by archiving roots and incrementing slot.
     *                  slot.
     */
    function forwardStateToSlot(s: BeaconState, slot: Slot, store: Store): (s': BeaconState)
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        requires foo606(s, store)
        // requires forall k :: k in s.block_roots ==> k in store.blocks.Keys

        // requires s.current_justified_checkpoint.epoch < get_current_epoch(s)
        // requires  get_previous_epoch(s) >= 1 ==> s.current_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store)


        // requires (s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> s.previous_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store) 
        // requires s.previous_justified_checkpoint.epoch < get_previous_epoch(s)
        // /** The attestations at previous epoch are valid. */
        // requires validPrevAttestations(s, store)
        // requires get_current_epoch(s) *  SLOTS_PER_EPOCH  < s.slot ==> validCurrentAttestations(s, store)

        requires s.slot <= slot
        requires |s.validators| == |s.balances|

        ensures s'.slot == slot
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures |s'.validators| == |s'.balances|
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures s'.eth1_data_votes == s.eth1_data_votes

        ensures foo606(s', store)


        //  termination ranking function
        decreases slot - s.slot
    {
        if (s.slot == slot) then 
            s
        else
            var s':= forwardStateToSlot(s, slot - 1, store);
            // assume(foo606(s', store));
            // assume(forall k :: k in s'.block_roots ==> k in store.blocks.Keys);
            // assume(s'.current_justified_checkpoint.epoch < get_current_epoch(s'));
            // assume(get_previous_epoch(s') >= 1 ==> s'.current_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store));
            nextSlot(s', store)
    }

    lemma forwardStateIsNotStoreDependent(s: BeaconState, slot: Slot, store1: Store, store2: Store)
        /** Store is well-formed. */
        requires isClosedUnderParent(store1)
        requires isClosedUnderParent(store2)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store1)
        requires isSlotDecreasing(store2)

        requires foo606(s, store1)
        requires foo606(s, store2)

        requires s.slot <= slot
        requires |s.validators| == |s.balances|
        ensures forwardStateToSlot(s, slot, store1) == forwardStateToSlot(s, slot, store2) 
    {
        if s.slot == slot {
            //  Thanks Dafny 
        } else {
            var s' := forwardStateToSlot(s, slot - 1, store1);
            forwardStateIsNotStoreDependent(s, slot - 1, store1, store2);
            assert(nextSlot(s', store1) == nextSlot(s', store2));
        }
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
    function advanceSlot(s : BeaconState) : BeaconState 
        //  Make sure s.slot does not overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
    {
        //  Add header root to history of block_roots
        var new_block_roots := s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s.latest_block_header)];
        //  Add state root to history of state roots
        var new_state_roots := s.state_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s)];
        //  Increment slot and copy latest_block_header
        s.(
            slot := s.slot + 1,
            block_roots := new_block_roots,
            state_roots := new_state_roots
        )
    }

    /**
     *  Defines the value of state at next slot.
     */
    function nextSlot(s: BeaconState, store: Store): (s': BeaconState) 
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        // requires forall k :: k in s.block_roots ==> k in store.blocks.Keys

        /** @todo: is current_epoch >=1 enough? */
        // requires get_previous_epoch(s) >= 1

        /** Block root at current epoc is in store. */
        // requires (s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        // requires (s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys

        requires foo606(s, store)
        /** Current justified checkpoint is justified and root in store. */ 
        // requires s.current_justified_checkpoint.root in store.blocks.Keys 
        // requires isJustified(s.current_justified_checkpoint, store)
        // requires s.current_justified_checkpoint.epoch < get_current_epoch(s)
        // requires  get_previous_epoch(s) >= 1 ==> s.current_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store)
       
        /** The block root at previous epoch is in the store. */
        // requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys

        // requires (s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> s.previous_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store) 
        // requires s.previous_justified_checkpoint.epoch < get_previous_epoch(s)
        // /** The attestations at previous epoch are valid. */
        // requires validPrevAttestations(s, store)
        // requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot ==> validCurrentAttestations(s, store)

        /** The justified checkpoints in s are indeed justified ands the root is in store. */
        // requires s.previous_justified_checkpoint.root in store.blocks.Keys 
        // requires s.current_justified_checkpoint.root in store.blocks.Keys 
        
        // requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0 ==> blockRootsValid(s, store)

        // requires isJustified(s.previous_justified_checkpoint, store)
        // requires isJustified(s.current_justified_checkpoint, store)

         /** Attestations to current epoch are valid. */
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0 ==> validCurrentAttestations(updateJustificationPrevEpoch(s, store), store)

        requires s.slot as nat + 1 < 0x10000000000000000 as nat

        requires |s.validators| == |s.balances|

        requires hash_tree_root(resolveStateRoot(s, store).latest_block_header) in store.blocks.Keys

        requires (s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0
        // requires (s.slot as nat + 1) < SLOTS_PER_EPOCH as nat

        // requires (s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 1

        // ensures false 

        ensures s'.latest_block_header.state_root != DEFAULT_BYTES32
        /** If s.slot is not at the boundary of an epoch, the 
            attestation/finality fields are unchanged. */
        ensures  (s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat != 0  ==>
            s'.justification_bits  == s.justification_bits
            && s'.previous_epoch_attestations  == s.previous_epoch_attestations
            && s'.current_epoch_attestations  == s.current_epoch_attestations
            && s'.previous_justified_checkpoint  == s.previous_justified_checkpoint
            && s'.current_justified_checkpoint  == s.current_justified_checkpoint
            && s'.validators  == s.validators
            && s'.balances  == s.balances
            && |s'.validators| == |s'.balances| 
            && s'.eth1_data_votes ==  s.eth1_data_votes
            && s'.eth1_deposit_index  == s.eth1_deposit_index

        ensures s'.previous_justified_checkpoint.root in store.blocks.Keys  
        ensures isJustified(s'.previous_justified_checkpoint, store)
        ensures s'.current_justified_checkpoint.root in store.blocks.Keys  
        ensures isJustified(s'.current_justified_checkpoint, store)

        // ensures false
        // ensures foo606(s', store)
        // ensures (forall k :: k in s'.block_roots ==> k in store.blocks.Keys)
        // ensures (s'.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> s'.current_justified_checkpoint.epoch < get_current_epoch(s')

        // ensures (get_previous_epoch(s') >= 1 ==> s'.current_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store))

        // ensures forall k :: k in s'.block_roots ==> k in store.blocks.Keys

    {
        // reveal_foo606();
        if (s.slot + 1) %  SLOTS_PER_EPOCH == 0 then 
            //  Apply update on partially resolved state, and then update slot
            assert(s.slot % SLOTS_PER_EPOCH != 0);
            var s1 := resolveStateRoot(s, store).(slot := s.slot, block_roots := s.block_roots);

            // assert get_block_root(s, get_current_epoch(s)) in store.blocks.Keys;
            // assert(s1.slot == s.slot);
            // assert(get_current_epoch(s1) * SLOTS_PER_EPOCH < s1.slot);
            // assert(get_block_root(s1, get_current_epoch(s1)) == get_block_root(s, get_current_epoch(s)));
            // assert get_block_root(s, get_current_epoch(s)) in store.blocks.Keys;
            // assert get_block_root(s1, get_current_epoch(s1)) in store.blocks.Keys;
            // assert get_block_root(s1, get_previous_epoch(s1)) in store.blocks.Keys;
            // assert(s1.current_justified_checkpoint.root == s.current_justified_checkpoint.root);
            // assert(s1.previous_justified_checkpoint == s.previous_justified_checkpoint);
            // assert s.current_justified_checkpoint.root in store.blocks.Keys;
            // assert s1.current_justified_checkpoint.root in store.blocks.Keys ;
            // assert s1.previous_justified_checkpoint.root in store.blocks.Keys ;
            // assert s1.current_justified_checkpoint.epoch < get_current_epoch(s1);
            // assert(get_block_root(s1, get_previous_epoch(s1)) == get_block_root(s, get_previous_epoch(s)));
            // assert get_block_root(s1, get_previous_epoch(s1)) in store.blocks.Keys;

            // assume(s1.block_roots == s.block_roots);
            // assert s1.previous_justified_checkpoint.root in chainRoots(get_block_root(s1, get_previous_epoch(s1)), store) ;
            // assert s1.previous_justified_checkpoint.epoch < get_previous_epoch(s1);
            // assert(s1.previous_epoch_attestations == s.previous_epoch_attestations);
            // assert s1.current_justified_checkpoint.root in chainRoots(get_block_root(s1, get_previous_epoch(s1)), store);

            preserveValidPrev(s, s1, store);
            // assert validPrevAttestations(s, store);
            assert validPrevAttestations(s1, store);

            assert s1.previous_justified_checkpoint.root in store.blocks.Keys ;
            assert s1.current_justified_checkpoint.root in store.blocks.Keys ;
            
            assert isJustified(s1.previous_justified_checkpoint, store);
            assert isJustified(s1.current_justified_checkpoint, store);

            // assert(updateJustificationPrevEpoch(s1, store) == updateJustificationPrevEpoch(s, store));
            preserveValidCurrent(updateJustificationPrevEpoch(s, store), updateJustificationPrevEpoch(s1, store), store);
            assert validCurrentAttestations(updateJustificationPrevEpoch(s1, store), store);

            var s2 := updateJustificationAndFinalisation(s1, store);
            assert(isJustified(s2.previous_justified_checkpoint, store));
            assert(isJustified(s2.current_justified_checkpoint, store));
            var s3 := finalUpdates(s2, store);
            assert(isJustified(s3.previous_justified_checkpoint, store));
            assert(isJustified(s3.current_justified_checkpoint, store));
            var s4 := s3.(slot := s.slot + 1);

            assert(isJustified(s4.previous_justified_checkpoint, store));
            assert(isJustified(s4.current_justified_checkpoint, store));
            assert s4.previous_justified_checkpoint.root in store.blocks.Keys ;
            assert s4.current_justified_checkpoint.root in store.blocks.Keys ;
            assert(s4.slot == s.slot + 1);
            // assume s4.current_justified_checkpoint.epoch < get_current_epoch(s4);
            // assume forall k :: k in resolveStateRoot(s4).block_roots ==> k in store.blocks.Keys;
            // assume (get_previous_epoch(s4) >= 1 ==> s4.current_justified_checkpoint.root in chainRoots(get_block_root(s4, get_previous_epoch(s4)), store));

            assert(((s4.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> s.previous_justified_checkpoint.root in chainRoots(get_block_root(s4, get_previous_epoch(s4)), store)));
            assert (s4.slot as nat + 1) %  SLOTS_PER_EPOCH as nat != 0 ;
            assert(get_previous_epoch(s4) >= 1 ==> s4.current_justified_checkpoint.root in chainRoots(get_block_root(s4, get_previous_epoch(s4)), store));
            // assume((forall k :: k in s4.block_roots ==> k in store.blocks.Keys));
            assert blockRootsValidWeak(s4, store);
            reveal_validCurrentAttestations();
            assert(s4.current_epoch_attestations == []);
            assert(validCurrentAttestations(s4, store));
            assert(s4.previous_justified_checkpoint == s.current_justified_checkpoint);
            assert(get_previous_epoch(s4) == get_current_epoch(s));
            transferValidCurrentAttToPreviousAtEpoch(s, s4, store);
            assert(validPrevAttestations(s4, store));
            assert(foo606(s4, store));

            s4
        else if (s.slot + 1) %  SLOTS_PER_EPOCH != 1 then 
            var s':= resolveStateRoot(s, store);
            //  @note: this captures advanceSlot as a special case of resolveStateRoot 
            assert s'.current_justified_checkpoint.epoch < get_current_epoch(s');   //  p1
            assert forall k :: k in s'.block_roots ==> k in store.blocks.Keys;
            assert (get_previous_epoch(s') >= 1 ==> s'.current_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store)); //  P2

            assert s'.previous_justified_checkpoint == s.previous_justified_checkpoint;
            assert s'.current_justified_checkpoint == s.current_justified_checkpoint;

            assert (get_current_epoch(s') >= 1 ==> s'.previous_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store));    //  P3 

            assert s'.previous_justified_checkpoint.epoch < get_previous_epoch(s');   // P4
            // assert  ((s'.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> validPrevAttestations(s', store)) ;  // P5
           
            // assert ((s'.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> validCurrentAttestations(s', store)) ; // P6
            assert s'.previous_justified_checkpoint.root in store.blocks.Keys ; // P7
            assert s'.current_justified_checkpoint.root in store.blocks.Keys ;  // P8

            // var store' := store.(blocks := store.blocks + )

            // store' := store.(blocks := store.blocks[hash_tree_root(b) := b] )
            // assume()
            assert forall k :: k in s'.block_roots ==> k in store.blocks.Keys;
            assert blockRootsValidWeak(s', store);
            
            // assert ((s'.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0 ==> blockRootsValid(s', store));
            assert isJustified(s'.previous_justified_checkpoint, store);  // P10
            assert isJustified(s'.current_justified_checkpoint, store);   //  P11
            // assert(((s'.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> s.previous_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store)));
            // assert(foo606(s', store));
            assert(s'.slot == s.slot + 1);
            // assert(s'.current_epoch_attestations == []);
            // assert(validCurrentAttestations(s', store));
            // assert s.current_justified_checkpoint == s'.current_justified_checkpoint;
            // assert ((s'.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0 ==> s'.current_justified_checkpoint.epoch < get_current_epoch(s'));
            // resolveStateRoot(s)
            s'
        else 
            assert (s.slot + 1) %  SLOTS_PER_EPOCH == 1;
            var s':= resolveStateRoot(s, store);
            //  @note: this captures advanceSlot as a special case of resolveStateRoot 
            assert s'.current_justified_checkpoint.epoch < get_current_epoch(s');   //  p1
            assert forall k :: k in s'.block_roots ==> k in store.blocks.Keys;
            assert (get_previous_epoch(s') >= 1 ==> s'.current_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store)); //  P2

            assert s'.previous_justified_checkpoint == s.previous_justified_checkpoint;
            assert s'.current_justified_checkpoint == s.current_justified_checkpoint;

            assert (get_current_epoch(s') >= 1 ==> s'.previous_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store));    //  P3 

            assert s'.previous_justified_checkpoint.epoch < get_previous_epoch(s');   // P4
            // assert  ((s'.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> validPrevAttestations(s', store)) ;  // P5
           
            // assert ((s'.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> validCurrentAttestations(s', store)) ; // P6
            assert s'.previous_justified_checkpoint.root in store.blocks.Keys ; // P7
            assert s'.current_justified_checkpoint.root in store.blocks.Keys ;  // P8

            // var store' := store.(blocks := store.blocks + )

            // store' := store.(blocks := store.blocks[hash_tree_root(b) := b] )
            // assume()
            assert blockRootsValidWeak(s', store);
            assert forall k :: k in s'.block_roots ==> k in store.blocks.Keys;
            
            // assert ((s'.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0 ==> blockRootsValid(s', store));
            assert isJustified(s'.previous_justified_checkpoint, store);  // P10
            assert isJustified(s'.current_justified_checkpoint, store);   //  P11
            // assert(((s'.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> s.previous_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store)));
            // assert(foo606(s', store));
            assert(s'.slot == s.slot + 1);
            // assert s.current_justified_checkpoint == s'.current_justified_checkpoint;
            // assert ((s'.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0 ==> s'.current_justified_checkpoint.epoch < get_current_epoch(s'));
            // resolveStateRoot(s)
            s'
    }

}