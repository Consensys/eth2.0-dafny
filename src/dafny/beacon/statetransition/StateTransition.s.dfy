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

 // @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /trace /noCheating:0

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

    lemma {:axion} magicAddToStore(r: Root, store: Store)
         /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)
        ensures r in store.blocks.Keys 

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

    // function resolveBlockRoot(s: BeaconState, store: Store): (store': Store)
    //     /** Store is well-formed. */
    //     requires isClosedUnderParent(store)
    //     /**  The decreasing property guarantees that this function terminates. */
    //     requires isSlotDecreasing(store)

    //     //  Make sure s.slot does not  overflow
    //     requires s.slot as nat + 1 < 0x10000000000000000 as nat
    // {
    //     var new_latest_block_header := 
    //         if (s.latest_block_header.state_root == DEFAULT_BYTES32 ) then 
    //             s.latest_block_header.(state_root := hash_tree_root(s))
    //         else 
    //             s.latest_block_header
    //         ;
    //     if (s.latest_block_header.state_root == DEFAULT_BYTES32 ) then 
    //         store.(blocks := store.blocks[hash_tree_root(new_latest_block_header) := new_latest_block_header])
    //     else 
    //         store
    // }

    /**
     *  Complete the current slot.
     *
     *  @param  s   A beacon state.
     *  @returns    A new state s' such that:
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

        // requires s.latest_block_header.state_root == DEFAULT_BYTES32 
        requires blockRootsValidWeak(s, store)
        // requires get_current_epoch(s) * SLOTS_PER_EPOCH < s.slot

        // requires s.latest_block_header.state_root != DEFAULT_BYTES32 
        // requires s.latest_block_header.state_root == DEFAULT_BYTES32 ==>
        // requires s.latest_block_header.state_root == DEFAULT_BYTES32 ==>  
        //         hash_tree_root(s.latest_block_header.(state_root := hash_tree_root(s))) in store.blocks.Keys
        // requires s.latest_block_header.state_root != DEFAULT_BYTES32 ==>  
        //         hash_tree_root(s.latest_block_header) in store.blocks.Keys

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
        // reveal_blockRootsValidWeak2();
        var new_latest_block_header := 
            if (s.latest_block_header.state_root == DEFAULT_BYTES32 ) then 
                s.latest_block_header.(state_root := hash_tree_root(s))
            else 
                s.latest_block_header
            ;
        // var new_store := 
        //     if (s.latest_block_header.state_root == DEFAULT_BYTES32 ) then 
        //         store.(blocks := store.blocks[hash_tree_root(new_latest_block_header) := new_latest_block_header])
        //     else 
        //         store
        //     ;
        //  new state
        var s' := s.(
            slot := s.slot + 1,
            latest_block_header := new_latest_block_header,
            block_roots := s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(new_latest_block_header)],
            state_roots := s.state_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s)]
        );
        assume(blockRootsValidWeak(s', store));
        // assert(hash_tree_root(new_latest_block_header) in store.blocks.Keys);
        // assume (forall br :: br in s'.block_roots ==> br in store.blocks.Keys);
        s'
    }

    // lemma foo007(s: BeaconState, store: Store)
    //     /** The store is well-formed, each block with slot != 0 has a parent
    //         which is itself in the store. */
    //     requires isClosedUnderParent(store)
    //     requires isSlotDecreasing(store)  

    //     requires s.slot as nat + 1 < 0x10000000000000000 as nat

    //     requires (s.slot + 1) % SLOTS_PER_EPOCH  == 0
    //     // requires blockRootsValidWeak()
    //     // requires blockRootsValidWeak(s'.(slot := s.slot + 1), store);
    //     // assert s' == resolveStateRoot(s, store).(slot := s.slot);

    //     requires blockRootsValidWeak(s.(slot := s.slot + 1), store)
    //     ensures blockRootsValidWeak(resolveStateRoot(s, store).(slot := s.slot), store)
    // {

    // }

    // lemma foo101(s: BeaconState, s': BeaconState, store: Store)
    //     requires s.slot as nat + 1 < 0x10000000000000000 as nat
    //     requires get_current_epoch(s) * SLOTS_PER_EPOCH < s.slot

    //      /** The store is well-formed, each block with slot != 0 has a parent
    //         which is itself in the store. */
    //     requires isClosedUnderParent(store)
    //     requires isSlotDecreasing(store) 
    //     requires blockRootsValidWeak2(s, store)

    //     requires s.latest_block_header.state_root != DEFAULT_BYTES32
    //     // requires hash_tree_root(s.latest_block_header) in store.blocks.Keys

    //     requires s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int] == hash_tree_root(s.latest_block_header)
    //     requires s' == resolveStateRoot(s, store) 

    //     ensures blockRootsValidWeak2(s', store)
    // {

    // }

    // lemma foo102(s: BeaconState, s': BeaconState, store: Store)
    //     requires s.slot as nat + 1 < 0x10000000000000000 as nat
    //     requires get_current_epoch(s) * SLOTS_PER_EPOCH < s.slot

    //      /** The store is well-formed, each block with slot != 0 has a parent
    //         which is itself in the store. */
    //     requires isClosedUnderParent(store)
    //     requires isSlotDecreasing(store) 
    //     requires blockRootsValidWeak2(s, store)

    //     requires s.latest_block_header.state_root == DEFAULT_BYTES32
    //     // requires hash_tree_root(s.latest_block_header) in store.blocks.Keys

    //     requires s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int] == hash_tree_root(s.latest_block_header)
    //     requires s' == resolveStateRoot(s, store) 

    //     // ensures blockRootsValidWeak2(s', store)
    // {
    //     assert (forall br :: br in s'.block_roots ==> br in store.blocks.Keys);
    //     // assert (forall br :: br in chainRoots(s'.block_roots[0], store) ==>  br in store.blocks.Keys);
    //     // assert (forall i, j :: 0 < i < j < SLOTS_PER_HISTORICAL_ROOT ==> 
    //     //     s'.block_roots[i] in chainRoots(s'.block_roots[j], store)
    //     // )
    // }

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

        && ((s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 1 ==> s.current_epoch_attestations == [])
        // && ((s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0 ==> validCurrentAttestations(updateJustificationPrevEpoch(s, store), store))
    }

    // lemma foo707(s: BeaconState, store: Store)
    //     /** Store is well-formed. */
    //     requires isClosedUnderParent(store)
    //     /**  The decreasing property guarantees that this function terminates. */
    //     requires isSlotDecreasing(store)

    //     requires get_current_epoch(s) * SLOTS_PER_EPOCH < s.slot
    //     requires foo606(s, store)
    //     // ensures foo606(s, store)
    //     // ensures s.previous_justified_checkpoint.root in store.blocks.Keys 
    //     // ensures isJustified(s.previous_justified_checkpoint, store)
    //     // ensures get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
    // {
    //     assume(foo606(s, store));
    //     // reveal_foo606();
    //     assert(s.current_justified_checkpoint.root in store.blocks.Keys);
        
    //     // assert(foo606(s,store) ==> isJustified(s.previous_justified_checkpoint, store));
    // }

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

        requires |s.validators| == |s.balances|
        requires s.slot <= slot

        ensures s'.slot == slot
        ensures |s'.validators| == |s'.balances|
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures s'.eth1_data_votes == s.eth1_data_votes
        ensures s'.eth1_deposit_index  == s.eth1_deposit_index


//  ensures 
//             && s'.validators  == s.validators
//             && s'.balances  == s.balances
//             && |s'.validators| == |s'.balances| 
//             && s'.eth1_data_votes ==  s.eth1_data_votes
//             && s'.eth1_deposit_index  == s.eth1_deposit_index

        ensures foo606(s', store)

        //  termination ranking function
        decreases slot - s.slot
    {
        if (s.slot == slot) then 
            s
        else
            var s1:= forwardStateToSlot(s, slot - 1, store);
            nextSlot(s1, store)
    }


    //  does not seem to be used ...
    // lemma forwardStateIsNotStoreDependent(s: BeaconState, slot: Slot, store1: Store, store2: Store)
    //     /** Store is well-formed. */
    //     requires isClosedUnderParent(store1)
    //     requires isClosedUnderParent(store2)
    //     /**  The decreasing property guarantees that this function terminates. */
    //     requires isSlotDecreasing(store1)
    //     requires isSlotDecreasing(store2)

    //     requires foo606(s, store1)
    //     requires foo606(s, store2)

    //     requires s.slot <= slot
    //     requires |s.validators| == |s.balances|

    //     ensures  foo606(s, store1)
    //     ensures  foo606(s, store2)
    //     ensures forwardStateToSlot(s, slot, store1) == forwardStateToSlot(s, slot, store2) 

    //     decreases slot 
    // {
    //     if s.slot == slot {
    //         //  Thanks Dafny 
    //     } else {
    //         var s1 := forwardStateToSlot(s, slot - 1, store1);
    //         var s2 := forwardStateToSlot(s, slot - 1, store2);
    //         forwardStateIsNotStoreDependent(s, slot - 1, store1, store2);
    //         // assume 
    //         assert s1 == s2;
    //         nextSlotIsNotStoreDependent(s1, store1, store2);
    //         assert(nextSlot(s1, store1) == nextSlot(s2, store2));
    //     }
    // }

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

    // lemma foo202(s: BeaconState, s': BeaconState, store: Store)
    //     requires s.slot as nat + 1 < 0x10000000000000000 as nat
    //      /** The store is well-formed, each block with slot != 0 has a parent
    //         which is itself in the store. */
    //     requires isClosedUnderParent(store)
    //     requires isSlotDecreasing(store) 
    //     requires blockRootsValidWeak2(s, store)

    //     requires hash_tree_root(s.latest_block_header) in store.blocks.Keys

    //     // requires s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int] == hash_tree_root(s.latest_block_header)

    //     // requires 
    //     requires s' == advanceSlot(s) 

    //     ensures blockRootsValidWeak2(s', store)
    // {

    // }


    /**
     *  Defines the value of state at next slot.
     *  
     * Std: 163secs, split 1100secs   
     */
    function nextSlot(s: BeaconState, store: Store): (s': BeaconState) 
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        requires foo606(s, store)
        
        requires s.slot as nat + 1 < 0x10000000000000000 as nat

        requires |s.validators| == |s.balances|

       
        // requires (s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0

        ensures s'.latest_block_header.state_root != DEFAULT_BYTES32
        /** If s.slot is not at the boundary of an epoch, the 
            attestation/finality fields are unchanged. */
        ensures  (s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat != 0  ==>
            s'.justification_bits  == s.justification_bits
            && s'.previous_epoch_attestations  == s.previous_epoch_attestations
            && s'.current_epoch_attestations  == s.current_epoch_attestations
            && s'.previous_justified_checkpoint  == s.previous_justified_checkpoint
            && s'.current_justified_checkpoint  == s.current_justified_checkpoint
            
        ensures 
            && s'.validators  == s.validators
            && s'.balances  == s.balances
            && |s'.validators| == |s'.balances| 
            && s'.eth1_data_votes ==  s.eth1_data_votes
            && s'.eth1_deposit_index  == s.eth1_deposit_index

        ensures foo606(s', store)

    {
        // reveal_foo606();
        if (s.slot + 1) %  SLOTS_PER_EPOCH == 0 then 
            //  175sec std, 1220sec split
            //  Apply update on partially resolved state, and then update slot
            assert(s.slot % SLOTS_PER_EPOCH != 0);
            var s1 := resolveStateRoot(s, store).(slot := s.slot, block_roots := s.block_roots);

            preserveValidPrev(s, s1, store);
            // assert validPrevAttestations(s, store);
            assert validPrevAttestations(s1, store);

            assert s1.previous_justified_checkpoint.root in store.blocks.Keys ;
            assert s1.current_justified_checkpoint.root in store.blocks.Keys ;
            
            assert isJustified(s1.previous_justified_checkpoint, store);
            assert isJustified(s1.current_justified_checkpoint, store);

            // assert(updateJustificationPrevEpoch(s1, store) == updateJustificationPrevEpoch(s, store));
            preserveValidCurrent(updateJustificationPrevEpoch(s, store), updateJustificationPrevEpoch(s1, store), store);
            magicAddToStore(hash_tree_root(s1.latest_block_header), store);
            //  next one don't know how to get rid of it
            assume(validCurrentAttestations(updateJustificationPrevEpoch(s, store), store));
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

            assert(((s4.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> s.previous_justified_checkpoint.root in chainRoots(get_block_root(s4, get_previous_epoch(s4)), store)));
            assert (s4.slot as nat + 1) %  SLOTS_PER_EPOCH as nat != 0 ;
            assert(get_previous_epoch(s4) >= 1 ==> s4.current_justified_checkpoint.root in chainRoots(get_block_root(s4, get_previous_epoch(s4)), store));

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
            assert (s.slot + 1) %  SLOTS_PER_EPOCH != 0;

            //  Order of asserts is important
            var s':= resolveStateRoot(s, store);
            assert(s'.slot == s.slot + 1);

            magicAddToStore(hash_tree_root(s'.latest_block_header), store);

            assert get_current_epoch(s') * SLOTS_PER_EPOCH < s'.slot;
            assert get_current_epoch(s) * SLOTS_PER_EPOCH  < s.slot;

            assert get_current_epoch(s) == get_current_epoch(s');
            assert get_previous_epoch(s) == get_previous_epoch(s');

            //  @note: this captures advanceSlot as a special case of resolveStateRoot 
            assert forall k :: k in s'.block_roots ==> k in store.blocks.Keys;  //  P0
            
            assert s'.previous_justified_checkpoint == s.previous_justified_checkpoint;
            assert s'.current_justified_checkpoint == s.current_justified_checkpoint;

            assert s'.current_justified_checkpoint.epoch < get_current_epoch(s');   //  P1
            assert s'.previous_justified_checkpoint.epoch < get_previous_epoch(s');   // P4

            //  these assumes should be discharged
            assume get_block_root(s', get_current_epoch(s')) == get_block_root(s, get_current_epoch(s));
            assume get_block_root(s', get_previous_epoch(s')) == get_block_root(s, get_previous_epoch(s));

            assert (get_current_epoch(s') >= 1 ==> s'.previous_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store));    //  P3 

            assert (get_previous_epoch(s') >= 1 ==> s'.current_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store)); //  P2

            // assume  ((s'.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> validPrevAttestations(s', store)) ;  // P5
           
            // assume ((s'.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> validCurrentAttestations(s', store)) ; // P6
            assert s'.previous_justified_checkpoint.root in store.blocks.Keys ; // P7
            assert s'.current_justified_checkpoint.root in store.blocks.Keys ;  // P8

            // var store' := store.(blocks := store.blocks + )

            // store' := store.(blocks := store.blocks[hash_tree_root(b) := b] )
            // assume()
            // assume forall k :: k in s'.block_roots ==> k in store.blocks.Keys;
            assert blockRootsValidWeak(s', store);  //  P9
            
            // assert ((s'.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0 ==> blockRootsValid(s', store));
            assert isJustified(s'.previous_justified_checkpoint, store);  // P10
            assert isJustified(s'.current_justified_checkpoint, store);   //  P11
            // assume(((s'.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> s.previous_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store)));
            // assume(foo606(s', store));
            // assume(s'.current_epoch_attestations == []);
            // reveal_validCurrentAttestations();
            // reveal_validPrevAttestations();
            //  previous attestations
            // assert get_previous_epoch(s') *  SLOTS_PER_EPOCH   < s'.slot;

            
            transferValidCurrentAttToPreviousAtEpoch2(s, s', store);
            // assert (forall a :: a in s'.current_epoch_attestations ==> a in store.rcvdAttestations);
            assert(validPrevAttestations(s', store));   //  P5
            assert(validCurrentAttestations(s', store));    //  P6
            // assert(
            //     forall  a :: a in s'.current_epoch_attestations ==>
            //              a in s.current_epoch_attestations
            //              &&  a.data.source == s.current_justified_checkpoint
            // );
            // assert s.current_justified_checkpoint == s'.current_justified_checkpoint;
            // assert ((s'.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0 ==> s'.current_justified_checkpoint.epoch < get_current_epoch(s'));
            // resolveStateRoot(s)
            assert(foo606(s', store));

            s'
        else 
            assert (s.slot + 1) %  SLOTS_PER_EPOCH == 1;
            var s':= resolveStateRoot(s, store);
            //  @note: this captures advanceSlot as a special case of resolveStateRoot 
            assert(s'.slot == s.slot + 1);
            magicAddToStore(hash_tree_root(s'.latest_block_header), store);

            assert forall k :: k in s'.block_roots ==> k in store.blocks.Keys;

            assert get_current_epoch(s') * SLOTS_PER_EPOCH < s'.slot;
            assert get_current_epoch(s) * SLOTS_PER_EPOCH  == s.slot;

            assert s'.previous_justified_checkpoint == s.previous_justified_checkpoint;
            assert s'.current_justified_checkpoint == s.current_justified_checkpoint;

            assert s'.current_justified_checkpoint.epoch < get_current_epoch(s');   //  P1
            assert s'.previous_justified_checkpoint.epoch < get_previous_epoch(s');   // P4

            assert (get_previous_epoch(s') >= 1 ==> s'.current_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store)); //  P2
            assert (get_current_epoch(s') >= 1 ==> s'.previous_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store));    //  P3 

            // assert  ((s'.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> validPrevAttestations(s', store)) ;  // P5
           
            // assert ((s'.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> validCurrentAttestations(s', store)) ; // P6
            assert s'.previous_justified_checkpoint.root in store.blocks.Keys ; // P7
            assert s'.current_justified_checkpoint.root in store.blocks.Keys ;  // P8

            // var store' := store.(blocks := store.blocks + )

            // store' := store.(blocks := store.blocks[hash_tree_root(b) := b] )
            // assume()
            assert blockRootsValidWeak(s', store);  //  P9
            // assert forall k :: k in s'.block_roots ==> k in store.blocks.Keys;
            
            // assert ((s'.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0 ==> blockRootsValid(s', store));
            assert isJustified(s'.previous_justified_checkpoint, store);  // P10
            assert isJustified(s'.current_justified_checkpoint, store);   //  P11
            // assert(((s'.slot as nat + 1) %  SLOTS_PER_EPOCH as nat == 0 ==> s.previous_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store)));
            reveal_validCurrentAttestations();
            reveal_validPrevAttestations();
            assert(s.current_epoch_attestations == []);
            assert(s.current_epoch_attestations == s'.current_epoch_attestations);
            assert(validCurrentAttestations(s', store));
            // assert (forall a :: a in s'.current_epoch_attestations ==> a in store.rcvdAttestations);
            // assert get_current_epoch(s') *  SLOTS_PER_EPOCH   < s'.slot ;
            // assert (forall a :: a in s'.current_epoch_attestations ==>
            //     // && a in store.rcvdAttestations
            //     && a.data.source == s'.current_justified_checkpoint
            //     // && a.data.source.epoch == s.current_justified_checkpoint.epoch
            //     // && a.data.target.root == get_block_root(s, get_current_epoch(s))
            //     // && a.data.target.epoch ==  get_current_epoch(s)
            // );
            assert(validPrevAttestations(s', store));
            
            assert(foo606(s', store));
            // assume get_block_root(s', get_current_epoch(s')) == get_block_root(s, get_current_epoch(s));

            
            // transferValidCurrentAttToPreviousAtEpoch2(s, s', store);
            // assert (forall a :: a in s'.current_epoch_attestations ==> a in store.rcvdAttestations);
            // assert(validCurrentAttestations(s', store));
            // assert s.current_justified_checkpoint == s'.current_justified_checkpoint;
            // assert ((s'.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0 ==> s'.current_justified_checkpoint.epoch < get_current_epoch(s'));
            // resolveStateRoot(s)
            s'
    }

    // lemma resolveStateRootNotStoreDep(s: BeaconState, store1: Store, store2: Store)
    //      /** Store is well-formed. */
    //     requires isClosedUnderParent(store1)
    //     requires isClosedUnderParent(store2)
    //     /**  The decreasing property guarantees that this function terminates. */
    //     requires isSlotDecreasing(store1)
    //     requires isSlotDecreasing(store2)

    //     requires s.slot as nat + 1 < 0x10000000000000000 as nat

    //     requires foo606(s, store1)
    //     requires foo606(s, store2)

    //     ensures resolveStateRoot(s, store1) == resolveStateRoot(s, store2)

    // {

    // }

    /** Only case !=0 proved  */
    // lemma nextSlotIsNotStoreDependent(s: BeaconState, store1: Store, store2: Store)
    //     /** Store is well-formed. */
    //     requires isClosedUnderParent(store1)
    //     requires isClosedUnderParent(store2)
    //     /**  The decreasing property guarantees that this function terminates. */
    //     requires isSlotDecreasing(store1)
    //     requires isSlotDecreasing(store2)

    //     requires foo606(s, store1)
    //     requires foo606(s, store2)
        
    //     requires s.slot as nat + 1 < 0x10000000000000000 as nat

    //     requires |s.validators| == |s.balances|

    //     requires (s.slot + 1) %  SLOTS_PER_EPOCH != 0

    //     ensures nextSlot(s, store1) == nextSlot(s, store2)
    // {
    //     // resolveStateRootNotStoreDep(s, store1, store2);
    //     if (s.slot + 1) %  SLOTS_PER_EPOCH == 0 {
    //         //  Thanks Dafny
    //     } else if (s.slot + 1) %  SLOTS_PER_EPOCH != 1 {
    //         //  Thanks Dafny
    //     } else {
    //         assert (s.slot + 1) %  SLOTS_PER_EPOCH == 1; 
    //         //  Thanks Dafny
    //     }
    // }

}