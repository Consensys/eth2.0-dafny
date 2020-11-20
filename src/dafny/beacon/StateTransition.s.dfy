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
include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "../ssz/Constants.dfy"
include "BeaconChainTypes.dfy"
include "Validators.dfy"
include "Attestations.dfy"
include "Helpers.dfy"

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
    import opened Attestations
    import opened BeaconHelpers

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
     *  Result of processing a block.
     *  
     *  @param  s   A state.
     *  @param  b   A block to add to the state `s`.
     *  @returns    The state `s` updated to point to `b` with state_root set to 0.
     */
    function addBlockToState(s: BeaconState, b: BeaconBlock) :  BeaconState 
        //  Verify that the slots match
        requires b.slot == s.slot  
        // Verify that the parent matches
        requires b.parent_root == hash_tree_root(s.latest_block_header) 
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
    function resolveStateRoot(s: BeaconState): BeaconState 
        //  Make sure s.slot does not  overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        //  parent_root of the state block header is preserved
        ensures s.latest_block_header.parent_root == resolveStateRoot(s).latest_block_header.parent_root
        //  eth1_deposit_index is left unchanged
        ensures s.eth1_deposit_index == resolveStateRoot(s).eth1_deposit_index

        ensures  s.latest_block_header.state_root != DEFAULT_BYTES32 ==>
            resolveStateRoot(s) == advanceSlot(s)
    {
        var new_latest_block_header := 
            if (s.latest_block_header.state_root == DEFAULT_BYTES32 ) then 
                s.latest_block_header.(state_root := hash_tree_root(s))
            else 
                s.latest_block_header
            ;
        //  new state
        s.(
            slot := s.slot + 1,
            latest_block_header := new_latest_block_header,
            block_roots := s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(new_latest_block_header)],
            state_roots := s.state_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s)]
        )
    }

    /**
     *  Finalise a state and forward to slot in the future.
     *  
     *  @param  s       A state
     *  @param  slot    A slot. 
     *  @returns        A new state obtained by archiving roots and incrementing slot.
     *                  slot.
     */
    function forwardStateToSlot(s: BeaconState, slot: Slot) : BeaconState 
        requires s.slot <= slot

        ensures forwardStateToSlot(s, slot).slot == slot
        ensures forwardStateToSlot(s, slot).eth1_deposit_index == s.eth1_deposit_index
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
    function nextSlot(s: BeaconState) : BeaconState 
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        ensures nextSlot(s).latest_block_header.state_root != DEFAULT_BYTES32
        /** If s.slot is not at the boundary of an epoch, the 
            attestation/finality fields are unchanged. */
        ensures  (s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat != 0  ==>
            nextSlot(s).justification_bits  == s.justification_bits
            && nextSlot(s).previous_epoch_attestations  == s.previous_epoch_attestations
            && nextSlot(s).current_epoch_attestations  == s.current_epoch_attestations
            && nextSlot(s).previous_justified_checkpoint  == s.previous_justified_checkpoint
            && nextSlot(s).current_justified_checkpoint  == s.current_justified_checkpoint
    {
            if (s.slot + 1) %  SLOTS_PER_EPOCH == 0 then 
                //  Apply update on partially resolved state, and then update slot
                assert(s.slot % SLOTS_PER_EPOCH != 0);
                // updateJustification(resolveStateRoot(s).(slot := s.slot)).(slot := s.slot + 1)
                updateJustificationAndFinalisation(resolveStateRoot(s).(slot := s.slot)).(slot := s.slot + 1)
            else 
                //  @note: this captures advanceSlot as a special case of resolveStateRoot 
                resolveStateRoot(s)
    }

    /**
     *  Take into account deposits in a block.
     *
     *  @param  s       A beacon state.
     *  @param  body    A block body.
     *  @returns        The state obtained after taking account the deposits in `body` from state `s` 
     */
    function updateDeposits(s: BeaconState, b: BeaconBlock) : BeaconState 
        requires s.eth1_deposit_index as int +  |b.body.deposits| < 0x10000000000000000 
    {
        s.(
            eth1_deposit_index := (s.eth1_deposit_index as int + |b.body.deposits|) as uint64
        )
    }

    /**
     *  Simplified first-cut specification of process_justification_and_finalization.
     *
     *  @param  s   A beacon state the slot of which is not an Epoch boundary. 
     *  @returns    The new state with justification checkpoints updated.
     *  
     */
    function updateJustificationPrevEpoch(s: BeaconState) : BeaconState 
        /** State's slot is not an Epoch boundary. */
        requires s.slot % SLOTS_PER_EPOCH != 0
        /** Justification bit are right-shifted and last two are not modified.
            Bit0 (new checkpoint) and Bit1 (previous checkpoint) may be modified.
         */
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            updateJustificationPrevEpoch(s).justification_bits[2..] == 
                (s.justification_bits)[1..|s.justification_bits| - 1]
    {
        if  get_current_epoch(s) <= GENESIS_EPOCH + 1 then 
            s 
        else 
            //  Right shift  justification_bits and prepend false
            var newJustBits:= [false] + (s.justification_bits)[..JUSTIFICATION_BITS_LENGTH - 1];
            //  Previous epoch checkpoint
            //  Get attestations 
            var matching_target_attestations := 
                get_matching_target_attestations(s, get_previous_epoch(s));
            var b1 := get_attesting_balance(s, matching_target_attestations) as nat * 3 
                        >= get_total_active_balance(s) as nat * 2;
            var c := CheckPoint(get_previous_epoch(s),
                                        get_block_root(s, get_previous_epoch(s)));
            s.(
                current_justified_checkpoint := if b1 then c else s.current_justified_checkpoint,
                previous_justified_checkpoint := s.current_justified_checkpoint,
                justification_bits := if b1 then newJustBits[1 := true] else newJustBits
            )
    }

    function updateJustification(s: BeaconState) : BeaconState
        requires s.slot % SLOTS_PER_EPOCH != 0
        // ensures updateJustification(s) == 
        //     updateJustificationCurrentEpoch(updateJustificationPrevEpoch(s))
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            updateJustificationCurrentEpoch(s).justification_bits[1..] == 
                (s.justification_bits)[1..|s.justification_bits|]
    {
        updateJustificationCurrentEpoch(updateJustificationPrevEpoch(s))
    }

    function updateJustificationAndFinalisation(s: BeaconState) : BeaconState
        requires s.slot % SLOTS_PER_EPOCH != 0
    {
        updateFinalisedCheckpoint(updateJustification(s))
    }

    /**
     *  Update related to the processing of current epoch.
     */
    function updateJustificationCurrentEpoch(s: BeaconState) : BeaconState 
        /** State's slot is not an Epoch boundary. */
        requires s.slot % SLOTS_PER_EPOCH != 0
        /** Justification bit are right-shifted and last two are not modified.
            Bit0 (new checkpoint) and Bit1 (previous checkpoint) may be modified.
         */
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            updateJustificationCurrentEpoch(s).justification_bits[1..] == 
                (s.justification_bits)[1..|s.justification_bits|]
    {
        if  get_current_epoch(s) <= GENESIS_EPOCH + 1 then 
            s 
        else 
            //  Get attestations for current epoch
            var matching_target_attestations := 
                get_matching_target_attestations(s, get_current_epoch(s));
            var b1 := get_attesting_balance(s, matching_target_attestations) as nat * 3 
                        >= get_total_active_balance(s) as nat * 2;
            var c := CheckPoint(get_current_epoch(s),
                                        get_block_root(s, get_current_epoch(s)));
            s.(
                current_justified_checkpoint := if b1 then c else s.current_justified_checkpoint,
                // previous_justified_checkpoint := s.current_justified_checkpoint,
                justification_bits := if b1 then s.justification_bits[0 := true] else s.justification_bits
            )
    }

    /**
     *  Update a state finalised checkpoint.
     *  @param  s   A state.
     *  @returns    The new state after updating the status of finalised_checkpoint.
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
    function updateFinalisedCheckpoint(s: BeaconState) : BeaconState
        ensures s.slot == updateFinalisedCheckpoint(s).slot
    {
        if get_current_epoch(s) <= GENESIS_EPOCH + 1 then 
            s 
        else 
            var bits : seq<bool> := s.justification_bits;
            var current_epoch := get_current_epoch(s);
            if (all(bits[1..4]) && current_epoch >= 3 && s.previous_justified_checkpoint.epoch  == current_epoch - 3) then 
                //  The 2nd/3rd/4th most recent epochs are justified, the 2nd using the 4th as source
                s.(finalised_checkpoint := s.previous_justified_checkpoint) 
            else if (all(bits[1..3]) && s.previous_justified_checkpoint.epoch == current_epoch - 2) then 
                // The 2nd/3rd most recent epochs are justified, the 2nd using the 3rd as source
                s.(finalised_checkpoint := s.previous_justified_checkpoint) 
            else if (all(bits[0..3]) && s.current_justified_checkpoint.epoch == current_epoch - 2) then 
                // The 1st/2nd/3rd most recent epochs are justified, the 1st using the 3rd as source
                s.(finalised_checkpoint := s.current_justified_checkpoint) 
            else if (all(bits[0..2]) && s.current_justified_checkpoint.epoch == current_epoch - 1) then 
                // The 1st/2nd most recent epochs are justified, the 1st using the 2nd as source
                s.(finalised_checkpoint := s.current_justified_checkpoint) 
            else
                s 
    } 
}