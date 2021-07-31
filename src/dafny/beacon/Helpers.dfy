/*
 * Copyright 2021 ConsenSys Software Inc.
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
include "../utils/NativeTypes.dfy"
include "../ssz/Constants.dfy"
include "./BeaconChainTypes.dfy"
include "attestations/AttestationsTypes.dfy"
include "validators/Validators.dfy"

/**
 * Misc helpers.
 */
module BeaconHelpers {

    import opened Eth2Types
    import opened NativeTypes
    import opened Constants
    import opened BeaconChainTypes
    import opened AttestationsTypes
    import opened Validators

    /**
     *  Check that a bitlist has all bits set to 1.
     *  @param      xs  
     *  @returns    
     */
    function method all(xs: seq<bool>) : bool
    {
        forall i :: 0 < i < |xs| ==> xs[i]
    }
    
    /**
     *  The epoch of a slot.
     *
     *  @param  slot    A slot.
     *  @returns        The epoch of the slot.
     */
    function method compute_epoch_at_slot(slot: Slot) : Epoch
        ensures compute_epoch_at_slot(slot) as int * SLOTS_PER_EPOCH as int < 0x10000000000000000
        ensures compute_epoch_at_slot(slot) * SLOTS_PER_EPOCH <= slot 
    {
        divLess(slot as nat, SLOTS_PER_EPOCH as nat);
        div2(slot as nat, SLOTS_PER_EPOCH as nat);
        assert(slot / SLOTS_PER_EPOCH <= slot);
        (slot / SLOTS_PER_EPOCH) as Epoch
    }

    /**
     *  Slot number at start of an epoch.
     *  
     *  @param  epoch   An epoch.
     *  @returns        The slot number at the start of `epoch`.
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#compute_start_slot_at_epoch}
     */
    function method compute_start_slot_at_epoch(epoch: Epoch) : Slot
        requires epoch as int * SLOTS_PER_EPOCH as int < 0x10000000000000000    // report
    {
        epoch * SLOTS_PER_EPOCH as Slot
    }

    /**
     *  @param  state   A beacon state.
     *  @returns        The epoch of the state's slot.
     */
    function method get_current_epoch(state: BeaconState) : Epoch 
        ensures get_current_epoch(state) as int * SLOTS_PER_EPOCH as int < 0x10000000000000000
        ensures get_current_epoch(state) * SLOTS_PER_EPOCH <= state.slot
        ensures state.slot % SLOTS_PER_EPOCH != 0 ==> 
            get_current_epoch(state) * SLOTS_PER_EPOCH < state.slot
        /** A useful proof that states that the slot that corresponds
            to the current epoch is within the range of the history 
            a block roots stored in the state.block_roots. */
        ensures state.slot - get_current_epoch(state) * SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT
    {
        compute_epoch_at_slot(state.slot)
    }

    /**
     *  @param  state   A beacon state.
     *  @returns        Epoch before state's epoch and 0 is state's epoch is 0.
     */
    function method get_previous_epoch(state: BeaconState) : Epoch 
        ensures get_previous_epoch(state) <= get_current_epoch(state)
        ensures get_previous_epoch(state) as int * SLOTS_PER_EPOCH as int < 0x10000000000000000
        ensures get_previous_epoch(state) * SLOTS_PER_EPOCH <= state.slot
        ensures get_current_epoch(state) == 0 ==>  get_current_epoch(state) == get_previous_epoch(state)
        ensures get_current_epoch(state) > 0 ==> get_current_epoch(state) - 1 == get_previous_epoch(state) 
        /** A useful proof that states that the slot that corresponds
            to the previous epoch is within the range of the history 
            a block roots stored in the state.block_roots. */
        ensures state.slot - get_previous_epoch(state) * SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT

    {
        var e := get_current_epoch(state);
        //  max(0, e - 1)
        if e > 0 then e - 1 else e 
    }

    /**
     *  The block root at the start of an epoch.
     *
     *  @param  state   A beacon state.
     *  @param  epoch   A recent epoch (must be tracked in state.block_roots).
     *  @returns        The block root at the beginning of epoch. 
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#get_block_root}
     *  
     *  Given an epoch, start slot is epoch * SLOTS_PER_EPOCH.
     *  Only the last SLOTS_PER_HISTORICAL_ROOT block roots are stored in the state.
     *  To be able to retrieve the block root, the slot of epoch must be recent
     *  i.e state.slot - epoch * SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT.
     */
    function method get_block_root(state: BeaconState, epoch: Epoch) : Root  
        requires epoch as nat * SLOTS_PER_EPOCH as nat < 0x10000000000000000 
        requires epoch * SLOTS_PER_EPOCH < state.slot  
        requires state.slot - epoch * SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
    { 
        var slot_of_epoch := compute_start_slot_at_epoch(epoch);  
        assert(slot_of_epoch == epoch * SLOTS_PER_EPOCH);
        assert(slot_of_epoch < state.slot);
        get_block_root_at_slot(state, slot_of_epoch)
    }
    
    /**
     *  The block root at the start of a given (recent) slot.
     *
     *  @param  state   A beacon state.
     *  @param  slot    A recent slot (must be tracked in state.block_roots).
     *  @returns        The block root at (a recent) slot. 
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#get_block_root_at_slot}
     *  
     */
    function method get_block_root_at_slot(state: BeaconState, slot: Slot) : Root
        requires slot < state.slot 
        requires state.slot - slot <=  SLOTS_PER_HISTORICAL_ROOT
    {
        state.block_roots[slot % SLOTS_PER_HISTORICAL_ROOT]
    }

    /**
     *  Count instances of d in a list of eth1_data.
     */
     function method count_eth1_data_votes(l: ListOfEth1Data, d: Eth1Data) : nat
    {
        if |l| == 0 then 0
        else 
            if (l[0] == d) then 1 + count_eth1_data_votes(l[1..], d)
            else count_eth1_data_votes(l[1..], d)
    }
    
    /**
     *  A simple lemma to bound integer division when divisor >= 1.
     */
    lemma divLess(x : nat , k : nat) 
        requires k >= 1
        ensures 0 <= x / k <= x 
    {   //  Thanks Dafny
    }

    /**
     *  ( x  /  k ) * k is less than or equal to x.
     */
    lemma div2(x : nat, k : nat) 
        requires k >= 1 
        ensures ( x / k ) * k <= x
    {
    }
    

}