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

include "../utils/Eth2Types.dfy"
include "../ssz/Constants.dfy"
include "./BeaconChainTypes.dfy"
include "./Attestations.dfy"
/**
 * Misc helpers.
 */
module BeaconHelpers {

    import opened Eth2Types
    import opened Constants
    import opened BeaconChainTypes
    import opened Attestations


    /**
     *  A simple lemma to bound integer division when divisor >= 1.
     */
    lemma divLess(x : nat , k : nat) 
        requires k >= 1
        ensures 0 <= x / k <= x 
    {   //  Thanks Dafny
    }

    /**
     *  The epoch of a slot.
     *
     *  @param  slot    A slot.
     *  @returns        The epoch of the slot.
     */
    function method compute_epoch_at_slot(slot: Slot) : Epoch
    {
        divLess(slot as nat, SLOTS_PER_EPOCH as nat);
        assert( 0 <= (slot as int)/ (SLOTS_PER_EPOCH as int) <= slot as int);
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
    {
        compute_epoch_at_slot(state.slot)
    }

    /**
     *  @param  state   A beacon state.
     *  @returns        Epoch before state's epoch and 0 is state's epoch is 0.
     */
    function method get_previous_epoch(state: BeaconState) : Epoch 
        ensures get_previous_epoch(state) <= get_current_epoch(state)
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
        requires (epoch as int *  SLOTS_PER_EPOCH as int)  < state.slot as int 
        requires state.slot - (epoch as int *  SLOTS_PER_EPOCH as int) as Slot  
                        <=  SLOTS_PER_HISTORICAL_ROOT
    { 
        var e := compute_start_slot_at_epoch(epoch);
        assert(e < state.slot);
        get_block_root_at_slot(state, e)
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
     *  @param  state   A beacon state.
     *  @param  epoch   An epoch which is either the state's epoch ior the previous one.
     *  @returns        The current (resp. previous) list of attestations if epoch is 
     *                  state's epoch (resp. epoch before state's epoch). 
     */
    function method  get_matching_source_attestations(state: BeaconState, epoch: Epoch) : seq<PendingAttestation>
        //  report -> meaning of i in (a, b)? seems to be closed interval ...
        requires get_previous_epoch(state) <= epoch <= get_current_epoch(state)
    {
        // assert epoch in (get_previous_epoch(state), get_current_epoch(state))
        // return state.current_epoch_attestations if epoch == get_current_epoch(state) else state.previous_epoch_attestations
        if epoch == get_current_epoch(state) then
            state.current_epoch_attestations
        else 
            state.previous_epoch_attestations
    }  

    /**
     *  @param  state   A beacon state.
     *  @param  epoch   An epoch which is either the state's epoch ior the previous one.
     *  @return         Filtered list of source attestations. Keep only attestations `a`
     *                  (votes) such that target(a) is the block root of slot `epoch`. 
     */
    function method get_matching_target_attestations(state: BeaconState, epoch: Epoch) : seq<PendingAttestation>
        requires (epoch as int * SLOTS_PER_EPOCH as int)  < state.slot as int 
        requires state.slot as int - (epoch as int *  SLOTS_PER_EPOCH as int) 
                        <=  SLOTS_PER_HISTORICAL_ROOT as int 
        requires get_previous_epoch(state) <= epoch <= get_current_epoch(state)
        ensures forall a :: a in get_matching_target_attestations(state, epoch) ==>
                    a.data.target.root == get_block_root(state, epoch)
    {
        var ax := get_matching_source_attestations(state, epoch);
        filterAttestations(ax, get_block_root(state, epoch))
    }

    /**
     *  Collect attestations with a specific target root.
     *
     *  @param  x   A list of attestations.
     *  @param  r   A root value (hash of a block). 
     */
    function method filterAttestations(x : seq<PendingAttestation>, r : Root) : seq<PendingAttestation>
        ensures forall a :: a in x && a.data.target.root == r <==> a in filterAttestations(x, r) 
        decreases x
    {
        if |x| == 0 then 
            []
        else if x[0].data.target.root == r then 
                [x[0]] + filterAttestations(x[1..], r)
             else 
                filterAttestations(x[1..], r)
    }

}