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
include "../utils/NativeTypes.dfy"
include "../ssz/Constants.dfy"
include "./BeaconChainTypes.dfy"
include "attestations/AttestationsTypes.dfy"
include "./Validators.dfy"

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
     *  A simple lemma to bound integer division when divisor >= 1.
     */
    lemma divLess(x : nat , k : nat) 
        requires k >= 1
        ensures 0 <= x / k <= x 
    {   //  Thanks Dafny
    }

    lemma div2(x : nat, k : nat) 
        requires k >= 1 
        ensures ( x / k ) * k <= x
    {
    }

   
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
        requires epoch as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
        requires epoch *  SLOTS_PER_EPOCH   < state.slot  
        requires state.slot  - epoch  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
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
     *  @param  state   A beacon state.
     *  @param  epoch   An epoch which is either the state's epoch ior the previous one.
     *  @returns        The current (resp. previous) list of attestations if epoch is 
     *                  state's epoch (resp. epoch before state's epoch). 
     *  @note           The function name is misleading as it seems to be a counter-part
     *                  or symmetric of `get_matching_target_attestations` but it is not.
     *                  Moreover it does not perform any matching as the name indicates,
     *                  and the matching/filtering is done in `get_matching_target_attestations`.
     *                  A better name may be `get_attestations_at_epoch`.
     *  @note           An even better solution would be to remove this function 
     *                  and directly `use state.current_epoch_attestations` or 
     *                  `state.previous_epoch_attestations` in the callers.
     */
    function method  get_matching_source_attestations(state: BeaconState, epoch: Epoch) : seq<PendingAttestation>
        //  report -> meaning of i in (a, b)? seems to be closed interval ...
        requires get_previous_epoch(state) <= epoch <= get_current_epoch(state)
        ensures |get_matching_source_attestations(state, epoch)| < 0x10000000000000000
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
     *  @param  epoch   An epoch which is either the state's epoch or the previous one.
     *  @returns        Attestations at epoch with a target that is the block root
     *                  recorded for that epoch.         
     *
     */
    function method get_matching_target_attestations(state: BeaconState, epoch: Epoch) : seq<PendingAttestation>
        requires epoch as nat *  SLOTS_PER_EPOCH as nat  <  state.slot as nat
        requires state.slot - epoch *  SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT 
        requires 1 <= get_previous_epoch(state) <= epoch <= get_current_epoch(state)
        
        ensures |get_matching_target_attestations(state, epoch)| < 0x10000000000000000
        ensures forall a :: a in get_matching_target_attestations(state, epoch) ==>
                    a.data.target.root == get_block_root(state, epoch)

        ensures var e := get_previous_epoch(state);
            epoch == e ==> 
                get_matching_target_attestations(state, e) == 
                filterAttestations(state.previous_epoch_attestations, get_block_root(state, e))
        ensures var e := get_current_epoch(state);
            epoch == e ==> 
                get_matching_target_attestations(state, e) == 
                filterAttestations(state.current_epoch_attestations, get_block_root(state, e))
        decreases epoch //  seems needed to prove last two post-conds
    {
        //  Get attestattions at epoch as recorded in state (previous epoch or current epoch).
        var ax := get_matching_source_attestations(state, epoch);
        //  Collect attestations for (i.e. with target equal to) block root at epoch
        filterAttestations(ax, get_block_root(state, epoch))
    }

    function method get_attesting_balance(state: BeaconState, attestations: seq<PendingAttestation>) : Gwei 
        requires |attestations| < 0x10000000000000000
    // """
    // Return the combined effective balance of the set of unslashed validators participating in ``attestations``.
    // Note: ``get_total_balance`` returns ``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum to avoid divisions by zero.
    // """
    {
        // get_total_balance(state, get_unslashed_attesting_indices(state, attestations))
        |attestations| as Gwei 
    }

    // function method get_unslashed_attesting_indices(state: BeaconState,
                                    // attestations: seq<PendingAttestation>): set<ValidatorIndex>
    // output = set()  # type: Set[ValidatorIndex]
    // for a in attestations:
    //     output = output.union(get_attesting_indices(state, a.data, a.aggregation_bits))
    // return set(filter(lambda index: not state.validators[index].slashed, output))
    // {
    //     attestations 
    // }

    // function method  get_total_balance(state: BeaconState, indices: set<ValidatorIndex>) : Gwei
    // """
    // Return the combined effective balance of the ``indices``.
    // ``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum to avoid divisions by zero.
    // Math safe up to ~10B ETH, afterwhich this overflows uint64.
    // """
    // {
        // return Gwei(max(EFFECTIVE_BALANCE_INCREMENT, sum([state.validators[index].effective_balance for index in indices])));
        //  for now we return the size of indices
        // |indices| as Gwei 
    // }
    

    function method get_total_active_balance(state: BeaconState) : Gwei
        // requires |state.validators| < 0x10000000000000000
    // """
    // Return the combined effective balance of the active validators.
    // Note: ``get_total_balance`` returns ``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum to avoid divisions by zero.
    // """
    {
        // get_total_balance(state, set(get_active_validator_indices(state, get_current_epoch(state))))
        assert(|state.validators| < 0x10000000000000000);
        |state.validators| as uint64
    }

    /**
     *  Collect attestations with a specific target.
     *
     *  @param  x   A list of attestations.
     *  @param  br  A root value (hash of a block or block root). 
     *  @returns    The subset of `xl` that corresponds to attestation with target `r`.
     */
    function method filterAttestations(xl : seq<PendingAttestation>, br : Root) : seq<PendingAttestation>
        ensures |filterAttestations(xl, br)| <= |xl|
        ensures forall a :: a in xl && a.data.target.root == br <==> a in filterAttestations(xl, br) 
        decreases xl
    {
        if |xl| == 0 then 
            []
        else 
            (if xl[0].data.target.root == br then [xl[0]] else [])
                + filterAttestations(xl[1..], br)
    }

}