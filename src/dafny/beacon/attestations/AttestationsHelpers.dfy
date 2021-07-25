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

include "../../ssz/Constants.dfy"
include "../../utils/SetHelpers.dfy"
include "../../utils/MathHelpers.dfy"
include "../../utils/NativeTypes.dfy"
include "AttestationsTypes.dfy"
include "../../utils/Eth2Types.dfy"
include "../BeaconChainTypes.dfy"
include "../Helpers.dfy"

/**
 *  Provide datatype for fork choice rule (and LMD-GHOST).
 *
 *  Some properties of validators/attestations
 *  P1: attestations must be well-formed (see ForkChoiceHelpers, isValidAttestarions)
 *  P2: each validator is assigned to one committee per epoch
 *  P3: each HONEST validator attests at most oncd per epoch.
 */
module AttestationsHelpers {

    import opened Constants
    import opened Eth2Types
    import opened NativeTypes
    import opened SetHelpers
    import opened MathHelpers
    import opened AttestationsTypes
    import opened BeaconChainTypes
    import opened BeaconHelpers


    /**
     *  The number of attestations for a pair of checkpoints.
     *  
     *  @param  xa  The known list of attestations (votes).
     *  @param  src A checkpoint.
     *  @param  tgt A checkpoint.
     *  @returns    The number of votes for src --> tgt in `xa`.
     */
    function method countAttestationsForLink(xa : seq<PendingAttestation>, src : CheckPoint, tgt: CheckPoint) : nat
        ensures countAttestationsForLink(xa, src, tgt) <= |xa|
        decreases xa
    {
        if |xa| == 0 then 
            0
        else 
            (if xa[0].data.source == src && xa[0].data.target == tgt then 
                1

            else 
                0
            ) + countAttestationsForLink(xa[1..], src, tgt)
    }

    /**
     *  Collect set of indices of validators attesting a link.
     *
     *  @param  xa      A seq of attestations.
     *  @param  src     The source checkpoint of the link.
     *  @param  tgt     The target checkpoint of the link.
     *  @returns        The set of validators's indices that vote for (src. tgt) in `xa`. 
     */
     function collectValidatorsAttestatingForLink(xa : seq<PendingAttestation>, src : CheckPoint, tgt: CheckPoint) : set<nat>
        ensures forall e :: e in collectValidatorsAttestatingForLink(xa, src, tgt) ==>
            e < MAX_VALIDATORS_PER_COMMITTEE as nat
        ensures |collectValidatorsAttestatingForLink(xa, src, tgt)| <= MAX_VALIDATORS_PER_COMMITTEE as nat
        decreases xa
    {
        if |xa| == 0 then 
            { }
        else 
            unionCardBound(trueBitsCount(xa[0].aggregation_bits),
                collectValidatorsAttestatingForLink(xa[1..], src, tgt), MAX_VALIDATORS_PER_COMMITTEE as nat);
            (if xa[0].data.source == src && xa[0].data.target == tgt then 
                trueBitsCount(xa[0].aggregation_bits)
            else 
                {}
            ) + collectValidatorsAttestatingForLink(xa[1..], src, tgt)
    }

    /**
     *  Collect set of indices of validators attesting a link to a given target.
     *
     *  @param  xa      A seq of attestations.
     *  @param  tgt     The target checkpoint of the link.
     *  @returns        The set of validators's indices that vote for (_. tgt) in `xa`. 
     */
    function collectValidatorsIndicesAttestatingForTarget(xa : seq<PendingAttestation>, tgt: CheckPoint) : set<nat>
        ensures forall e :: e in collectValidatorsIndicesAttestatingForTarget(xa, tgt) ==>
            e < MAX_VALIDATORS_PER_COMMITTEE as nat
        ensures |collectValidatorsIndicesAttestatingForTarget(xa, tgt)| <= MAX_VALIDATORS_PER_COMMITTEE as nat
        decreases xa
    {
        if |xa| == 0 then 
            { }
        else 
            unionCardBound(trueBitsCount(xa[0].aggregation_bits),
                collectValidatorsIndicesAttestatingForTarget(xa[1..], tgt), MAX_VALIDATORS_PER_COMMITTEE as nat);
            (if xa[0].data.target == tgt then 
                trueBitsCount(xa[0].aggregation_bits)
            else 
                {}
            ) + collectValidatorsIndicesAttestatingForTarget(xa[1..], tgt)
    }

    /**
     *  Collect the set of indices for which xb[i] is true.
     *  
     *  @param  xb  A sequence of bools.
     *  @returns    The number of elements that are true in `xb`.
     */
    function trueBitsCount(xb : seq<bool>) : set<nat> 
        ensures |trueBitsCount(xb)| <= |xb|
        ensures forall i :: i in trueBitsCount(xb) <==> 0 <= i < |xb| && xb[i]
        decreases xb
    {
        if |xb| == 0 then 
            {}
        else 
            (if xb[|xb| - 1] then { |xb| - 1 } else {}) + trueBitsCount(xb[..|xb| - 1])
    }

    /**
     *  The set of validators attesting to a target is larger than the set 
     *  of validators attesting to a link with that target. 
     *
     *  @param  xa      A seq of attestations.
     *  @param  src     The source checkpoint of the link.
     *  @param  tgt     The target checkpoint of the link.
     */
    lemma {:induction xa} attForTgtLargerThanLinks(xa : seq<PendingAttestation>, src : CheckPoint, tgt: CheckPoint)
        ensures collectValidatorsAttestatingForLink(xa, src, tgt) <= collectValidatorsIndicesAttestatingForTarget(xa, tgt) 
        ensures |collectValidatorsAttestatingForLink(xa, src, tgt)| <= |collectValidatorsIndicesAttestatingForTarget(xa, tgt)| 
    {
        assert(collectValidatorsAttestatingForLink(xa, src, tgt) <= collectValidatorsIndicesAttestatingForTarget(xa, tgt) );
        cardIsMonotonic(collectValidatorsAttestatingForLink(xa, src, tgt), collectValidatorsIndicesAttestatingForTarget(xa, tgt));
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
    function method get_matching_source_attestations(state: BeaconState, epoch: Epoch) : seq<PendingAttestation>
        //  report? -> meaning of i in (a, b)? seems to be closed interval ...
        requires get_previous_epoch(state) <= epoch <= get_current_epoch(state)
        ensures |get_matching_source_attestations(state, epoch)| < 0x10000000000000000

        // this property will be assumed for the moment
        //ensures forall i :: 0 <= i < |get_matching_source_attestations(state, epoch)| 
        //    ==> get_matching_source_attestations(state, epoch)[i].data.index 
        //        < get_committee_count_per_slot(state, compute_epoch_at_slot(get_matching_source_attestations(state, epoch)[i].data.slot)) <= TWO_UP_6
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
     *  @note           This function does not check the epoch of the source attestation.
     *                  As a result if the seq of attestations in   
     *                  `state.previous/current_epoch_attestations` contains the same 
     *                  block root at different epochs, all the attestations will be collect.
     *                  However the following note seems to suggest that this cannot happen.
     *
     *  @note           From the eth2.0 specs: When processing attestations, we already only *                  accept attestations that have the correct Casper FFG source checkpoint 
     *                  (specifically, the most recent justified checkpoint that the chain 
     *                  knows about). The goal of this function is to get all attestations 
     *                  that have a correct Casper FFG source. Hence, it can safely just 
     *                  return all the PendingAttestations for the desired epoch 
     *                  (current or previous).
     *  @note           The claim "it can safely just return all the PendingAttestations for 
     *                  the desired epoch (current or previous)." is valid only if all the 
     *                  attestations in `state.previous/current_epoch_attestations`
     *                  are well-formed. 
     *  @todo           We should add this constraint to the pre-conditions of this function.
     */
    function method get_matching_target_attestations(state: BeaconState, epoch: Epoch) : seq<PendingAttestation>
        requires epoch as nat *  SLOTS_PER_EPOCH as nat  <  state.slot as nat
        requires state.slot - epoch *  SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT 
        requires 1 <= get_previous_epoch(state) <= epoch <= get_current_epoch(state)
        // requires 

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

    function method get_matching_head_attestations(state: BeaconState, epoch: Epoch) : seq<PendingAttestation>
        requires epoch as nat *  SLOTS_PER_EPOCH as nat  <  state.slot as nat
        requires state.slot - epoch *  SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT 
        requires 1 <= get_previous_epoch(state) <= epoch <= get_current_epoch(state)
        
        ensures |get_matching_head_attestations(state, epoch)| < 0x10000000000000000
        ensures forall a :: a in get_matching_head_attestations(state, epoch) ==>
                    a.data.slot < state.slot &&
                    state.slot - a.data.slot <= SLOTS_PER_HISTORICAL_ROOT &&
                    a.data.beacon_block_root == get_block_root_at_slot(state, a.data.slot)

    {
        var ax := get_matching_target_attestations(state, epoch);
        filterAttestationsyy(ax, state)
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

    function method get_unslashed_attesting_indices(s: BeaconState, attestations: seq<PendingAttestation>): set<ValidatorIndex>
        //requires forall i :: 0 <= i < |attestations| ==> attestations[i].data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(attestations[i].data.slot)) <= TWO_UP_6
        requires forall a :: a in attestations ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in attestations ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 

        ensures forall i  :: i in get_unslashed_attesting_indices(s, attestations) ==> i as nat < |s.validators|
    {
        if |attestations| == 0 then {}
        else 
            // output = set()  # type: Set[ValidatorIndex]
            // for a in attestations:
            //      output = output.union(get_attesting_indices(state, a.data, a.aggregation_bits))
            //      return set(filter(lambda index: not state.validators[index].slashed, output))       
            var indices := get_attesting_indices(s, attestations[0].data, attestations[0].aggregation_bits);
            var unslashed_indices := unslashed_attesting_indices_helper(s,indices);
            unslashed_indices + get_unslashed_attesting_indices(s, attestations[1..])
    }
    
    function method unslashed_attesting_indices_helper(s: BeaconState, indices: set<ValidatorIndex>): set<ValidatorIndex>
        requires forall i  :: i in indices ==> i as nat < |s.validators|
        ensures forall i  :: i in unslashed_attesting_indices_helper(s, indices) ==> i as nat < |s.validators|
    {
       if indices == {} then {}
       else 
            var x := PickIndex(indices);
            if !s.validators[x].slashed then {x} + unslashed_attesting_indices_helper(s, indices - {x})
            else unslashed_attesting_indices_helper(s, indices - {x})
    }


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


    function method get_total_balance_seq(s: BeaconState, indices: seq<ValidatorIndex>) : Gwei
        requires forall i :: 0 <= i < |indices| ==> indices[i] as nat < |s.validators|
        ensures EFFECTIVE_BALANCE_INCREMENT <= get_total_balance_seq(s, indices)

    {
        max(EFFECTIVE_BALANCE_INCREMENT as nat, get_total_balance_seq_helper(s, indices) as nat) as Gwei
    }

    function method get_total_balance_seq_helper(s: BeaconState, indices: seq<ValidatorIndex>) : Gwei
        requires forall i :: 0 <= i < |indices| ==> indices[i] as nat < |s.validators|
    {
        if |indices| == 0 then 0 as Gwei
        else
            assume s.validators[indices[0]].effective_balance as nat + get_total_balance_seq_helper(s, indices[1..]) as nat < 0x10000000000000000;
            s.validators[indices[0]].effective_balance + get_total_balance_seq_helper(s, indices[1..]) 
    }

    function method get_total_balance(s: BeaconState, indices: set<ValidatorIndex>) : Gwei
        requires forall i : ValidatorIndex :: i in indices ==> i as nat < |s.validators|

    {
        max(EFFECTIVE_BALANCE_INCREMENT as nat, get_total_balance_helper(s, indices) as nat) as Gwei
    }

    function method get_total_balance_helper(s: BeaconState, indices: set<ValidatorIndex>) : Gwei
        requires forall i : ValidatorIndex :: i in indices ==> i as nat < |s.validators|
    {
        if |indices| == 0 then 0 as Gwei
        else
            var y := PickIndex(indices);
            assume s.validators[y].effective_balance as nat + get_total_balance_helper(s, indices - {y}) as nat < 0x10000000000000000;
            s.validators[y].effective_balance + get_total_balance_helper(s, indices - {y}) 
    }

    function method PickIndex(s: set<ValidatorIndex>): ValidatorIndex
        requires s != {}
    {
        HasMinimum(s);
        var z :| z in s && forall y :: y in s ==> z as nat <= y as nat;
        z
    }

    lemma HasMinimum(s: set<ValidatorIndex>)
        requires s != {}
        ensures exists z :: z in s && forall y :: y in s ==> z <= y
        // Ref: https://stackoverflow.com/questions/51207795/the-hilbert-epsilon-operator
    {
        var z :| z in s;
        if s == {z} {
            // the mimimum of a singleton set is its only element
        } else if forall y :: y in s ==> z <= y {
            // we happened to pick the minimum of s
        } else {
            // s-{z} is a smaller, nonempty set and it has a minimum
            var s' := s - {z};
            HasMinimum(s');
            var z' :| z' in s' && forall y :: y in s' ==> z' <= y;
            // the minimum of s' is the same as the miminum of s
            forall y | y in s
            ensures z' <= y
            {
            if
            case y in s' =>
                assert z' <= y;  // because z' in minimum in s'
            case y == z =>
                var k :| k in s && k < z;  // because z is not minimum in s
                assert k in s';  // because k != z
            }
        }
    }

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

    function method get_total_active_balance_full(s: BeaconState) : Gwei
        // requires |state.validators| < 0x10000000000000000
        ensures EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s) 
    // """
    // Return the combined effective balance of the active validators.
    // Note: ``get_total_balance`` returns ``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum to avoid divisions by zero.
    // """
    {
        get_total_balance_seq(s, get_active_validator_indices(s.validators, get_current_epoch(s)))
    }

    // def get_attesting_indices(state: BeaconState,
    //                       data: AttestationData,
    //                       bits: Bitlist[MAX_VALIDATORS_PER_COMMITTEE]) -> Set[ValidatorIndex]:
    // """
    // Return the set of attesting indices corresponding to ``data`` and ``bits``.
    // """
    // committee = get_beacon_committee(state, data.slot, data.index)
    // return set(index for i, index in enumerate(committee) if bits[i])
    function method get_attesting_indices(s: BeaconState, data: AttestationData, bits: AggregationBits) : set<ValidatorIndex>
        requires TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(data.slot)) <= TWO_UP_6
        requires 0 < |get_beacon_committee(s, data.slot, data.index)| == |bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat

        ensures forall i :: i in get_attesting_indices(s, data, bits) ==> i as nat < |s.validators|
    {
        var committee := get_beacon_committee(s, data.slot, data.index);
        assert |committee| <= |bits|;
        assert forall e :: e in committee ==> e as nat < |s.validators|;
        filterIndicesxx(committee, bits)

    }

    function method filterIndicesxx(sv : seq<ValidatorIndex>, bits: AggregationBits) : set<ValidatorIndex>
        requires |sv| <= |bits|
        ensures |filterIndicesxx(sv, bits)| <= |sv|
        ensures forall i :: 0 <= i < |sv| && bits[i] ==> sv[i] in filterIndicesxx(sv, bits)
        ensures |filterIndicesxx(sv, bits)| <= |sv|
        ensures forall i :: i in filterIndicesxx(sv, bits) ==> i in sv
        decreases sv
    {
        if |sv| == 0 then 
            {}
        else 
            (if bits[0] then {sv[0]} else {})
                + filterIndicesxx(sv[1..], bits[1..])
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

    function method filterAttestationsyy(xl : seq<PendingAttestation>, s : BeaconState) : seq<PendingAttestation>
        ensures |filterAttestationsyy(xl, s)| <= |xl|
        ensures forall a :: a in xl && 
                            a.data.slot < s.slot &&
                            s.slot - a.data.slot <= SLOTS_PER_HISTORICAL_ROOT &&
                            a.data.beacon_block_root == get_block_root_at_slot(s, a.data.slot) <==> a in filterAttestationsyy(xl, s) 
        decreases xl
    {
        if |xl| == 0 then 
            []
        else 
            (if xl[0].data.slot < s.slot &&
                s.slot - xl[0].data.slot <= SLOTS_PER_HISTORICAL_ROOT &&
                xl[0].data.beacon_block_root == get_block_root_at_slot(s, xl[0].data.slot) then [xl[0]] else [])

                + filterAttestationsyy(xl[1..], s)

    }
   
}
