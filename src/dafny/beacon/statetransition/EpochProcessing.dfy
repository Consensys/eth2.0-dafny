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

include "../../utils/NonNativeTypes.dfy"
include "../../ssz/Constants.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../Helpers.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "EpochProcessing.s.dfy"
include "ProcessOperations.s.dfy"
include "../../utils/Eth2Types.dfy"

/**
 * State transition function for the Beacon Chain.
 */
module EpochProcessing {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NonNativeTypes
    import opened Constants
    import opened BeaconChainTypes
    import opened AttestationsTypes
    import opened BeaconHelpers
    import opened AttestationsHelpers
    import opened EpochProcessingSpec
    import opened ProcessOperationsSpec
    import opened Eth2Types

// # Attestations
//     previous_epoch_attestations: List[PendingAttestation, MAX_ATTESTATIONS * SLOTS_PER_EPOCH]
//     current_epoch_attestations: List[PendingAttestation, MAX_ATTESTATIONS * SLOTS_PER_EPOCH]
//     # Finality
//     justification_bits: Bitvector[JUSTIFICATION_BITS_LENGTH]  # Bit set for every recent justified epoch
//     previous_justified_checkpoint: Checkpoint  # Previous epoch snapshot
//     current_justified_checkpoint: Checkpoint
//     finalized_checkpoint: Checkpoint

    /**
     *  At epoch boundaries, update justifications, rewards, penalities,
     *  resgistry, slashing, and final updates.
     *
     *  @param  s   A beacon state.
     *  @returns    
     *  @todo       To be specified and implemented. currently returns s.
     */
    method process_epoch(s: BeaconState) returns (s' : BeaconState) 
        //  Make sure s.slot does not overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        //  And we should only execute this method when:
        requires (s.slot + 1) % SLOTS_PER_EPOCH == 0

        requires |s.validators| == |s.balances|

        /** Update justification and finalisation accodring to functional spec. */
        ensures s' == finalUpdates(updateFinalisedCheckpoint(updateJustification(s), s))

        /** Leaves some fields unchanged. */
        ensures s'.slot == s.slot
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
    {
        assert(s.slot as nat + 1 < 0x10000000000000000 as nat);
        s' := process_justification_and_finalization(s);
        // process_rewards_and_penalties(state)
        // process_registry_updates(state)
        // process_slashings(state)
        s' := process_final_updates(s');
        // assert(s' == finalUpdates(s2));
        // assume(s' == forwardStateToSlot(s, s.slot));
        // assume(s' == resolveStateRoot(s));
        return s';
    }

    /* */
    method process_rewards_and_penalties(s: BeaconState)  returns (s' : BeaconState)
        requires |s.validators| == |s.balances|
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        requires integer_square_root(get_total_active_balance(s)) > 1
        requires EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance(s)

        requires get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat
        requires 1 <= get_previous_epoch(s) <= get_current_epoch(s)

        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        requires get_current_epoch(s) != GENESIS_EPOCH ==> 
                    var (rewards,penalties) := get_attestation_deltas(s); 
                    forall v :: 0 <= v < |rewards| ==> s.balances[v] as nat + rewards[v] as nat < 0x10000000000000000;
        
        ensures  get_current_epoch(s) == GENESIS_EPOCH ==> s' == s
        ensures  get_current_epoch(s) != GENESIS_EPOCH ==> 
                    var (rewards,penalties) := get_attestation_deltas(s); 
                    s' == updateRewardsAndPenalties(s, rewards, penalties)
    {
        if get_current_epoch(s) == GENESIS_EPOCH {
            return s;
        }
        
        s' := s;
        var (rewards, penalties) := get_attestation_deltas(s');
        
        var i := 0;

        assert s' == updateRewardsAndPenalties(s, rewards[..i], penalties[..i]);
        //assume forall v :: 0 <= v < |rewards| ==> s.balances[v] as nat + rewards[v] as nat < 0x10000000000000000;

        while i < |s'.validators| //for index in range(len(state.validators)):
            invariant i <= |rewards| == |penalties|
            invariant |rewards| == |penalties| == |s.validators| == |s.balances| == |s'.validators| == |s'.balances|
            invariant |rewards[..i]| == |penalties[..i]| <= |s.validators| == |s.balances|
            //invariant forall v :: i <= v < |s.balances| ==> s'.balances[v] == s.balances[v]
            //invariant forall v :: 0 <= v < i ==> s'.balances[v] == if s.balances[v] + rewards[v] > penalties[v] then s.balances[v] + rewards[v] - penalties[v] else 0 as Gwei;
            //invariant forall v :: 0 <= v < i ==> s'.balances[v] == updateRewardsAndPenalties(s, rewards[..i], penalties[..i]).balances[v];
            //invariant forall v :: i <= v < |s.balances| ==> s'.balances[v] == s.balances[v] == updateRewardsAndPenalties(s, rewards[..i], penalties[..i]).balances[v];
            //invariant forall v :: 0 <= v < |s.balances| ==> s'.balances[v] == updateRewardsAndPenalties(s, rewards[..i], penalties[..i]).balances[v];
            //invariant forall v :: 0 <= v < |s.validators| ==> s'.validators[v] == updateRewardsAndPenalties(s, rewards[..i], penalties[..i]).validators[v];
            invariant i == |rewards[..i]|
            invariant s' == updateRewardsAndPenalties(s, rewards[..i], penalties[..i])
        {
            assert i < |rewards|;
            assert i < |s'.balances|;
            //assume s'.balances[i] as nat + rewards[i] as nat < 0x10000000000000000;
            
            s' := increase_balance(s', i as ValidatorIndex, rewards[i]);
            s' := decrease_balance(s', i as ValidatorIndex, penalties[i]);
            assert s'.balances[i] == if s.balances[i] + rewards[i] > penalties[i] then s.balances[i] + rewards[i] - penalties[i] else 0 as Gwei;
            assert forall v :: 0 <= v <= i ==> s'.balances[v] == if s.balances[v] + rewards[v] > penalties[v] then s.balances[v] + rewards[v] - penalties[v] else 0 as Gwei;
            i := i + 1;
        } 
        assert rewards[..i] == rewards;
        assert penalties[..i] == penalties;
        assert s' == updateRewardsAndPenalties(s, rewards, penalties);
    }

    // function rewardsAndPenalties(s: BeaconState) : BeaconState
    //     requires |s.validators| == |s.balances|
    //     requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
    //     requires integer_square_root(get_total_active_balance(s)) > 1
    //     requires EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance(s)

    //     requires get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat
    //     requires 1 <= get_previous_epoch(s) <= get_current_epoch(s)

    //     requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
    //     requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
    //     requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
    //     requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
    //     requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
    //     requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
    //     requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
    //     requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
    //     requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    // {
    //     if get_current_epoch(s) == GENESIS_EPOCH then   
    //         s
    //     else
    //         var (rewards, penalties) := get_attestation_deltas(s);
    //         updateRewardsAndPenalties(s, rewards, penalties)
    // }

    function updateRewardsAndPenalties(s: BeaconState, rewards: seq<Gwei>, penalties: seq<Gwei>): BeaconState
        requires |rewards| == |penalties| <= |s.validators| == |s.balances|
        requires forall i :: 0 <= i < |rewards| ==> s.balances[i] as nat + rewards[i] as nat < 0x10000000000000000

        
        ensures |s.balances| == |updateRewardsAndPenalties(s, rewards, penalties).balances|
        ensures |s.validators| == |updateRewardsAndPenalties(s, rewards, penalties).validators|
        ensures forall i :: |rewards| <= i < |s.balances| ==> updateRewardsAndPenalties(s, rewards, penalties).balances[i] == s.balances[i]
        ensures forall i :: 0 <= i < |rewards| ==> updateRewardsAndPenalties(s, rewards, penalties).balances[i] == if s.balances[i] + rewards[i] > penalties[i] then 
                                                        s.balances[i] + rewards[i] - penalties[i]
                                                    else    
                                                        0 as Gwei
        ensures forall i :: 0 <= i < |s.validators| ==> updateRewardsAndPenalties(s, rewards, penalties).validators[i] == s.validators[i]
        ensures updateRewardsAndPenalties(s, rewards, penalties) == s.(balances := updateRewardsAndPenalties(s, rewards, penalties).balances)

        decreases |rewards|, |penalties|
    {
        if |rewards| == 0 then s
        else
            var index := |rewards| - 1;
            // var s' := if rewards[|rewards|-1] > penalties[|penalties|-1] then 
            //                 //assume s.balances[index] as nat + rewards[|rewards|-1] as nat - penalties[|penalties|-1] as nat < 0x10000000000000000;
            //                 increase_balance(s, index as ValidatorIndex, rewards[|rewards|-1] - penalties[|penalties|-1])
            //             else 
            //                 //assume s.balances[index] as nat + penalties[|penalties|-1] as nat - rewards[|rewards|-1] as nat < 0x10000000000000000;
            //                 decrease_balance(s, index as ValidatorIndex, penalties[|penalties|-1] - rewards[|rewards|-1]);
            var s1 := increase_balance(s, index as ValidatorIndex, rewards[index]);
            assert s1.balances[index] == s.balances[index] + rewards[index];

            var s2 := decrease_balance(s1, index as ValidatorIndex, penalties[index]);
            assert s2.balances[index] == if s1.balances[index] > penalties[index] then s1.balances[index] - penalties[index] else 0 as Gwei;
            assert if s.balances[index] + rewards[index] > penalties[index] then s2.balances[index] == s.balances[index] + rewards[index] - penalties[index] 
                                                                         else s2.balances[index] == 0 as Gwei;

            //updateRewardsAndPenaltiesLemma(s, rewards, penalties);
            updateRewardsAndPenalties(s2, rewards[..index], penalties[..index])
            //s.(balances := increase_balance(s,get_validator_index(pk, d.data.pubkey),d.data.amount).balances)
    }

    // lemma updateRewardsAndPenaltiesLemma(s: BeaconState, rewards: seq<Gwei>, penalties: seq<Gwei>)
    //     requires |rewards| == |penalties| <= |s.validators| == |s.balances|
    //     requires forall i :: 0 <= i < |rewards| ==> s.balances[i] as nat + rewards[i] as nat < 0x10000000000000000

        
    //     ensures forall i :: 0 <= i < |rewards| ==> updateRewardsAndPenalties(s, rewards, penalties).balances[i] ==  if s.balances[i] + rewards[i] > penalties[i] then 
    //                                                     s.balances[i] + rewards[i] - penalties[i]
    //                                                 else    
    //                                                     0 as Gwei

    //     decreases |rewards|, |penalties|
        
    // {
    //     if |rewards| == 0 {}
    //     else {
            
    //         var index := |rewards| - 1;

    //         var s1 := increase_balance(s, index as ValidatorIndex, rewards[index]);
    //         assert s1.balances[index] == s.balances[index] + rewards[index];
    //         assert forall i :: 0 <= i < index ==> s1.balances[i] == s.balances[i];


    //         var s2 := decrease_balance(s1, index as ValidatorIndex, penalties[index]);
    //         assert s2.balances[index] == if s1.balances[index] > penalties[index] then s1.balances[index] - penalties[index] else 0 as Gwei;
    //         assert s2.balances[index] == if s.balances[index] + rewards[index] > penalties[index] then 
    //                                         s.balances[index] + rewards[index] - penalties[index] 
    //                                     else 
    //                                         0 as Gwei;
    //         assert forall i :: 0 <= i < index ==> s2.balances[i] == s.balances[i];
    //         assert index == |rewards[..index]|;


    //         assert updateRewardsAndPenalties(s, rewards, penalties) == updateRewardsAndPenalties(s2, rewards[..index], penalties[..index]);

    //         assert updateRewardsAndPenalties(s, rewards, penalties).balances[index] == if s.balances[index] + rewards[index] > penalties[index] then 
    //                                         s.balances[index] + rewards[index] - penalties[index] 
    //                                     else 
    //                                         0 as Gwei;            

    //         updateRewardsAndPenaltiesLemma(s2, rewards[..index], penalties[..index]);

    //         assert forall i :: 0 <= i < |rewards[..index]| ==> updateRewardsAndPenalties(s2, rewards[..index], penalties[..index]).balances[i] == if s2.balances[i] + rewards[i] > penalties[i] then 
    //                                                                 s2.balances[i] + rewards[i] - penalties[i]
    //                                                             else    
    //                                                                 0 as Gwei;

            

    //         assert forall i :: 0 <= i < |rewards[..index]| ==> updateRewardsAndPenalties(s2, rewards[..index], penalties[..index]).balances[i] == if s.balances[i] + rewards[i] > penalties[i] then 
    //                                                                 s.balances[i] + rewards[i] - penalties[i]
    //                                                             else    
    //                                                                 0 as Gwei;

            
    //         //assert forall i :: 0 <= i < index ==> s2.balances[i] + rewards[i] == s.balances[i] + rewards[i];
    //         //assert forall i :: 0 <= i < index ==> s2.balances[i] + rewards[i] - penalties[i] == s.balances[i] + rewards[i] - penalties[i];

    //         // assert forall i :: 0 <= i < index ==> if s.balances[i] + rewards[i] > penalties[i] then 
    //         //                                             updateRewardsAndPenalties(s, rewards, penalties).balances[i] == s.balances[i] + rewards[i] - penalties[i]
    //         //                                       else     
    //         //                                             updateRewardsAndPenalties(s, rewards, penalties).balances[i] == 0 as Gwei;



    //     }

    // }



    /**
     *  Rotate the attestations.
     *  @param  s   A state.
     *  @returns    `s` with attestations rotated.
     *
     *  @todo       This is a partial implementation capturing only
     *              the attestations updates.
     */
    method process_final_updates(s: BeaconState)  returns (s' : BeaconState)
        ensures s' == finalUpdates(s)
    {
        s' := s.(
            previous_epoch_attestations := s.current_epoch_attestations,
            current_epoch_attestations := []
        );
    }

    /**
     *  Update justification and finalisation status.
     *  
     *  @param  s   A beacon state.
     *  @returns    The state obtained after updating the justification/finalisation
     *              variables of `s`.
     *
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#justification-and-finalization}
     */
    method process_justification_and_finalization(s : BeaconState) returns (s' : BeaconState) 
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0

        requires |s.validators| == |s.balances|

        /** Computes the next state according to the functional specification. */
        ensures s' == updateFinalisedCheckpoint(updateJustification(s), s)
        
        /** Some components of the state are left unchanged. */
        ensures s'.slot == s.slot
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
    {
        //  epoch in state s is given by s.slot

        if get_current_epoch(s) <= GENESIS_EPOCH + 1 {
            //  Initial FFG checkpoint values have a `0x00` stub for `root`.
            //  Skip FFG updates in the first two epochs to avoid corner cases 
            //  that might result in modifying this stub.
            return s;   
        } else {
            assert(get_current_epoch(s) >= 2);
            //  Process justifications and finalisations
            var previous_epoch := get_previous_epoch(s);
            var current_epoch := get_current_epoch(s);
            assert(previous_epoch == current_epoch - 1);
            assert(previous_epoch as int * SLOTS_PER_EPOCH as int  < s.slot as int);
            assert(s.slot as int - (previous_epoch as int *  SLOTS_PER_EPOCH as int) 
                        <=  SLOTS_PER_HISTORICAL_ROOT as int );

            //  Process justifications and update justification bits
            // state.previous_justified_checkpoint = state.current_justified_checkpoint
            s' := s.(previous_justified_checkpoint := s.current_justified_checkpoint);

            //  Right-Shift of justification bits and initialise first to false
            s' := s'.(justification_bits := [false] + (s.justification_bits)[..JUSTIFICATION_BITS_LENGTH - 1]); 
            //  Determine whether ??
            assert(get_previous_epoch(s') <= previous_epoch <= get_current_epoch(s'));
            assert(s'.slot == s.slot);
            assert(previous_epoch as int * SLOTS_PER_EPOCH as int  < s'.slot as int);
            //  slot of previous epoch is not too far in the past
            assert(s'.slot as int - (previous_epoch as int *  SLOTS_PER_EPOCH as int) 
                        <=  SLOTS_PER_HISTORICAL_ROOT as int );
            assert(s'.block_roots == s.block_roots);
            assert(get_block_root(s', previous_epoch) == get_block_root(s, previous_epoch));
            assert(|s'.validators| == |s.validators|);
            //  Compute the attestations in s.previous_epoch_attestations that 
            //  vote for get_block_root(state, previous_epoch) i.e. the block root at the beginning
            //  of the previous epoch. (retrieve in the historical roots).
            var matching_target_attestations_prev := get_matching_target_attestations(s', previous_epoch) ;  
            //  @note should be the same as get_matching_target_attestations(s, previous_epoch) ;  
            // Previous epoch
            if get_attesting_balance(s', matching_target_attestations_prev) as uint128 * 3 >=       
                                get_total_active_balance(s') as uint128 * 2 {
                //  shift the justified checkpoint
                s' := s'.(current_justified_checkpoint := 
                            CheckPoint(previous_epoch,
                                        get_block_root(s', previous_epoch)));
                s' := s'.(justification_bits := s'.justification_bits[1 := true]);
            }
            assert(s'.slot == updateJustificationPrevEpoch(s).slot);
            assert(s'.current_justified_checkpoint == updateJustificationPrevEpoch(s).current_justified_checkpoint);
            assert(s'.previous_justified_checkpoint == updateJustificationPrevEpoch(s).previous_justified_checkpoint);
            assert(s' == updateJustificationPrevEpoch(s)); 

            ghost var s2 := s';
            //  Current epoch
            var matching_target_attestations_cur := get_matching_target_attestations(s', current_epoch) ;
            if get_attesting_balance(s', matching_target_attestations_cur) as nat * 3 >=       
                                    get_total_active_balance(s') as nat * 2 {
                //  shift the justified checkpoint
                s' := s'.(
                        justification_bits := s'.justification_bits[0 := true],
                        current_justified_checkpoint := 
                            CheckPoint(current_epoch,
                                        get_block_root(s', current_epoch)));
            }
            assert(s' == updateJustificationCurrentEpoch(s2));

            //  Process finalizations
            /*
             *  Epochs layout
             *
             *  | ............ | ........... | .......... | ........ |
             *  | ............ | ........... | .......... | ........ |
             *  e1             e2            e3           e4
             *  bit[3]        bit[2]        bit[1]        bit[0]
             *  
             *
             *  Python slice a[k:l] means: a[k] ... a[l -1]
             */
            ghost var s3 := s';

            var bits : seq<bool> := s'.justification_bits;
            // assume(s.previous_justified_checkpoint.epoch as nat + 3 < 0x10000000000000000 );
            //  if current_epoch == 2, s.previous_justified_checkpoint.epoch + 3 >= 3 so the 
            //  following condition is false. As a result we do not need to compute 
            //  s.previous_justified_checkpoint.epoch + 3 and can avoid a possible overflow.
            //  We assume here that the target language is such that AND conditions are evaluated ///   short-circuit i.e. unfolded as nested ifs
            //  
            //  The 2nd/3rd/4th most recent epochs are justified, the 2nd using the 4th as source
            if (all(bits[1..4]) && current_epoch >= 3 && s.previous_justified_checkpoint.epoch  == current_epoch - 3) {
                s' := s'.(finalised_checkpoint := s.previous_justified_checkpoint) ;
            }
            //  The 2nd/3rd most recent epochs are justified, the 2nd using the 3rd as source
            if (all(bits[1..3]) && s.previous_justified_checkpoint.epoch == current_epoch - 2) {
                s' := s'.(finalised_checkpoint := s.previous_justified_checkpoint) ;
            }
            //  The 1st/2nd/3rd most recent epochs are justified, the 1st using the 3rd as source
            if (all(bits[0..3]) && s.current_justified_checkpoint.epoch == current_epoch - 2) {
                s' := s'.(finalised_checkpoint := s.current_justified_checkpoint) ;
            }
            //  The 1st/2nd most recent epochs are justified, the 1st using the 2nd as source
            if (all(bits[0..2]) && s.current_justified_checkpoint.epoch == current_epoch - 1) {
                s' := s'.(finalised_checkpoint := s.current_justified_checkpoint) ;
            }
            assert(s' == updateFinalisedCheckpoint(s3, s));
            return s';
        }

        return s;
    }

}