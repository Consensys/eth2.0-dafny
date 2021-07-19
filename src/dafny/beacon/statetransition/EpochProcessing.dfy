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
include "../../utils/MathHelpers.dfy"

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
    import opened MathHelpers

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
     *  @note       ?? Mention any simplifcations
     */
    method process_epoch(s: BeaconState) returns (s' : BeaconState) 
        //  Make sure s.slot does not overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        //  And we should only execute this method when:
        requires (s.slot + 1) % SLOTS_PER_EPOCH == 0

        requires |s.validators| == |s.balances|
        //requires if get_current_epoch(s) > GENESIS_EPOCH + 1 then  get_previous_epoch(s) >= s.finalised_checkpoint.epoch else true
        //requires if get_current_epoch(s) != GENESIS_EPOCH then  EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance(s) else true
        //requires if get_current_epoch(s) != GENESIS_EPOCH then  1 <= get_previous_epoch(s) else true // <= get_current_epoch(s)
        requires forall a :: a in s.previous_epoch_attestations ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6 
        requires forall a :: a in s.previous_epoch_attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in s.previous_epoch_attestations ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat
      
        // /** Leaves some fields unchanged. */
        ensures s'.slot == s.slot
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures |s'.validators| == |s'.balances|
        ensures s' == updateEpoch(s)
    {
        assert(s.slot as nat + 1 < 0x10000000000000000 as nat);
        s' := process_justification_and_finalization(s);

        assert s' == updateFinalisedCheckpoint(updateJustification(s), s);
        assert s' == updateJustificationAndFinalisation(s);
        ghost var s1 := s';

        assert s'.previous_epoch_attestations == s.previous_epoch_attestations;
        assert s'.validators == s.validators;
        
        assert forall a :: a in s'.previous_epoch_attestations ==> a.data.index < get_committee_count_per_slot(s', compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6 ;
        assert forall a :: a in s'.previous_epoch_attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s'.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat ;
        assert forall a :: a in s'.previous_epoch_attestations ==> 0 < |get_beacon_committee(s', a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat;

        s' := process_rewards_and_penalties(s');

        assert s' == updateRAndP(updateJustificationAndFinalisation(s));
        
        // process_registry_updates(state)

        assert |s'.validators| == |s'.balances| == |s.validators|;
        s' := process_slashings(s');
        assert s' == updateSlashings(updateRAndP(updateJustificationAndFinalisation(s)));

        s' := process_eth1_data_reset(s');
        assert s' == updateEth1DataReset(updateSlashings(updateRAndP(updateJustificationAndFinalisation(s))));

        assert |s'.validators| == |s'.balances| == |s.validators|;
        s' := process_effective_balance_updates(s');
        assert s' == updateEffectiveBalance(updateEth1DataReset(updateSlashings(updateRAndP(updateJustificationAndFinalisation(s)))));

        s' := process_slashings_reset(s');
        assert s' == updateSlashingsReset(updateEffectiveBalance(updateEth1DataReset(updateSlashings(updateRAndP(updateJustificationAndFinalisation(s))))));

        s' := process_randao_mixes_reset(s');
        assert s' == updateRandaoMixes(updateSlashingsReset(updateEffectiveBalance(updateEth1DataReset(updateSlashings(updateRAndP(updateJustificationAndFinalisation(s)))))));

        s' := process_historical_roots_update(s');
        assert s' == updateHistoricalRoots(updateRandaoMixes(updateSlashingsReset(updateEffectiveBalance(updateEth1DataReset(updateSlashings(updateRAndP(updateJustificationAndFinalisation(s))))))));

        s' := process_participation_record_updates(s');
        assert s' == updateParticipationRecords(updateHistoricalRoots(updateRandaoMixes(updateSlashingsReset(updateEffectiveBalance(updateEth1DataReset(updateSlashings(updateRAndP(updateJustificationAndFinalisation(s)))))))));

        //      s' := process_final_updates(s');
        // assert(s' == finalUpdates(s2));
        // assume(s' == forwardStateToSlot(s, s.slot));
        // assume(s' == resolveStateRoot(s));
        assert s' == updateEpoch(s);
        return s';
    }
    
    /* */
    method process_rewards_and_penalties(s: BeaconState)  returns (s' : BeaconState)
        requires |s.validators| == |s.balances|
        //requires if get_current_epoch(s) > GENESIS_EPOCH + 1 then  get_previous_epoch(s) >= s.finalised_checkpoint.epoch else true
        //requires if get_current_epoch(s) != GENESIS_EPOCH then  EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance(s) else true
       // requires if get_current_epoch(s) != GENESIS_EPOCH then  1 <= get_previous_epoch(s) else true // <= get_current_epoch(s)

        requires forall a :: a in s.previous_epoch_attestations ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6 
        requires forall a :: a in s.previous_epoch_attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in s.previous_epoch_attestations ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
        
        ensures s' == updateRAndP(s)
    {
        // Simplify edge cases
        if get_current_epoch(s) <= GENESIS_EPOCH + 1 { 
            return s;
        }
        
        s' := s;
        assume get_previous_epoch(s) >= s.finalised_checkpoint.epoch;
        assert EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s); 
        assert 1 <= get_previous_epoch(s);
        //assume integer_square_root(get_total_active_balance(s)) > 1;
        var (rewards, penalties) := get_attestation_deltas(s');
        
        var i := 0;

        
        assert s' == updateRewardsAndPenalties(s, rewards[..i], penalties[..i]);
        assume forall v :: 0 <= v < |rewards| ==> s.balances[v] as nat + rewards[v] as nat < 0x10000000000000000;
        

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
            //invariant s' == updateRewardsAndPenaltiesWrapper(s)
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
        assert s' == updateRAndP(s);

    }

    // function updateRegistry(s: BeaconState): BeaconState
    //     requires |s.validators| == |s.balances|
    //     //ensures updateRegistry(s) == updateEligibilityAndEjectionsHelper(s, |s.validators|)
    

    function updateEligibility(s: BeaconState): BeaconState
        requires |s.validators| == |s.balances|
        ensures updateEligibility(s) == updateEligibilityHelper(s, |s.validators|)
    {
        updateEligibilityHelper(s, |s.validators|)
    }

    function updateEligibilityHelper(s: BeaconState, len: nat): BeaconState
        requires len <= |s.validators| == |s.balances|
        ensures |updateEligibilityHelper(s, len).validators| == |s.validators|
        ensures updateEligibilityHelper(s, len) == s.(validators := updateEligibilityHelper(s, len).validators)
        ensures forall v :: len <= v < |s.validators| ==> updateEligibilityHelper(s, len).validators[v] == s.validators[v]
        ensures forall v :: 0 <= v < len ==> 
            updateEligibilityHelper(s, len).validators[v] == 
                    if is_eligible_for_activation_queue(s.validators[v])
                        then s.(validators := s.validators[v := s.validators[v].(activation_eligibility_epoch := get_current_epoch(s) + 1)]).validators[v]
                        else s.validators[v]
        decreases len
    {
        if len == 0 then s
        else
            var i := len -1;
            assert i < |s.validators|;
            var s1 := if is_eligible_for_activation_queue(s.validators[i])
                    then s.(validators := s.validators[i := s.validators[i].(activation_eligibility_epoch := get_current_epoch(s) + 1)])
                    else s;
            assert s1.validators[i].activation_eligibility_epoch == if is_eligible_for_activation_queue(s.validators[i]) then get_current_epoch(s) + 1 
                                                                    else s.validators[i].activation_eligibility_epoch;
            
            assert |s1.balances| == |s1.validators| == |s.validators|; 
            assert forall v :: len <= v < |s.validators| ==> s1.validators[v] == s.validators[v];
        
            updateEligibilityHelper(s1, len-1)
    }

    function updateEjections(s: BeaconState): BeaconState
        requires |s.validators| == |s.balances|
        ensures updateEjections(s) == updateEjectionsHelper(s, |s.validators|)
    {
        updateEjectionsHelper(s, |s.validators|)
    }

    function updateEjectionsHelper(s: BeaconState, len: nat): BeaconState
        requires len <= |s.validators| == |s.balances|
        ensures updateEjectionsHelper(s, len) == s.(validators := updateEjectionsHelper(s, len).validators)

        ensures |updateEjectionsHelper(s, len).validators| == |s.validators|
        ensures updateEjectionsHelper(s, len) == s.(validators := updateEjectionsHelper(s, len).validators)
        ensures forall v :: len <= v < |s.validators| ==> updateEjectionsHelper(s, len).validators[v] == s.validators[v]
        ensures forall v :: 0 <= v < len ==> 
            // var new_val := if (is_active_validator(s.validators[v],  get_current_epoch(s)) && s.validators[v].effective_balance <= EJECTION_BALANCE )
            //             then initiate_validator_exit(s, v as ValidatorIndex).validators[v]
            //             else s.validators[v];
            updateEjectionsHelper(s, len).validators[v] == if (is_active_validator(s.validators[v],  get_current_epoch(s)) && s.validators[v].effective_balance <= EJECTION_BALANCE )
                        then initiate_validator_exit(s, v as ValidatorIndex).validators[v]
                        else s.validators[v]

        decreases len
    // {
    //     if len == 0 then s
    //     else
    //         var i := len -1;
    //         assert i < |s.validators|;
    //         var s1 := if (is_active_validator(s.validators[i],  get_current_epoch(s)) && s.validators[i].effective_balance <= EJECTION_BALANCE )
    //             // initiate_validator_exit(state, ValidatorIndex(index))
    //                 then initiate_validator_exit(s, i as ValidatorIndex)
    //                 else s;
    //         assert s1.validators[i] == if (is_active_validator(s.validators[i],  get_current_epoch(s)) && s.validators[i].effective_balance <= EJECTION_BALANCE )
    //                                         then initiate_validator_exit(s, i as ValidatorIndex).validators[i]
    //                                         else s.validators[i];
            
    //         assert |s1.balances| == |s1.validators| == |s.validators|; 
    //         assert forall v :: 0 <= v < |s1.balances|  ==> s1.balances[v] == s.balances[v];
    //         assert forall v :: i < v < |s.validators| ==> s1.validators[v] == s.validators[v];
    //         assert forall v :: 0 <= v < i ==> s1.validators[v] == s.validators[v];
    //         updateEjectionsHelper(s1, len-1)
    // }

    // /** */
    // method process_registry_updates(s: BeaconState)  returns (s' : BeaconState)
    //     requires |s.validators| == |s.balances|
    //     //ensures s' == updateRegistry(s)
    // {
    //     //  Process activation eligibility and ejections
    //     s' := s;
    //     var i := 0;
    //     assert s' == updateEligibilityHelper(s', i);

    //     while i < |s'.validators|
    //         invariant  |s.validators| == |s.balances| ==|s'.balances| == |s'.validators|
    //         invariant i <= |s'.validators| == |s'.balances| 
    //         invariant forall v :: 0 <= v < |s.balances| ==> s'.balances[v] ==  s.balances[v]
    //         invariant forall v :: i <= v < |s.validators| ==> s'.validators[v] ==  s.validators[v]
            
    //         invariant s' == s.(validators := s'.validators)
    //         invariant get_current_epoch(s') == get_current_epoch(s)

    //         invariant forall v :: 0 <= v < i ==> 
    //             updateEligibilityHelper(s, i).validators[v] == 
    //                     if is_eligible_for_activation_queue(s.validators[v])
    //                         then s.(validators := s.validators[v := s.validators[v].(activation_eligibility_epoch := get_current_epoch(s) + 1)]).validators[v]
    //                         else s.validators[v]

    //         invariant s' == updateEligibilityHelper(s', i)
    //     {
    //         assert s'.validators[i] == s.validators[i];
    //         // is_eligible_for_activation_queue:  v.activation_eligibility_epoch == FAR_FUTURE_EPOCH && v.effective_balance == MAX_EFFECTIVE_BALANCE
    //         if is_eligible_for_activation_queue(s.validators[i]) {
    //             //s'.validator[i].activation_eligibility_epoch := get_current_epoch(s') + 1;
    //             s' := s'.(validators := s'.validators[i := s'.validators[i].(activation_eligibility_epoch := get_current_epoch(s) + 1)]);   
    //         }
    //         assert s'.validators[i].activation_eligibility_epoch == if is_eligible_for_activation_queue(s.validators[i]) then get_current_epoch(s) + 1 
    //                                                                 else s.validators[i].activation_eligibility_epoch;
            
    //         i := i + 1;
            
    //     }
    //     assert s' == updateEligibilityHelper(s', i);
    //     var s1 := s';

    //     // Process ejections
    //     var j := 0;
    //     assert s' == updateEjectionsHelper(s1, j);
    //     while j < |s'.validators|
    //         invariant  |s1.validators| == |s1.balances| ==|s'.balances| == |s'.validators|
    //         invariant i <= |s'.validators| == |s'.balances| 
    //         invariant forall v :: 0 <= v < |s.balances| ==> s'.balances[v] ==  s.balances[v]
    //         invariant forall v :: j <= v < |s.validators| ==> s'.validators[v] ==  s.validators[v]
            
    //         invariant s' == s.(validators := s'.validators)
    //         invariant get_current_epoch(s') == get_current_epoch(s)

    //         // invariant forall v :: 0 <= v < j ==> 
    //         //     updateEjectionsHelper(s, j).validators[v] == 
    //         //             if (is_active_validator(s.validators[j],  get_current_epoch(s)) && s.validators[j].effective_balance <= EJECTION_BALANCE )
    //         //                then initiate_validator_exit(s, v as ValidatorIndex).validators[v]
    //         //                 else s.validators[v]

    //         // invariant s' == updateEjectionsHelper(s', j)
    //     {
    //         assert s'.validators[j] == s.validators[j];
    //         if (is_active_validator(s.validators[j],  get_current_epoch(s)) && s.validators[j].effective_balance <= EJECTION_BALANCE ) {
    //             s' := initiate_validator_exit(s', j as ValidatorIndex);   
    //         }
    //         assert s'.validators[i].activation_eligibility_epoch == if is_eligible_for_activation_queue(s.validators[i]) then get_current_epoch(s) + 1 
    //                                                                 else s.validators[i].activation_eligibility_epoch;
            
    //         j := j + 1;
            
    //     }
    //     assert s' == updateEjectionsHelper(s', j);

    //     // while i < |s'.validators|
    //     //     invariant  |s.validators| == |s.balances| ==|s'.balances| == |s'.validators|
    //     //     invariant i <= |s'.validators| == |s'.balances| 
    //     //     invariant forall v :: 0 <= v < |s.balances| ==> s'.balances[v] ==  s.balances[v]
    //     //     invariant forall v :: i <= v < |s.validators| ==> s'.validators[v] ==  s.validators[v]
            
    //     //     invariant s' == s.(validators := s'.validators)
    //     //     invariant get_current_epoch(s') == get_current_epoch(s)
    //     //     //invariant s' == updateEligibilityAndEjectionsHelper(s', i)
    //     // {
    //     //     assert s'.validators[i] == s.validators[i];
    //     //     // is_eligible_for_activation_queue:  v.activation_eligibility_epoch == FAR_FUTURE_EPOCH && v.effective_balance == MAX_EFFECTIVE_BALANCE
    //     //     if is_eligible_for_activation_queue(s.validators[i]) {
    //     //         //s'.validator[i].activation_eligibility_epoch := get_current_epoch(s') + 1;
    //     //         s' := s'.(validators := s'.validators[i := s'.validators[i].(activation_eligibility_epoch := get_current_epoch(s) + 1)]);   
    //     //     }
    //     //     assert s'.validators[i].activation_eligibility_epoch == if is_eligible_for_activation_queue(s.validators[i]) then get_current_epoch(s) + 1 
    //     //                                                             else s.validators[i].activation_eligibility_epoch;
    //     //     // i.e. even if made eligible for the activation queue, these validators won't be active validators and so don't overlap with the next section
            
    //     //     //assert get_current_epoch(s) < FAR_FUTURE_EPOCH;
            
    //     //     // is_active_validator: validator.activation_epoch <= epoch < validator.exitEpoch
    //     //     if is_active_validator(s.validators[i],  get_current_epoch(s)) && s.validators[i].effective_balance <= EJECTION_BALANCE {
    //     //         // initiate_validator_exit(state, ValidatorIndex(index))
    //     //         assert !(is_eligible_for_activation_queue(s.validators[i]) && s'.validators[i].effective_balance <= EJECTION_BALANCE);
    //     //         assert s'.validators[i] == s.validators[i];
    //     //         s' := initiate_validator_exit(s', i as ValidatorIndex);   
    //     //     }
    //     // //    assert s'.validators[i].exitEpoch == if is_active_validator(s.validators[i],  get_current_epoch(s)) && s.validators[i].effective_balance <= EJECTION_BALANCE
    //     // //                                 then initiate_validator_exit(s', i as ValidatorIndex).validators[i].exitEpoch
    //     // //                                 else s.validators[i].exitEpoch;
            
            
    //     //     i := i  + 1;
    //     //     //assert s' == updateEligibilityAndEjectionsHelper(s', i);
    //     // }



    //     //     # Queue validators eligible for activation and not yet dequeued for activation
    //     //     activation_queue = sorted([
    //     //     index for index, validator in enumerate(state.validators)
    //     //     if is_eligible_for_activation(state, validator)
    //     //     # Order by the sequence of activation_eligibility_epoch setting and then index
    //     //     ], key=lambda index: (state.validators[index].activation_eligibility_epoch, index))
    //     var activation_queue := get_activation_queue(s', 0);
    //     // @Note: in a simplification of the spec the activiation queue is not sorted


    //     var k := 0;

    //     //assert s' == updateRegistry(s); // need to functional equivalents??

    //     // # Dequeued validators for activation up to churn limit
    //     // for index in activation_queue[:get_validator_churn_limit(state)]:
    //     //     validator = state.validators[index]
    //     //     validator.activation_epoch = compute_activation_exit_epoch(get_current_epoch(state))
    //     // var churn_limit := get_validator_churn_limit(s') ;
    //     // assume churn_limit as nat <= |activation_queue| <= |s'.validators|;
    //     // assume forall index :: 0 <= index < |activation_queue[..churn_limit]| ==> activation_queue[index] as nat < |s'.validators|;
        
    //     // while j < |activation_queue[..churn_limit]|
    //     //     invariant  |s.validators| == |s.balances| ==|s'.balances| == |s'.validators|
    //     //     invariant j <= |s'.validators| == |s'.balances| 
    //     //     // invariant forall v :: i <= v < |s.balances| ==> s'.balances[v] ==  s.balances[v]
            
    //     //     // invariant s' == s.(validators := s'.validators)
    //     // {
    //     //     assert activation_queue[j] as nat < |s'.validators|;
    //     //     s' := s'.(validators := s'.validators[activation_queue[j] := s'.validators[activation_queue[j]].(activation_epoch := compute_activation_exit_epoch(get_current_epoch(s')))]);   
    //     //     j := j  + 1;
    //     // }
    // }

    // // // lemma RegistryHelperLemma(s: BeaconState, i: ValidatorIndex)
    // // //     requires get_current_epoch(s) < FAR_FUTURE_EPOCH
    // // //     requires i as nat < |s.validators|
    // // //     ensures !(is_eligible_for_activation_queue(s.validators[i]) && s.validators[i].effective_balance <= EJECTION_BALANCE)
    // // // {
    // // //     assert is_eligible_for_activation_queue(s.validators[i]) ==> s.validators[i].effective_balance == MAX_EFFECTIVE_BALANCE;

    // // // }
    

    method process_slashings(s: BeaconState) returns (s' : BeaconState)
        requires |s.validators| == |s.balances| 
        ensures |s'.validators| == |s'.balances| 
        ensures s' == updateSlashings(s)
    {
        var epoch := get_current_epoch(s);
        var total_balance := get_total_active_balance_full(s);
        var sumSlashings := get_total_slashings(s.slashings);
        var adjusted_total_slashing_balance := min((sumSlashings as nat * PROPORTIONAL_SLASHING_MULTIPLIER as nat) as nat, total_balance as nat) as Gwei;
        var increment := EFFECTIVE_BALANCE_INCREMENT;  // Factored out from penalty numerator to avoid uint64 overflow
        
        assert total_balance > 0 as Gwei;
        assert increment > 0 as Gwei;
        assume forall v :: 0 <= v < |s.validators| ==> 0 <= s.validators[v].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat < 0x10000000000000000;
        assume epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2 < 0x10000000000000000;
            
    
        s' := s;
        var i := 0;
        assert s' == updateSlashingsHelper(s, i, epoch, total_balance, adjusted_total_slashing_balance, increment);

        while i < |s'.balances|
            invariant  |s.validators| == |s.balances| ==|s'.balances| == |s'.validators|
            invariant i <= |s'.validators| == |s'.balances| 
            invariant s.validators == s'.validators
            invariant forall v :: i <= v < |s.balances| ==> s'.balances[v] ==  s.balances[v]

            //ensures |s'.validators| == |s.validators| 
            //ensures |s'.balances| == |s.balances| 
        
            //ensures forall v :: 0 <= v < |s.validators| ==> s'.validators[v]  == s.validators[v]
            invariant s' == s.(balances := s'.balances)
            //ensures forall v :: len <= v < |s.balances| ==> s'.balances[v]  == s.balances[v]


            invariant s' == s.(balances := s'.balances)
            
            invariant forall v :: 0 <= v < i ==> 
        
                assert v < |s.balances|;

                var new_bal := if (s.validators[v].slashed && (epoch + EPOCHS_PER_SLASHINGS_VECTOR / 2) == s.validators[v].withdrawable_epoch)
                                        // then if s.balances[v] > penalty as Gwei then s.balances[v] - penalty as Gwei
                                        //                                                 else 0 as Gwei
                                        then decrease_balance(s, v as ValidatorIndex, (s.validators[v].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat) as Gwei).balances[v]
                                        else s.balances[v];
                updateSlashingsHelper(s, i, epoch, total_balance, adjusted_total_slashing_balance, increment).balances[v] == new_bal
            invariant s' == updateSlashingsHelper(s, i, epoch, total_balance, adjusted_total_slashing_balance, increment)
            
        {
            // var penalty_numerator := s'.validators[i].effective_balance as nat / increment as nat * adjusted_total_slashing_balance as nat;
            // var penalty := penalty_numerator as nat / total_balance  as nat * increment as nat;
            // assume 0 <= penalty < 0x10000000000000000;
            
            if (s'.validators[i].slashed && (epoch + EPOCHS_PER_SLASHINGS_VECTOR / 2) == s'.validators[i].withdrawable_epoch) {
                
                s' := decrease_balance(s', i as ValidatorIndex, (s.validators[i].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat) as Gwei);
            }
    
            //assert s.validators == s'.validators;
            assert s'.balances[i] == if (s.validators[i].slashed && (epoch + EPOCHS_PER_SLASHINGS_VECTOR / 2) == s.validators[i].withdrawable_epoch)
                                            // then 
                                            //     if s.balances[i] > penalty as Gwei then s.balances[i] - penalty as Gwei
                                            //                                         else 0 as Gwei
                                            then decrease_balance(s, i as ValidatorIndex, (s.validators[i].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat) as Gwei).balances[i]
                                            else s.balances[i];
            //assert forall v :: i < v < |s.balances| ==> s'.balances[v] == s.balances[v];
            i := i + 1;
            // assert i <= |s.balances| == |s.validators| ;
            // assert total_balance > 0 as Gwei;
            // assert increment > 0 as Gwei;
            // assert forall v :: 0 <= v < |s.validators| ==> 0 <= s.validators[v].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat < 0x10000000000000000;
            // assert epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2 < 0x10000000000000000;
            // assert s' == updateSlashingsHelper(s, i, epoch, total_balance, adjusted_total_slashing_balance, increment);
        
        }
        //assert |s.balances| == |s.validators|;

        assert s' == updateSlashingsHelper(s, i, epoch, total_balance, adjusted_total_slashing_balance, increment);
        assert i == |s'.validators|;
        assert s' == updateSlashings(s);
    }

    

    


    method process_eth1_data_reset(s: BeaconState) returns (s' : BeaconState)
        ensures s' == updateEth1DataReset(s)
    {
        var next_epoch := get_current_epoch(s) + 1;
        // Reset eth1 data votes
        if (next_epoch % EPOCHS_PER_ETH1_VOTING_PERIOD) == 0 {
            s' := s.(eth1_data_votes := []);
        }
        else {s' := s;}
    }
    

    method process_effective_balance_updates(s: BeaconState) returns (s' : BeaconState)
        requires |s.balances| == |s.validators|
        ensures s' == updateEffectiveBalance(s)
    {
        s' := s;
        
        var i := 0;
        assert s' == updateEffectiveBalanceHelper(s, i);
        //assume forall v :: 0 <= v < |rewards| ==> s.balances[v] as nat + rewards[v] as nat < 0x10000000000000000;
        var HYSTERESIS_INCREMENT := EFFECTIVE_BALANCE_INCREMENT / HYSTERESIS_QUOTIENT;
        var DOWNWARD_THRESHOLD := HYSTERESIS_INCREMENT * HYSTERESIS_DOWNWARD_MULTIPLIER;
        var UPWARD_THRESHOLD := HYSTERESIS_INCREMENT * HYSTERESIS_UPWARD_MULTIPLIER;

        assume forall v :: i <= v < |s.validators| ==> s.balances[v] as nat + DOWNWARD_THRESHOLD as nat  < 0x10000000000000000;
        assume forall v :: i <= v < |s.validators| ==> s.validators[v].effective_balance as nat + UPWARD_THRESHOLD as nat  < 0x10000000000000000;
        assert forall v :: i <= v < |s.validators| ==> 0 <= (s.balances[v] % EFFECTIVE_BALANCE_INCREMENT) < EFFECTIVE_BALANCE_INCREMENT;
        assert forall v :: i <= v < |s.validators| ==> s.balances[v] >= (s.balances[v] % EFFECTIVE_BALANCE_INCREMENT);
        
        while i < |s'.balances| //for index in range(len(state.validators)):
            invariant  |s.validators| == |s.balances| ==|s'.balances| == |s'.validators|
            invariant i <= |s'.validators|
            invariant forall v :: i <= v < |s.validators| ==> s'.validators[v]  == s.validators[v];
            invariant s' == s.(validators := s'.validators);
            
            invariant s'.balances == s.balances
            invariant forall v :: i <= v < |s.validators| ==> s'.validators[v].effective_balance ==  s.validators[v].effective_balance;
            invariant forall v :: i <= v < |s.balances| ==> s'.balances[v] ==  s.balances[v];
            // invariant forall v :: 0 <= v < i ==> 
            //                 s'.validators[v].effective_balance ==  
            //                         if (s.balances[v]+ DOWNWARD_THRESHOLD < s.validators[v].effective_balance || s.validators[v].effective_balance + UPWARD_THRESHOLD < s.balances[v]) 
            //                             then min((s.balances[v] - (s.balances[v] % EFFECTIVE_BALANCE_INCREMENT)) as nat, MAX_EFFECTIVE_BALANCE as nat) as Gwei 
            //                             else s.validators[v].effective_balance;

            invariant forall v :: 0 <= v < i ==> 
                    var balance := s.balances[v];
                    var HYSTERESIS_INCREMENT := EFFECTIVE_BALANCE_INCREMENT / HYSTERESIS_QUOTIENT;
                    var DOWNWARD_THRESHOLD := HYSTERESIS_INCREMENT * HYSTERESIS_DOWNWARD_MULTIPLIER;
                    var UPWARD_THRESHOLD := HYSTERESIS_INCREMENT * HYSTERESIS_UPWARD_MULTIPLIER;
                    assume balance as nat + DOWNWARD_THRESHOLD as nat  < 0x10000000000000000;
                    assume s.validators[v].effective_balance as nat + UPWARD_THRESHOLD as nat  < 0x10000000000000000;
                    assert 0 <= (balance % EFFECTIVE_BALANCE_INCREMENT) < EFFECTIVE_BALANCE_INCREMENT;
                    assert balance >= (balance % EFFECTIVE_BALANCE_INCREMENT);
                    //assert balance - (balance % EFFECTIVE_BALANCE_INCREMENT) >= 0;

                    // s'.validators[v].effective_balance ==  
                    //                     if (balance + DOWNWARD_THRESHOLD < s.validators[v].effective_balance || s.validators[v].effective_balance + UPWARD_THRESHOLD < balance) 
                    //                         then min((balance - (balance % EFFECTIVE_BALANCE_INCREMENT)) as nat, MAX_EFFECTIVE_BALANCE as nat) as Gwei 
                    //                         else s.validators[v].effective_balance;
                    var new_bal := if (s.balances[v] + DOWNWARD_THRESHOLD < s.validators[v].effective_balance || s.validators[v].effective_balance + UPWARD_THRESHOLD < s.balances[v]) 
                                        then min((s.balances[v] - (s.balances[v] % EFFECTIVE_BALANCE_INCREMENT)) as nat, MAX_EFFECTIVE_BALANCE as nat) as Gwei 
                                        else s.validators[v].effective_balance;
                    s'.validators[v] == s.validators[v].(effective_balance := new_bal);
            
           //invariant s' == updateEffectiveBalanceHelper(s, i)
        {
            var balance := s'.balances[i];
            if (balance + DOWNWARD_THRESHOLD < s'.validators[i].effective_balance || s'.validators[i].effective_balance + UPWARD_THRESHOLD < balance) {
                    s' := s'.(validators := s'.validators[i := s'.validators[i].(effective_balance := min((balance - (balance % EFFECTIVE_BALANCE_INCREMENT)) as nat, MAX_EFFECTIVE_BALANCE as nat) as Gwei)]);
                }
            
            assert s'.validators[i].effective_balance == if (balance + DOWNWARD_THRESHOLD < s.validators[i].effective_balance || s.validators[i].effective_balance + UPWARD_THRESHOLD < balance) 
                                                         then min((balance - (balance % EFFECTIVE_BALANCE_INCREMENT)) as nat, MAX_EFFECTIVE_BALANCE as nat) as Gwei 
                                                         else s.validators[i].effective_balance;
            
            assert  i <= |s.balances| == |s.validators|;
            assert |s'.validators| == |s.validators|;
            assert |s'.balances| == |s.balances|;
            assert s'.balances == s.balances;
            //requires forall v :: i <= v < |s.validators| ==> s'.validators[v].effective_balance  == s.validators[v].effective_balance
            
            // assert forall v :: 0 <= v < i ==> 
            //         var balance := s.balances[v];
            //         var HYSTERESIS_INCREMENT := EFFECTIVE_BALANCE_INCREMENT / HYSTERESIS_QUOTIENT;
            //         var DOWNWARD_THRESHOLD := HYSTERESIS_INCREMENT * HYSTERESIS_DOWNWARD_MULTIPLIER;
            //         var UPWARD_THRESHOLD := HYSTERESIS_INCREMENT * HYSTERESIS_UPWARD_MULTIPLIER;
            //         assume balance as nat + DOWNWARD_THRESHOLD as nat  < 0x10000000000000000;
            //         assume s.validators[v].effective_balance as nat + UPWARD_THRESHOLD as nat  < 0x10000000000000000;
            //         assert 0 <= (balance % EFFECTIVE_BALANCE_INCREMENT) < EFFECTIVE_BALANCE_INCREMENT;
            //         assert balance >= (balance % EFFECTIVE_BALANCE_INCREMENT);
            //         //assert balance - (balance % EFFECTIVE_BALANCE_INCREMENT) >= 0;

            //         // s'.validators[v].effective_balance ==  
            //         //                     if (balance + DOWNWARD_THRESHOLD < s.validators[v].effective_balance || s.validators[v].effective_balance + UPWARD_THRESHOLD < balance) 
            //         //                         then min((balance - (balance % EFFECTIVE_BALANCE_INCREMENT)) as nat, MAX_EFFECTIVE_BALANCE as nat) as Gwei 
            //         //                         else s.validators[v].effective_balance;
            //         var new_bal := if (s.balances[v] + DOWNWARD_THRESHOLD < s.validators[v].effective_balance || s.validators[v].effective_balance + UPWARD_THRESHOLD < s.balances[v]) 
            //                             then min((s.balances[v] - (s.balances[v] % EFFECTIVE_BALANCE_INCREMENT)) as nat, MAX_EFFECTIVE_BALANCE as nat) as Gwei 
            //                             else s.validators[v].effective_balance;
            //         s'.validators[v] == s.validators[v].(effective_balance := new_bal);
                
                
            
            i := i +1;
            //hope1(s, s', i);
            assert s' == updateEffectiveBalanceHelper(s, i);
        }
        
        //hope1(s, s', i);
        assert |s.balances| == |s.validators|;
        //assert |s'.validators| == |s.validators|;
        //assert |s'.balances| == |s.balances|;
        //assert s'.balances == s.balances;

        assert s' == updateEffectiveBalanceHelper(s, i);
        assert i == |s'.validators|;
        assert s' == updateEffectiveBalance(s);
    }

    // lemma hope1(s: BeaconState, s': BeaconState, i: nat)
    //     requires  i <= |s.balances| == |s.validators|
    //     requires |s'.validators| == |s.validators|
    //     requires |s'.balances| == |s.balances|
    //     requires s'.balances == s.balances
    //     //requires forall v :: i <= v < |s.validators| ==> s'.validators[v].effective_balance  == s.validators[v].effective_balance
    //     requires s' == s.(validators := s'.validators)
    //     requires forall v :: i <= v < |s.validators| ==> s'.validators[v]  == s.validators[v]
        
    //     requires forall v :: 0 <= v < i ==> 
    //             var balance := s.balances[v];
    //             var HYSTERESIS_INCREMENT := EFFECTIVE_BALANCE_INCREMENT / HYSTERESIS_QUOTIENT;
    //             var DOWNWARD_THRESHOLD := HYSTERESIS_INCREMENT * HYSTERESIS_DOWNWARD_MULTIPLIER;
    //             var UPWARD_THRESHOLD := HYSTERESIS_INCREMENT * HYSTERESIS_UPWARD_MULTIPLIER;
    //             assume balance as nat + DOWNWARD_THRESHOLD as nat  < 0x10000000000000000;
    //             assume s.validators[v].effective_balance as nat + UPWARD_THRESHOLD as nat  < 0x10000000000000000;
    //             assert 0 <= (balance % EFFECTIVE_BALANCE_INCREMENT) < EFFECTIVE_BALANCE_INCREMENT;
    //             assert balance >= (balance % EFFECTIVE_BALANCE_INCREMENT);
    //             //assert balance - (balance % EFFECTIVE_BALANCE_INCREMENT) >= 0;

    //             // s'.validators[v].effective_balance ==  
    //             //                     if (balance + DOWNWARD_THRESHOLD < s.validators[v].effective_balance || s.validators[v].effective_balance + UPWARD_THRESHOLD < balance) 
    //             //                         then min((balance - (balance % EFFECTIVE_BALANCE_INCREMENT)) as nat, MAX_EFFECTIVE_BALANCE as nat) as Gwei 
    //             //                         else s.validators[v].effective_balance;
    //             var new_bal := if (s.balances[v] + DOWNWARD_THRESHOLD < s.validators[v].effective_balance || s.validators[v].effective_balance + UPWARD_THRESHOLD < s.balances[v]) 
    //                                 then min((s.balances[v] - (s.balances[v] % EFFECTIVE_BALANCE_INCREMENT)) as nat, MAX_EFFECTIVE_BALANCE as nat) as Gwei 
    //                                 else s.validators[v].effective_balance;
    //             s'.validators[v] == s.validators[v].(effective_balance := new_bal);
            
    //             //s'.validators[v].pubkey == s.validators[v].pubkey &&
    //             //s'.validators[v].effective_balance == new_bal &&
    //             //s'.validators[v].slashed == s.validators[v].slashed &&
    //             //s'.validators[v].activationEpoch == s.validators[v].activationEpoch &&
    //             //s'.validators[v].exitEpoch == s.validators[v].exitEpoch &&
    //             //s'.validators[v].withdrawable_epoch == s.validators[v].withdrawable_epoch 
    //     ensures  s' == updateEffectiveBalanceHelper(s, i)
    // {
    //     // Thanks Dafny
    //     assert s'.balances == updateEffectiveBalanceHelper(s, i).balances;
    //     assert forall v :: i <= v < |s.validators| ==> s'.validators[v] == updateEffectiveBalanceHelper(s, i).validators[v];
    //     assert forall v :: 0 <= v < i ==> 
    //         // var balance := s.balances[v];
    //         var HYSTERESIS_INCREMENT := EFFECTIVE_BALANCE_INCREMENT / HYSTERESIS_QUOTIENT;
    //         var DOWNWARD_THRESHOLD := HYSTERESIS_INCREMENT * HYSTERESIS_DOWNWARD_MULTIPLIER;
    //         var UPWARD_THRESHOLD := HYSTERESIS_INCREMENT * HYSTERESIS_UPWARD_MULTIPLIER;

    //         assume s.balances[v] as nat + DOWNWARD_THRESHOLD as nat  < 0x10000000000000000;
    //         assume s.validators[v].effective_balance as nat + UPWARD_THRESHOLD as nat  < 0x10000000000000000;

    //         //updateEffectiveBalanceHelper(s, len).validators[v].effective_balance == 
    //         var new_bal := if (s.balances[v] + DOWNWARD_THRESHOLD < s.validators[v].effective_balance || s.validators[v].effective_balance + UPWARD_THRESHOLD < s.balances[v]) 
    //                                 then min((s.balances[v] - (s.balances[v] % EFFECTIVE_BALANCE_INCREMENT)) as nat, MAX_EFFECTIVE_BALANCE as nat) as Gwei 
    //                                 else s.validators[v].effective_balance;
    //         updateEffectiveBalanceHelper(s, i).validators[v] == s.validators[v].(effective_balance := new_bal);
    //         //updateEffectiveBalanceHelper(s, i).validators[v].pubkey == s'.validators[v].pubkey &&
    //         //updateEffectiveBalanceHelper(s, i).validators[v].effective_balance == new_bal == s'.validators[v].effective_balance &&
    //         //updateEffectiveBalanceHelper(s, i).validators[v].slashed == s'.validators[v].slashed &&
    //         //updateEffectiveBalanceHelper(s, i).validators[v].activationEpoch == s'.validators[v].activationEpoch &&
    //         //updateEffectiveBalanceHelper(s, i).validators[v].exitEpoch == s'.validators[v].exitEpoch &&
    //         //updateEffectiveBalanceHelper(s, i).validators[v].withdrawable_epoch == s'.validators[v].withdrawable_epoch ;
    //     assert  s' == updateEffectiveBalanceHelper(s, i);
    // }



    

    
    
    /**/
    method process_slashings_reset(s: BeaconState) returns (s' : BeaconState)
        ensures s' == updateSlashingsReset(s)
    {
        var next_epoch := get_current_epoch(s) + 1;
        // Reset slashings
        s' := s.(
                slashings := s.slashings[(next_epoch % EPOCHS_PER_SLASHINGS_VECTOR) as nat := 0 as Gwei]
            );

    }


    /**/
    method process_randao_mixes_reset(s: BeaconState) returns (s' : BeaconState)
        ensures s' == updateRandaoMixes(s)
    {
        var current_epoch := get_current_epoch(s);
        var next_epoch := current_epoch + 1;
        // Set randao mix
        // state.randao_mixes[next_epoch % EPOCHS_PER_HISTORICAL_VECTOR] = get_randao_mix(s, current_epoch)
        s' := s.(
                randao_mixes := s.randao_mixes[(next_epoch % EPOCHS_PER_HISTORICAL_VECTOR) as nat := get_randao_mix(s, current_epoch)]
            );

    }
    
    
    /**/
    method process_historical_roots_update(s: BeaconState) returns (s' : BeaconState)
        ensures s' == updateHistoricalRoots(s)
    {
        // Set historical root accumulator
        var next_epoch := (get_current_epoch(s) + 1) as Epoch;
        if next_epoch % (SLOTS_PER_HISTORICAL_ROOT / SLOTS_PER_EPOCH) == 0 {
            var historical_batch := HistoricalBatch(s.block_roots, s.state_roots);
            s' := s.(
                historical_roots := s.historical_roots + [hash(historical_batch)]
            );
        }
        else  {s' := s;}
    }

    /**
     *  Rotate the attestations.
     *  @param  s   A state.
     *  @returns    `s` with attestations rotated.
     *
     *  @todo       This is a partial implementation capturing only
     *              the attestations updates.
     */
    method process_participation_record_updates(s: BeaconState) returns (s' : BeaconState)
        ensures s' == updateParticipationRecords(s)
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
        ensures s'.previous_epoch_attestations == s.previous_epoch_attestations 
        //ensures get_previous_epoch(s') >= s'.finalised_checkpoint.epoch
        
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