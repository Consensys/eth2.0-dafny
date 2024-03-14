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

//  @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /timeLimit:100 /noCheating:1

include "../../utils/NonNativeTypes.dfy"
include "../../ssz/Constants.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../Helpers.dfy"
include "../Helpers.p.dfy"
include "EpochProcessing.s.dfy"
include "../../utils/Eth2Types.dfy"
include "../../utils/MathHelpers.dfy"
include "../../utils/NativeTypes.dfy"

/**
 * Epoch processing and related functions for the Beacon Chain.
 */
module EpochProcessing {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NonNativeTypes
    import opened Constants
    import opened BeaconChainTypes
    import opened AttestationsTypes
    import opened BeaconHelpers
    import opened BeaconHelperProofs
    import opened EpochProcessingSpec
    import opened Eth2Types
    import opened MathHelpers
    import opened NativeTypes

    /**
     *  At epoch boundaries, update justifications, rewards, penalities,
     *  registry, slashing, and final updates, etc.
     *
     *  @param  s   A beacon state.
     *  @returns    A new state resulting from the processing of the epoch components.
     *  @note       The process_effective_balance_updates component has been simplified.
     */
    method process_epoch(s: BeaconState) returns (s' : BeaconState) 
        //  Make sure s.slot does not overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        //  And we should only execute this method when:
        requires (s.slot + 1) % SLOTS_PER_EPOCH == 0
        requires |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)
      
        ensures s'.slot == s.slot
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures |s'.validators| == |s'.balances|
        ensures s' == updateEpoch(s)
        ensures is_valid_state_epoch_attestations(s')
    {
        assert(s.slot as nat + 1 < 0x10000000000000000 as nat);
        s' := process_justification_and_finalization(s);

        assert is_valid_state_epoch_attestations(s');
        assert s' == updateFinalisedCheckpoint(updateJustification(s), s);
        assert s' == updateJustificationAndFinalisation(s);
        
        s' := process_rewards_and_penalties(s');

        assert s' == updateRAndP(updateJustificationAndFinalisation(s));
    
        assert |s'.validators| == |s'.balances| == |s.validators|;

        s' := process_registry_updates(s');
        assert s' == updateRegistry(
                        updateRAndP(
                            updateJustificationAndFinalisation(s)
                        )
                    );


        s' := process_slashings(s');
        assert s' == updateSlashings(
                        updateRegistry(
                            updateRAndP(
                                updateJustificationAndFinalisation(s)
                            )
                        )
                    );

        s' := process_eth1_data_reset(s');
        assert s' == updateEth1DataReset(
                        updateSlashings(
                            updateRegistry(
                                updateRAndP(
                                    updateJustificationAndFinalisation(s)
                                )
                            )
                        )
                    );

        assert |s'.validators| == |s'.balances| == |s.validators|;
        s' := process_effective_balance_updates(s');
        assert s' == updateEffectiveBalance(
                        updateEth1DataReset(
                            updateSlashings(
                                updateRegistry(
                                    updateRAndP(
                                        updateJustificationAndFinalisation(s)
                                    )
                                )
                            )
                        )
                    );

        s' := process_slashings_reset(s');
        assert s' == updateSlashingsReset(
                        updateEffectiveBalance(
                            updateEth1DataReset(
                                updateSlashings(
                                    updateRegistry(
                                        updateRAndP(
                                            updateJustificationAndFinalisation(s)
                                        )
                                    )
                                )
                            )
                        )
                    );


        s' := process_randao_mixes_reset(s');
        assert s' == updateRandaoMixes(
                        updateSlashingsReset(
                            updateEffectiveBalance(
                                updateEth1DataReset(
                                    updateSlashings(
                                        updateRegistry(
                                            updateRAndP(
                                                updateJustificationAndFinalisation(s)
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    );

        s' := process_historical_summaries_update(s');
        assert s' == updateHistoricalSummaries(
                        updateRandaoMixes(
                            updateSlashingsReset(
                                updateEffectiveBalance(
                                    updateEth1DataReset(
                                        updateSlashings(
                                            updateRegistry(
                                                updateRAndP(
                                                    updateJustificationAndFinalisation(s)
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    );

        s' := process_participation_record_updates(s');
        assert s' == updateParticipationRecords(
                        updateHistoricalSummaries(
                            updateRandaoMixes(
                                updateSlashingsReset(
                                    updateEffectiveBalance(
                                        updateEth1DataReset(
                                            updateSlashings(
                                                updateRegistry(
                                                    updateRAndP(
                                                        updateJustificationAndFinalisation(s)
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    );

        assert s' == updateEpoch(s);
        return s';
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
        requires is_valid_state_epoch_attestations(s)

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
        ensures is_valid_state_epoch_attestations(s')
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
            s' := s'.(justification_bits 
                        := [false] + (s.justification_bits)[..JUSTIFICATION_BITS_LENGTH - 1]); 
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
            var matching_target_attestations_prev 
                    := get_matching_target_attestations(s', previous_epoch) ;  
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
            assert s'.slot == updateJustificationPrevEpoch(s).slot;
            assert s'.current_justified_checkpoint 
                    == updateJustificationPrevEpoch(s).current_justified_checkpoint;
            assert s'.previous_justified_checkpoint 
                    == updateJustificationPrevEpoch(s).previous_justified_checkpoint;
            assert s' == updateJustificationPrevEpoch(s); 

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
            //  We assume here that the target language is such that AND conditions are evaluated 
            ///   short-circuit i.e. unfolded as nested ifs
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
    
    /** 
     *  Process rewards and penalties.
     *  
     *  @param  s   A state.
     *  @returns    The state obtained after applying the epoch rewards and penalties.
     *
     *  @note       This function uses axiom AssumeNoGweiOverflowToAddRewards.
     *  @note       This axiom is used as a simplification to ensure that balance 
     *              overflows don't occur. To remove this axiom a strategy similar
     *              to that applied within the deposit processing could be applied.          
     */
    method process_rewards_and_penalties(s: BeaconState)  returns (s' : BeaconState)
        requires |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)
        
        ensures s' == updateRAndP(s)
        ensures is_valid_state_epoch_attestations(s')
    {
        // Simplify edge cases
        if get_current_epoch(s) <= GENESIS_EPOCH + 1 { 
            return s;
        }
        
        s' := s;
        var (rewards, penalties) := get_attestation_deltas(s');
        var i := 0;
        
        assert s' == updateRewardsAndPenalties(s, rewards[..i], penalties[..i]);
        // An assume lemma is used to prevent overflows 
        AssumeNoGweiOverflowToAddRewards(s', rewards);
        // i.e. assume forall v :: 0 <= v < |rewards| 
        //        ==> s.balances[v] as nat + rewards[v] as nat < 0x10000000000000000;
        
        while i < |s'.validators| 
            invariant i <= |rewards| == |penalties|
            invariant |rewards| 
                        == |penalties| 
                        == |s.validators| 
                        == |s.balances| 
                        == |s'.validators| 
                        == |s'.balances|
            invariant |rewards[..i]| == |penalties[..i]| <= |s.validators| == |s.balances|
            invariant i == |rewards[..i]|
            invariant s' == updateRewardsAndPenalties(s, rewards[..i], penalties[..i])
        {
            assert i < |rewards|;
            assert i < |s'.balances|;
            s' := increase_balance(s', i as ValidatorIndex, rewards[i]);
            s' := decrease_balance(s', i as ValidatorIndex, penalties[i]);
            assert s'.balances[i] == if s.balances[i] + rewards[i] > penalties[i] 
                                        then s.balances[i] + rewards[i] - penalties[i] 
                                        else 0 as Gwei;
            assert forall v :: 0 <= v <= i 
                    ==> s'.balances[v] == if s.balances[v] + rewards[v] > penalties[v] 
                                            then s.balances[v] + rewards[v] - penalties[v] 
                                            else 0 as Gwei;
            i := i + 1;
        } 
        assert rewards[..i] == rewards;
        assert penalties[..i] == penalties;
        assert s' == updateRewardsAndPenalties(s, rewards, penalties);
        assert s' == updateRAndP(s);
    }

    /** 
     *  Process registry updates.
     *  
     *  @param  s   A state.
     *  @returns    The state obtained after applying the epoch registry updates
     *
     *  @note       This component has been simplified.
     *              i.e the activation queue within process_queue_validators is not 
     *              sorted. Please refer to process_queue_validators and updateQueueValidators.
     *  @note       This component uses the axiom AssumeMinimumActiveValidators.
     */
    method process_registry_updates(s: BeaconState) returns (s' : BeaconState)
        requires |s.validators| == |s.balances| 
        requires is_valid_state_epoch_attestations(s)

        ensures |s'.validators| == |s'.balances| 
        ensures s' == updateRegistry(s)
        ensures is_valid_state_epoch_attestations(s')
    {
        s' := process_activation_eligibility(s);
        AssumeMinimumActiveValidators(s');
        s' := process_ejections(s');
        s' := process_queue_validators(s');
    }

    /** 
     *  A helper to process the first component of the registry updates.
     *  
     *  @param  s   A state.
     *  @returns    The state obtained after applying the activation eligibility updates
     */
    method process_activation_eligibility(s: BeaconState) returns (s' : BeaconState)
        requires |s.validators| == |s.balances| 
        requires is_valid_state_epoch_attestations(s)

        ensures |s'.validators| == |s'.balances| 
        ensures is_valid_state_epoch_attestations(s')
        ensures s' == updateActivationEligibility(s)
    {
        s' := s;
        var i := 0;
        assert s' == updateActivationEligibilityHelper(s, i);

        while i < |s'.validators|
            invariant i <= |s'.validators| == |s'.balances| == |s.validators|
            invariant is_valid_state_epoch_attestations(s')
            invariant s' == updateActivationEligibilityHelper(s, i)
        {
            if is_eligible_for_activation_queue(s.validators[i]) {
                    s' := set_activation_eligibility_epoch(s', 
                                                            i as ValidatorIndex, 
                                                            get_current_epoch(s) + 1 as Epoch
                                                            );
            }
            i := i + 1;
            assert s' == updateActivationEligibilityHelper(s, i);

        }
        assert s' == updateActivationEligibilityHelper(s, i);
        assert i == |s'.validators|;
        assert s' == updateActivationEligibility(s);
    }
    
    /** 
     *  A helper to process the second component of the registry updates.
     *  
     *  @param  s   A state.
     *  @returns    The state obtained after applying the ejection updates
     */
    method process_ejections(s: BeaconState) returns (s' : BeaconState)
        requires |s.validators| == |s.balances| 
        requires is_valid_state_epoch_attestations(s)
        requires minimumActiveValidators(s)

        ensures |s'.validators| == |s'.balances| 
        ensures is_valid_state_epoch_attestations(s')
        ensures s' == updateEjections(s)
    {
        s' := s;
        var i := 0;
        assert s' == updateEjectionsHelper(s, i);

        while i < |s'.validators|
            invariant i <= |s'.validators| == |s'.balances| == |s.validators| 
            invariant is_valid_state_epoch_attestations(s')
            invariant s' == updateEjectionsHelper(s, i)
        {
            if ((is_active_validator(s'.validators[i], get_current_epoch(s')))
                && (s'.validators[i].effective_balance <= EJECTION_BALANCE))
                {  
                    s' := initiate_validator_exit(s', i as ValidatorIndex);
                }
            i := i + 1;
            assert s' == updateEjectionsHelper(s, i);

        }
        assert s' == updateEjectionsHelper(s, i);
        assert i == |s'.validators|;
        assert s' == updateEjections(s);
    }

    /** 
     *  A helper to process the final component of the registry updates.
     *  
     *  @param  s   A state.
     *  @returns    The state obtained after applying the dequeue updates
     */
    method process_queue_validators(s: BeaconState) returns (s' : BeaconState)
        requires |s.validators| == |s.balances| 
        requires is_valid_state_epoch_attestations(s)

        ensures |s'.validators| == |s'.balances| 
        ensures is_valid_state_epoch_attestations(s')
        ensures s' == updateQueueValidators(s)
    {
        s' := s;
        var i := 0;

        // # Queue validators eligible for activation and not yet dequeued for activation
        var activation_queue := get_validator_indices_activation_eligible(s.validators, s.finalised_checkpoint.epoch); 
        // @note The activation queue is not sorted as per the spec. 
        //       This simplification could be removed at a future point.
        // i.e. 
        // activation_queue = sorted([
        //     index for index, validator in enumerate(state.validators)
        //     if is_eligible_for_activation(state, validator)
        //     # Order by the sequence of activation_eligibility_epoch setting and then index
        // ], key=lambda index: (state.validators[index].activation_eligibility_epoch, index))
        var churn_limit := get_validator_churn_limit(s) as nat;

        // # Dequeued validators for activation up to churn limit
        var dequeue := if churn_limit <= |activation_queue| 
                        then activation_queue[..churn_limit]
                        else [];

        assert s' == updateQueueValidatorsHelper(s, dequeue, i);

        while i < |s'.validators|
            invariant i <= |s'.validators| ==  |s.validators|
            invariant is_valid_state_epoch_attestations(s')
            invariant get_current_epoch(s') == get_current_epoch(s)
            invariant compute_activation_exit_epoch(get_current_epoch(s')) == compute_activation_exit_epoch(get_current_epoch(s))
            invariant s' == updateQueueValidatorsHelper(s, dequeue, i)
        {
            if i as uint64 in dequeue {
                s' := set_activation_epoch(s', 
                                           i as ValidatorIndex, 
                                           compute_activation_exit_epoch(get_current_epoch(s'))
                                          );
            }
            i := i + 1;
            assert s' == updateQueueValidatorsHelper(s, dequeue, i);

        }
        assert s' == updateQueueValidatorsHelper(s, dequeue, i);
        assert i == |s'.validators|;
        assert s' == updateQueueValidators(s);
    }

    /** 
     *  Process slashings.
     *  
     *  @param  s   A state.
     *  @returns    The state obtained after applying the epoch slashings.
     *
     *  @note       This function uses axiom AssumeNoEpochOverflow and 
     *              AssumeNoGweiOverflowToUpdateSlashings.
     *  @note       These axioms are used as a simplification to ensure that balance 
     *              overflows don't occur. To remove this axiom a strategy similar
     *              to that applied within the deposit processing could be applied.        
     */
    method process_slashings(s: BeaconState) returns (s' : BeaconState)
        requires |s.validators| == |s.balances| 
        requires is_valid_state_epoch_attestations(s)

        ensures |s'.validators| == |s'.balances| 
        ensures s' == updateSlashings(s)
        ensures is_valid_state_epoch_attestations(s')
    {
        var epoch := get_current_epoch(s);
        var total_balance := get_total_active_balance_full(s);
        var sumSlashings := get_total_slashings(s.slashings);
        var adjusted_total_slashing_balance := 
            min((sumSlashings as nat * PROPORTIONAL_SLASHING_MULTIPLIER as nat) as nat, 
                total_balance as nat) as Gwei;
        var increment := EFFECTIVE_BALANCE_INCREMENT;  
        // Factored out from penalty numerator to avoid uint64 overflow
        
        assert total_balance > 0 as Gwei;
        assert increment > 0 as Gwei;
        AssumeNoGweiOverflowToUpdateSlashings(s.validators, 
                                              adjusted_total_slashing_balance as nat, 
                                              total_balance as nat);
        AssumeNoEpochOverflow(epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2);

        s' := s;
        var i := 0;
        assert s' == updateSlashingsHelper(s, 
                                           i, 
                                           epoch, 
                                           total_balance, 
                                           adjusted_total_slashing_balance, 
                                           increment);

        while i < |s'.balances|
            invariant  |s.validators| == |s.balances| ==|s'.balances| == |s'.validators|
            invariant i <= |s'.validators| == |s'.balances| 
            //invariant forall v :: i <= v < |s.balances| ==> s'.balances[v] ==  s.balances[v]
            //invariant s' == s.(balances := s'.balances)
            invariant s' == updateSlashingsHelper(s, 
                                                  i, 
                                                  epoch, 
                                                  total_balance, 
                                                  adjusted_total_slashing_balance, 
                                                  increment)
        {
            if (s'.validators[i].slashed && (epoch + EPOCHS_PER_SLASHINGS_VECTOR / 2) 
                == s'.validators[i].withdrawable_epoch) {
                    s' := decrease_balance(s', 
                                           i as ValidatorIndex, 
                                           (s.validators[i].effective_balance as nat 
                                            * adjusted_total_slashing_balance as nat 
                                            / total_balance  as nat) as Gwei
                                          );
            }
            
            i := i + 1;
        }
        assert s' == updateSlashingsHelper(s, 
                                           i, 
                                           epoch, 
                                           total_balance, 
                                           adjusted_total_slashing_balance, 
                                           increment);
        assert i == |s'.validators|;
        assert s' == updateSlashings(s);
    }

    /** 
     *  Process eth1 data reset.
     *  
     *  @param  s   A state.
     *  @returns    The state obtained after applying the epoch eth1 data reset.
     */
    method process_eth1_data_reset(s: BeaconState) returns (s' : BeaconState)
        requires is_valid_state_epoch_attestations(s)

        ensures s' == updateEth1DataReset(s)
        ensures is_valid_state_epoch_attestations(s')
    {
        var next_epoch := get_current_epoch(s) + 1;
        // Reset eth1 data votes
        if (next_epoch % EPOCHS_PER_ETH1_VOTING_PERIOD) == 0 {
            s' := s.(eth1_data_votes := []);
        }
        else {s' := s;}
    }
    
    /** 
     *  Process effective balance updates.
     *  
     *  @param  s   A state.
     *  @returns    The state obtained after applying the epoch effective balance updates
     *
     *  @note       This function uses axiom AssumeNoGweiOverflowToUpdateEffectiveBalance.
     *  @note       This axiom is used as a simplification to ensure that balance 
     *              overflows don't occur. To remove this axiom a strategy similar
     *              to that applied within the deposit processing could be applied.      
     */
    method process_effective_balance_updates(s: BeaconState) returns (s' : BeaconState)
        requires |s.validators| == |s.balances| 
        requires is_valid_state_epoch_attestations(s)

        ensures |s'.validators| == |s'.balances| 
        ensures is_valid_state_epoch_attestations(s')
        ensures s' == updateEffectiveBalance(s)
    {
        AssumeNoGweiOverflowToUpdateEffectiveBalance(s.balances);

        var HYSTERESIS_INCREMENT := EFFECTIVE_BALANCE_INCREMENT / HYSTERESIS_QUOTIENT;
        var down := HYSTERESIS_INCREMENT * HYSTERESIS_DOWNWARD_MULTIPLIER;
        var up := HYSTERESIS_INCREMENT * HYSTERESIS_UPWARD_MULTIPLIER;

        s' := s;
        var i := 0;
        assert s' == updateEffectiveBalanceHelper(s, i, up as nat, down as nat);

        while i < |s'.balances|
            invariant  |s.validators| == |s.balances| ==|s'.balances| == |s'.validators|
            invariant i <= |s'.validators| == |s'.balances| 
            invariant forall v :: i <= v < |s.validators| ==> s'.validators[v] == s.validators[v]
            invariant forall v :: 0 <= v < |s.validators| ==> s'.balances[v] == s.balances[v]
            invariant is_valid_state_epoch_attestations(s')
            invariant s' == updateEffectiveBalanceHelper(s, i, up as nat, down as nat)
        {
            assert EFFECTIVE_BALANCE_INCREMENT > 0;
            
            if (s.balances[i] as nat + down as nat < s.validators[i].effective_balance as nat) 
                || (s.validators[i].effective_balance as nat + up as nat < s.balances[i] as nat) {
                    var new_bal 
                        := min((s.balances[i] - (s.balances[i] % EFFECTIVE_BALANCE_INCREMENT)) as nat, 
                                MAX_EFFECTIVE_BALANCE as nat);
                    s' := set_effective_balance(s', i as ValidatorIndex, new_bal as Gwei);
            }
            
            i := i + 1;
            assert s' == updateEffectiveBalanceHelper(s, i, up as nat, down as nat);

        }
        assert s' == updateEffectiveBalanceHelper(s, i, up as nat, down as nat);
        assert i == |s'.validators|;
        assert s' == updateEffectiveBalance(s);
    }
    
    /** 
     *  Process slashings reset.
     *  
     *  @param  s   A state.
     *  @returns    The state obtained after applying the epoch slashings reset.
     */
    method process_slashings_reset(s: BeaconState) returns (s' : BeaconState)
        requires is_valid_state_epoch_attestations(s)

        ensures s' == updateSlashingsReset(s)
        ensures is_valid_state_epoch_attestations(s')
    {
        var next_epoch := get_current_epoch(s) + 1;
        // Reset slashings
        s' := s.(
                slashings 
                    := s.slashings[(next_epoch % EPOCHS_PER_SLASHINGS_VECTOR) as nat := 0 as Gwei]
            );
    }

    /** 
     *  Process randao mixes reset.
     *  
     *  @param  s   A state.
     *  @returns    The state obtained after applying the epoch randao mixes reset.
     */
    method process_randao_mixes_reset(s: BeaconState) returns (s' : BeaconState)
        requires is_valid_state_epoch_attestations(s)

        ensures s' == updateRandaoMixes(s)
        ensures is_valid_state_epoch_attestations(s')
    {
        var current_epoch := get_current_epoch(s);
        var next_epoch := current_epoch + 1;
        s' := s.(
                randao_mixes := s.randao_mixes[
                            (next_epoch % EPOCHS_PER_HISTORICAL_VECTOR) as nat 
                                := get_randao_mix(s, current_epoch)
                        ]
            );
    }
    
    // /** 
    //  *  Process the historical roots update.
    //  *  
    //  *  @param  s   A state.
    //  *  @returns    The state obtained after applying the epoch historical roots update.
    //  */
    // method process_historical_roots_update(s: BeaconState) returns (s' : BeaconState)
    //     requires is_valid_state_epoch_attestations(s)

    //     ensures s' == updateHistoricalRoots(s)
    //     ensures is_valid_state_epoch_attestations(s')
    // {
    //     // Set historical root accumulator
    //     var next_epoch := (get_current_epoch(s) + 1) as Epoch;
    //     if next_epoch % (SLOTS_PER_HISTORICAL_ROOT / SLOTS_PER_EPOCH) == 0 {
    //         var historical_batch := HistoricalBatch(s.block_roots, s.state_roots);
    //         s' := s.(
    //             historical_roots := s.historical_roots + [hash(historical_batch)]
    //         );
    //     }
    //     else  {s' := s;}
    // }


    /** 
     *
     */
    method process_historical_summaries_update(s: BeaconState) returns (s': BeaconState)
        requires is_valid_state_epoch_attestations(s)

        // ensures s' == updateHistoricalSummaries(s)
        // ensures is_valid_state_epoch_attestations(s')
    {
        var next_epoch := (get_current_epoch(s) + 1) as Epoch;
        if next_epoch % (SLOTS_PER_HISTORICAL_ROOT / SLOTS_PER_EPOCH) == 0 {
            var historical_summary := HistoricalSummary(s.block_roots, s.state_roots);
            if |s.historical_summaries| <= 100 {
                s' := s.(
                    historical_summaries := s.historical_summaries + [(historical_summary)]
                );
            }
            else {
                s' := s;
            }
        }
        else {
            s' := s;
        }
    }


    /**
     *  Rotate the attestations.
     *  @param  s   A state.
     *  @return    `s` with attestations rotated.
     */
    method process_participation_record_updates(s: BeaconState) returns (s' : BeaconState)
        requires is_valid_state_epoch_attestations(s)

        ensures s' == updateParticipationRecords(s)
        ensures is_valid_state_epoch_attestations(s')
    {
        s' := s.(
            previous_epoch_attestations := s.current_epoch_attestations,
            current_epoch_attestations := []
        );
    }
    
}
