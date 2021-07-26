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

include "../../utils/Eth2Types.dfy"
include "../../utils/MathHelpers.dfy"
include "../../utils/NativeTypes.dfy"
include "../../ssz/Constants.dfy"

include "../BeaconChainTypes.dfy"
include "Validators.dfy"
include "../attestations/AttestationsTypes.dfy"
//include "ValidatorHelpers.p.dfy"
include "../Helpers.dfy"



/**
 *  Beacon chain helper functional specifications.
 */
module ValidatorHelpers {

    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened MathHelpers
    import opened NativeTypes
    import opened Constants

    import opened BeaconChainTypes
    import opened Validators
    import opened AttestationsTypes
    import opened BeaconHelpers

    /**
     *  Check if there is at least one active validator.
     *
     *  @param      s   A beacon state.
     *  @returns        True if 
     *                  |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0,
     *                  otherwise False.
     */
    predicate minimumActiveValidators(s: BeaconState)
    {
        |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
    }
    
    /** initiate_validator_exit
     *  
     *  Initiate the exit of the validator with index ``index``.
     *
     */
    function method initiate_validator_exit(s: BeaconState, index: ValidatorIndex) : BeaconState
        requires |s.validators| == |s.balances|
        requires index as int < |s.validators| 
        //requires s.validators[index].exitEpoch == FAR_FUTURE_EPOCH

        ensures |s.validators| == |initiate_validator_exit(s,index).validators|
        ensures |initiate_validator_exit(s,index).validators| == |initiate_validator_exit(s,index).balances|
        ensures initiate_validator_exit(s,index).validators[index].exitEpoch > get_current_epoch(s) + MAX_SEED_LOOKAHEAD
                || initiate_validator_exit(s,index).validators[index].exitEpoch == s.validators[index].exitEpoch
        ensures forall i :: (0 <= i < |s.validators|) && (i != index as int) ==> 
                initiate_validator_exit(s,index).validators[i].exitEpoch == s.validators[i].exitEpoch
        ensures initiate_validator_exit(s,index).validators[index].exitEpoch < FAR_FUTURE_EPOCH
    {
        // # Return if validator already initiated exit
        // validator = state.validators[index]
        if s.validators[index].exitEpoch != FAR_FUTURE_EPOCH then
            s
        else 
        //     return
        //assert s.validators[index].exitEpoch == FAR_FUTURE_EPOCH;
        
        // # Compute exit queue epoch
        // exit_epochs = [v.exit_epoch for v in state.validators if v.exit_epoch != FAR_FUTURE_EPOCH]
        var exit_epochs := get_exit_epochs(s.validators);
        
        // exit_queue_epoch = max(exit_epochs + [compute_activation_exit_epoch(get_current_epoch(state))])
        var exit_queue_epoch := max_epoch(exit_epochs + [compute_activation_exit_epoch(get_current_epoch(s))]);

        assert compute_activation_exit_epoch(get_current_epoch(s)) > get_current_epoch(s) + MAX_SEED_LOOKAHEAD;
        assert compute_activation_exit_epoch(get_current_epoch(s)) in exit_epochs + [compute_activation_exit_epoch(get_current_epoch(s))];
        assert max_epoch(exit_epochs + [compute_activation_exit_epoch(get_current_epoch(s))]) >= compute_activation_exit_epoch(get_current_epoch(s));
        assert exit_queue_epoch > get_current_epoch(s) + MAX_SEED_LOOKAHEAD;

        // exit_queue_churn = len([v for v in state.validators if v.exit_epoch == exit_queue_epoch])
        var exit_queue_churn := |get_queue_churn(s.validators, exit_queue_epoch)|;
        var validator_churn_limit := get_validator_churn_limit(s);

        // if exit_queue_churn >= get_validator_churn_limit(state):
        //     exit_queue_epoch += Epoch(1)

        // # Set validator exit epoch and withdrawable epoch
        // validator.exit_epoch = exit_queue_epoch
        // validator.withdrawable_epoch = Epoch(validator.exit_epoch + MIN_VALIDATOR_WITHDRAWABILITY_DELAY)

        assume exit_queue_epoch as int + 1 + MIN_VALIDATOR_WITHDRAWABILITY_DELAY as nat < 0x10000000000000000; 

        if exit_queue_churn  >= get_validator_churn_limit(s) as nat then 
            s.(validators := s.validators[index as int := s.validators[index].(exitEpoch := exit_queue_epoch + 1 as Epoch,
                                                            withdrawable_epoch := (exit_queue_epoch as nat + 1 + MIN_VALIDATOR_WITHDRAWABILITY_DELAY as nat) as Epoch)])
        else
            s.(validators := s.validators[index as int := s.validators[index].(exitEpoch := exit_queue_epoch,
                                                            withdrawable_epoch := (exit_queue_epoch as nat + MIN_VALIDATOR_WITHDRAWABILITY_DELAY as nat) as Epoch)])
    }


        /** slash_validator
     *  
     *  Slash the validator with index ``slashed_index``.
     */
    function method slash_validator(s: BeaconState, slashed_index: ValidatorIndex, whistleblower_index: ValidatorIndex): BeaconState
        requires slashed_index as int < |s.validators| 
        requires whistleblower_index as int < |s.validators| 
        requires |s.validators| == |s.balances|
        //requires s.validators[slashed_index].exitEpoch == FAR_FUTURE_EPOCH
        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        //ensures |get_active_validator_indices(slash_validator(s,slashed_index,whistleblower_index).validators, get_current_epoch(s))| > 0
        ensures slash_validator(s, slashed_index, whistleblower_index).slot == s.slot
    {
        var epoch : Epoch := get_current_epoch(s);
        var proposer_index := get_beacon_proposer_index(s);

        var s' := initiate_validator_exit(s, slashed_index); // only validator exitEpoch & withdrawable_epoch fields possibly changed

        assert |s.balances| == |s'.balances|;
        assert |s'.balances| == |s'.validators|;
        assert get_current_epoch(s) == get_current_epoch(s');
        
        //assert initiate_validator_exit(s,slashed_index).validators[slashed_index].exitEpoch > get_current_epoch(s) + MAX_SEED_LOOKAHEAD;
        assert forall i :: (0 <= i < |s.validators|) && (i != slashed_index as int) ==> 
                initiate_validator_exit(s,slashed_index).validators[i].exitEpoch == s.validators[i].exitEpoch;
        
        //assert s'.validators[slashed_index].exitEpoch > get_current_epoch(s) + MAX_SEED_LOOKAHEAD;
        assert forall i :: (0 <= i < |s.validators|) && (i != slashed_index as int) ==> 
                s'.validators[i].exitEpoch == s.validators[i].exitEpoch;
        
        assert forall i :: (0 <= i < |s'.validators|) ==> 
                is_active_validator(s.validators[i], get_current_epoch(s)) == is_active_validator(s'.validators[i], get_current_epoch(s'));

        initiateValidatorExitPreservesActivateValidators(s.validators, s'.validators,  get_current_epoch(s'));
        assert get_active_validator_indices(s'.validators, get_current_epoch(s')) == get_active_validator_indices(s.validators, get_current_epoch(s));
        assert |get_active_validator_indices(s'.validators, get_current_epoch(s'))| > 0;
        
        // NOTE:    steps reordered to suit Dafny function method output
        //          order irrelevant as 'Apply proposer and whistleblower rewards' relies only on s'.validators[slashed_index].effective_balance

        // # Apply proposer and whistleblower rewards
        
        // if whistleblower_index is None:
        //     whistleblower_index = proposer_index
        // Note: 'None' is not available in Dafny and so functions that call slash_validator will have this parameter set to proposer_index
        
        
        // NOTE: there doesn't seem to be anything to check that the validator being slashed isn't the proposer of the block that contains the ps
        // though it makes sense that a validator wouldn't proposer to slash itself!
        // assert slashed_index != whistleblower_index;

        var whistleblower_reward : Gwei := (s'.validators[slashed_index].effective_balance as int / WHISTLEBLOWER_REWARD_QUOTIENT as nat) as Gwei;
        var proposer_reward := (whistleblower_reward as int / PROPOSER_REWARD_QUOTIENT as int) as Gwei;
        var validator_penalty := (s'.validators[slashed_index].effective_balance as int / MIN_SLASHING_PENALTY_QUOTIENT as nat) as Gwei;

        //s' := increase_balance(s', proposer_index, proposer_reward);
        //s' := increase_balance(s', whistleblower_index, Gwei(whistleblower_reward - proposer_reward));
        
        //var validator := s'.validators[slashed_index];
        // validator.slashed = True
        // validator.withdrawable_epoch = max(validator.withdrawable_epoch, Epoch(epoch + EPOCHS_PER_SLASHINGS_VECTOR))
        // state.slashings[epoch % EPOCHS_PER_SLASHINGS_VECTOR] += validator.effective_balance

        assume (s'.slashings[epoch as int % EPOCHS_PER_SLASHINGS_VECTOR as nat] as int + s'.validators[slashed_index].effective_balance as int) < 0x10000000000000000;
        assert slashed_index as int < |s'.balances|; 
        assert proposer_index as int < |s'.balances|; 
        assert whistleblower_index as int < |s'.balances|; 
        assume s'.balances[proposer_index] as int + proposer_reward as int < 0x10000000000000000;
        // Note: if proposer_index == whistleblower_index then the following assume statement is required rather than
        // assume s'.balances[whistleblower_index] as int + (whistleblower_reward - proposer_reward) as int < 0x10000000000000000;
        // The following assume statement covers both cases and will be replaced at a later date by functionality that
        // takes into account the total amount of Eth available.
        assume s'.balances[whistleblower_index] as int + whistleblower_reward  as int < 0x10000000000000000;

        s'.(validators := s'.validators[slashed_index := s'.validators[slashed_index].(slashed := true,
                                                            withdrawable_epoch := max(s'.validators[slashed_index].withdrawable_epoch as nat,(epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat)) as Epoch)],
            slashings := s'.slashings[(epoch as int % EPOCHS_PER_SLASHINGS_VECTOR as nat) := s'.slashings[epoch as int % EPOCHS_PER_SLASHINGS_VECTOR as nat] + s'.validators[slashed_index].effective_balance],
            balances := increase_balance(
                            increase_balance(
                                decrease_balance(s', slashed_index, validator_penalty), 
                                proposer_index, 
                                proposer_reward), 
                            whistleblower_index, 
                            (whistleblower_reward - proposer_reward)).balances)
            
        
        // the triple nested mutation of balances is somewhat messy but for the moment it allows slashed_validator to remain as a function method 
        //(rather than a method)

    }

     // Beacon State Mutators

/** increase_balance
     *  Increase the validator balance at index ``index`` by ``delta``.
     *
     *  @notes  The datatype Gwei has temporarily been changed from uint64 to nat so as to simplify the
     *          properties required to process a deposit. Hence a further requires will be needed to prevent
     *          overflow once this temporary simplification is removed.
     *  
     **/
    // function method increase_balance(s: BeaconState, index: ValidatorIndex, delta: Gwei): BeaconState 
    //     requires index as int < |s.balances| 
    //     requires s.balances[index] as int + delta as int < 0x10000000000000000
    //     ensures |s.balances| == |increase_balance(s,index,delta).balances|
    //     ensures increase_balance(s,index,delta).balances[index] == s.balances[index] + delta
    // {
    //     s.(
    //         balances := s.balances[index as int := (s.balances[index] + delta)]
    //     )
    // }

    /** increase_balance
     *  Increase the validator balance at index ``index`` by ``delta``.
     *  
     **/
    function method increase_balance(s: BeaconState, index: ValidatorIndex, delta: Gwei): BeaconState 
        requires index as int < |s.balances| 
        requires s.balances[index] as int + delta as int < 0x10000000000000000
        ensures |s.balances| == |increase_balance(s,index,delta).balances|
        ensures increase_balance(s,index,delta).balances[index] == s.balances[index] + delta
    {
        s.(
            balances := s.balances[index as int := (s.balances[index] + delta)]
        )
    }

    /** decrease_balance
     *  Decrease the validator balance at index ``index`` by ``delta``.
     *
     **/
    function method decrease_balance(s: BeaconState, index: ValidatorIndex, delta: Gwei): BeaconState 
        requires index as int < |s.balances| 
        ensures |s.balances| == |decrease_balance(s,index,delta).balances|
        ensures if s.balances[index] > delta then decrease_balance(s,index,delta).balances[index] == s.balances[index] - delta
                else decrease_balance(s,index,delta).balances[index] == 0
        ensures s.validators == decrease_balance(s,index,delta).validators
    {
        if s.balances[index] > delta then
            s.(
                balances := s.balances[index as int := (s.balances[index] - delta)]
            )
        else
            s.(
                balances := s.balances[index as int := 0]
            )
    }


function total_deposits(deposits: seq<Deposit>): nat
    {
        if |deposits| == 0 then 0
        //else deposits[0].data.amount as nat + total_deposits(deposits[1..])
        else total_deposits(deposits[..|deposits|-1]) + deposits[|deposits|-1].data.amount as nat
    }

    function total_balances(bal: seq<Gwei>): nat
    {
        if |bal| == 0 then 0
        else bal[0] as nat + total_balances(bal[1..])
    }


    lemma slash_validator_lemma(s: BeaconState, slashed_index: ValidatorIndex, whistleblower_index: ValidatorIndex)
        requires slashed_index as int < |s.validators| 
        requires whistleblower_index as int < |s.validators| 
        requires |s.validators| == |s.balances|
        //requires s.validators[slashed_index].exitEpoch == FAR_FUTURE_EPOCH
        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        ensures slash_validator(s, slashed_index, whistleblower_index).validators[slashed_index].slashed
    {

    }


    lemma slashValidatorPreservesMinimumActiveValidators(s: BeaconState, slashed_index: ValidatorIndex, whistleblower_index: ValidatorIndex)
        requires slashed_index as int < |s.validators| 
        requires whistleblower_index as int < |s.validators| 
        requires |s.validators| == |s.balances|
        //requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires minimumActiveValidators(s)
        
        ensures minimumActiveValidators(slash_validator(s,slashed_index,whistleblower_index))
    {
        slashValidatorPreservesActivateValidators(s, slashed_index, whistleblower_index);
    }

    // ?? prove that the only way slashed is set to true is by calling slash_validator?? 
    
    lemma slashValidatorPreservesActivateValidators(s: BeaconState, slashed_index: ValidatorIndex, whistleblower_index: ValidatorIndex)
        requires slashed_index as int < |s.validators| 
        requires whistleblower_index as int < |s.validators| 
        requires |s.validators| == |s.balances|
        //requires s.validators[slashed_index].exitEpoch == FAR_FUTURE_EPOCH
        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        
        ensures get_active_validator_indices(s.validators, get_current_epoch(s)) ==
                    get_active_validator_indices(slash_validator(s,slashed_index,whistleblower_index).validators, get_current_epoch(s))
    {
        
        var epoch : Epoch := get_current_epoch(s);
        var proposer_index := get_beacon_proposer_index(s);
        var s' := initiate_validator_exit(s, slashed_index); // only validator exitEpoch & withdrawable_epoch fields possibly changed

        // show initiate validator exit doesn't change the set of active validator indices
        
        assert |s.balances| == |s'.balances|;
        assert |s'.balances| == |s'.validators|;
        assert epoch == get_current_epoch(s');
        
        //assert initiate_validator_exit(s,slashed_index).validators[slashed_index].exitEpoch > epoch + MAX_SEED_LOOKAHEAD;
        assert forall i :: (0 <= i < |s.validators|) && (i != slashed_index as int) ==> 
                initiate_validator_exit(s,slashed_index).validators[i].exitEpoch == s.validators[i].exitEpoch;
        
        //assert s'.validators[slashed_index].exitEpoch > epoch + MAX_SEED_LOOKAHEAD;
        assert forall i :: (0 <= i < |s.validators|) && (i != slashed_index as int) ==> 
                s'.validators[i].exitEpoch == s.validators[i].exitEpoch;
        
        assert forall i :: (0 <= i < |s'.validators|) ==> 
                is_active_validator(s.validators[i], epoch) == is_active_validator(s'.validators[i], epoch);

        initiateValidatorExitPreservesActivateValidators(s.validators, s'.validators, epoch);
        assert get_active_validator_indices(s'.validators, epoch) == get_active_validator_indices(s.validators, epoch);
        assert |get_active_validator_indices(s'.validators, epoch)| > 0;

        // show update to s', including rewards/penalties, doesn't change the set of active validator indices
        var whistleblower_reward : Gwei := (s'.validators[slashed_index].effective_balance as int / WHISTLEBLOWER_REWARD_QUOTIENT as nat) as Gwei;
        var proposer_reward := (whistleblower_reward as int / PROPOSER_REWARD_QUOTIENT as int) as Gwei;
        var validator_penalty := (s'.validators[slashed_index].effective_balance as int / MIN_SLASHING_PENALTY_QUOTIENT as nat) as Gwei;

        assume (s'.slashings[epoch as int % EPOCHS_PER_SLASHINGS_VECTOR as nat] as int + s'.validators[slashed_index].effective_balance as int) < 0x10000000000000000;
        assert slashed_index as int < |s'.balances|; 
        assert proposer_index as int < |s'.balances|; 
        assert whistleblower_index as int < |s'.balances|; 
        
        assume s'.balances[proposer_index] as int + proposer_reward as int < 0x10000000000000000;
        assume s'.balances[whistleblower_index] as int + whistleblower_reward  as int < 0x10000000000000000;


        s' := s'.(  validators := s'.validators[slashed_index := s'.validators[slashed_index].(slashed := true,
                                                            withdrawable_epoch := max(s'.validators[slashed_index].withdrawable_epoch as nat,(epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat)) as Epoch)],
                    slashings := s'.slashings[(epoch as int % EPOCHS_PER_SLASHINGS_VECTOR as nat) := s'.slashings[epoch as int % EPOCHS_PER_SLASHINGS_VECTOR as nat] + s'.validators[slashed_index].effective_balance],
                    balances := increase_balance(
                                    increase_balance(
                                        decrease_balance(s', slashed_index, validator_penalty), 
                                        proposer_index, 
                                        proposer_reward), 
                                    whistleblower_index, 
                                    (whistleblower_reward - proposer_reward)).balances);
        
        //assert s'.validators[slashed_index].exitEpoch > epoch + MAX_SEED_LOOKAHEAD;
        assert forall i :: (0 <= i < |s.validators|) && (i != slashed_index as int) ==> 
                s'.validators[i].exitEpoch == s.validators[i].exitEpoch;

        assert forall i :: (0 <= i < |s'.validators|) ==> 
                is_active_validator(s.validators[i], epoch) == is_active_validator(s'.validators[i], epoch);

        assert s' == slash_validator(s,slashed_index,whistleblower_index);
        
        sameActiveValidatorsImpliesSameActiveValidatorIndices(s.validators, s'.validators, epoch);
        assert get_active_validator_indices(s'.validators, epoch) == get_active_validator_indices(s.validators, epoch);
    }

    // is_valid_indexed_attestation
    // Check if ``indexed_attestation`` is not empty, has sorted and unique indices and has a valid aggregate signature.
    // Note: at this time only the first part of the check is being implemented

    lemma valid_indexed_attestation_lemma(s: BeaconState, s': BeaconState, indexed_attestation: IndexedAttestation)
        requires is_valid_indexed_attestation(s,indexed_attestation) 
        ensures is_valid_indexed_attestation(s',indexed_attestation)
    {
        // Thanks Dafny
    }

    lemma initiateValidatorExitPreservesActivateValidators(sv: ListOfValidators, sv': ListOfValidators, epoch: Epoch)
        requires |sv| == |sv'|
        requires forall i :: (0 <= i < |sv'|) ==> 
                is_active_validator(sv[i], epoch) == is_active_validator(sv'[i], epoch)
        ensures get_active_validator_indices(sv', epoch) == get_active_validator_indices(sv, epoch)
    {
        if |sv'| == 0 {
            assert get_active_validator_indices(sv', epoch) == get_active_validator_indices(sv, epoch);
        }
        else {
            assert get_active_validator_indices(sv', epoch) == 
                if is_active_validator(sv'[|sv'|-1], epoch) then 
                    get_active_validator_indices(sv'[..|sv'|-1], epoch) + [(|sv'|-1) as ValidatorIndex]
                else 
                    get_active_validator_indices(sv'[..|sv'|-1], epoch);
            
            assert get_active_validator_indices(sv', epoch) == 
                if is_active_validator(sv[|sv|-1], epoch) then 
                    get_active_validator_indices(sv'[..|sv'|-1], epoch) + [(|sv'|-1) as ValidatorIndex]
                else 
                    get_active_validator_indices(sv'[..|sv'|-1], epoch);

            assert |sv| == |sv'|;
            assert get_active_validator_indices(sv', epoch) == 
                if is_active_validator(sv[|sv|-1], epoch) then 
                    get_active_validator_indices(sv'[..|sv|-1], epoch) + [(|sv|-1) as ValidatorIndex]
                else 
                    get_active_validator_indices(sv'[..|sv|-1], epoch);
            initiateValidatorExitPreservesActivateValidators(sv[..|sv|-1], sv'[..|sv|-1], epoch);
        }
    }

    
    lemma sameActiveValidatorsImpliesSameActiveValidatorIndices(sv1: ListOfValidators, sv2: ListOfValidators, epoch: Epoch)
        requires |sv1| == |sv2|   
        requires forall i :: (0 <= i < |sv1|) ==> is_active_validator(sv1[i], epoch) == is_active_validator(sv2[i], epoch)
        ensures get_active_validator_indices(sv1, epoch) == get_active_validator_indices(sv2, epoch)
    {
        if |sv1| == 0 {
            assert get_active_validator_indices(sv2, epoch) == get_active_validator_indices(sv1, epoch);
        }
        else {
            sameActiveValidatorsImpliesSameActiveValidatorIndices(sv1[..|sv1|-1], sv2[..|sv2|-1], epoch);
        }
    }


    lemma individualBalanceBoundMaintained(sb: seq<Gwei>, d: Deposit)
        requires total_balances(sb) + d.data.amount as int < 0x10000000000000000
        ensures forall i :: 0 <= i < |sb| ==> sb[i] as int + d.data.amount as int < 0x10000000000000000
    {
        if |sb| == 0 {
            // Thanks Dafny
        }
        else {
            assert total_balances(sb) == sb[0] as int + total_balances(sb[1..]);
            assert sb[0] as int + d.data.amount as int < 0x10000000000000000;
            assert total_balances(sb[1..]) + d.data.amount as int < 0x10000000000000000;
            individualBalanceBoundMaintained(sb[1..],d);
        }
    } 

    


    
    lemma updateExistingBalance(s: BeaconState, index: ValidatorIndex, delta: Gwei)
        requires index as int < |s.balances| 
        requires s.balances[index] as int + delta as int < 0x10000000000000000
        requires |s.balances| < VALIDATOR_REGISTRY_LIMIT as int

        ensures total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances) + delta as int
    {
        //assert increase_balance(s,index,delta).balances[index] == s.balances[index] + delta;
        //assert forall i :: 0 <= i < |s.balances| && i != index as int ==> increase_balance(s,index,delta).balances[i] == s.balances[i];

        if index as int < |s.balances|-1 {
            assert increase_balance(s,index,delta).balances == increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]] + increase_balance(s,index,delta).balances[(index+1)..];
                                                                
            //assert total_balances(increase_balance(s,index,delta).balances[..index]) == total_balances(s.balances[..index]);
            //assert total_balances([increase_balance(s,index,delta).balances[index]]) == total_balances([s.balances[index]]) + delta as int;
            //assert total_balances(increase_balance(s,index,delta).balances[(index+1)..]) == total_balances(s.balances[(index+1)..]);

            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]] + increase_balance(s,index,delta).balances[(index+1)..]);

            distBalancesProp(increase_balance(s,index,delta).balances[..index], [increase_balance(s,index,delta).balances[index]]);
            //assert total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]]) == total_balances(increase_balance(s,index,delta).balances[..index]) + total_balances([increase_balance(s,index,delta).balances[index]]);
            distBalancesProp(increase_balance(s,index,delta).balances[..index]+[increase_balance(s,index,delta).balances[index]], increase_balance(s,index,delta).balances[(index+1)..]);
            //assert total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]] + increase_balance(s,index,delta).balances[(index+1)..]) == total_balances(increase_balance(s,index,delta).balances[..index]) + total_balances([increase_balance(s,index,delta).balances[index]]) + total_balances(increase_balance(s,index,delta).balances[index+1..]);

            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(increase_balance(s,index,delta).balances[..index]) + total_balances([increase_balance(s,index,delta).balances[index]]) + total_balances(increase_balance(s,index,delta).balances[index+1..]);
            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]) + delta as int + total_balances(s.balances[(index+1)..]);

            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]) + total_balances(s.balances[(index+1)..]) + delta as int;

            assert s.balances == s.balances[..index] + [s.balances[index]] + s.balances[(index+1)..];
            //assert total_balances(s.balances) == total_balances(s.balances[..index] + [s.balances[index]] + s.balances[(index+1)..]);

            distBalancesProp(s.balances[..index], [s.balances[index]]);
            //assert total_balances(s.balances[..index] + [s.balances[index]]) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]);
            distBalancesProp(s.balances[..index]+[s.balances[index]], s.balances[(index+1)..]);
            //assert total_balances(s.balances[..index] + [s.balances[index]] + s.balances[(index+1)..]) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]) + total_balances(s.balances[index+1..]);

            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances) + delta as int;
        }
        else {
            //assert index as int == |s.balances| - 1;
            assert increase_balance(s,index,delta).balances == increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]];
                                                                
            //assert total_balances(increase_balance(s,index,delta).balances[..index]) == total_balances(s.balances[..index]);
            //assert total_balances([increase_balance(s,index,delta).balances[index]]) == total_balances([s.balances[index]]) + delta as int;
            
            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]]);

            distBalancesProp(increase_balance(s,index,delta).balances[..index], [increase_balance(s,index,delta).balances[index]]);
            //assert total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]]) == total_balances(increase_balance(s,index,delta).balances[..index]) + total_balances([increase_balance(s,index,delta).balances[index]]);
            
            
            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]) + delta as int;

            assert s.balances == s.balances[..index] + [s.balances[index]] ;
            //assert total_balances(s.balances) == total_balances(s.balances[..index] + [s.balances[index]]);

            distBalancesProp(s.balances[..index], [s.balances[index]]);
            //assert total_balances(s.balances[..index] + [s.balances[index]]) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]);
            
            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances) + delta as int;
        }
    }

    lemma distBalancesProp(sb1: seq<Gwei>, sb2: seq<Gwei>)
        ensures total_balances(sb1 + sb2) == total_balances(sb1) + total_balances(sb2) 
    {
        if |sb1| == 0 {
            assert sb1 + sb2 == sb2;
        }
        else {
            var sb := sb1 + sb2;
            //assert sb == [sb1[0]] +  sb1[1..] + sb2;
            assert sb[1..] == sb1[1..] + sb2;
            assert total_balances(sb) == sb[0] as int + total_balances(sb[1..]);
            //assert total_balances(sb1 + sb2) == sb[0] as int + total_balances(sb1[1..] + sb2);
            distBalancesProp(sb1[1..],sb2);

        }
    }

    lemma distDepositsProp(sd1: seq<Deposit>, sd2: seq<Deposit>)
        ensures total_deposits(sd1 + sd2) == total_deposits(sd1) + total_deposits(sd2) 
    {
        if |sd2| == 0 {
            assert sd1 + sd2 == sd1;
        }
        else {
            var sd := sd1 + sd2;
            //assert sd == sd1 + sd2[..|sd2|-1] +  [sd2[|sd2|-1]];
            assert sd[..|sd|-1] == sd1 + sd2[..|sd2|-1] ;
            assert total_deposits(sd) == total_deposits(sd[..|sd|-1]) + sd2[|sd2|-1].data.amount as int;
            //assert total_deposits(sd1 + sd2) == total_deposits(sd1 + sd2[..|sd2|-1] ) + sd2[|sd2|-1].data.amount as int;
            distDepositsProp(sd1, sd2[..|sd2|-1] );
        }
    }
    lemma subsetDepositSumProp(deposits: seq<Deposit>, i: nat)
        requires i <= |deposits|
        ensures total_deposits(deposits[..i]) <= total_deposits(deposits);
    {
        if i == |deposits| {
            assert deposits[..i] == deposits;
        }
        else {
            //assert i < |deposits|;
            assert deposits == deposits[..i] + deposits[i..];
            assert total_deposits(deposits) == total_deposits(deposits[..i] + deposits[i..]);
            distDepositsProp(deposits[..i], deposits[i..]);
            //assert total_deposits(deposits[..i] + deposits[i..]) == total_deposits(deposits[..i]) + total_deposits(deposits[i..]); 
        }
    }


    
}