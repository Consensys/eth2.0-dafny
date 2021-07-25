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

include "../utils/MathHelpers.dfy"
include "../utils/NativeTypes.dfy"

include "../ssz/Constants.dfy"

/**
 *  Proofs for misc helpers
 */
module BeaconHelperProofs {

    //  Import some constants, types and beacon chain helpers.
    import opened MathHelpers
    import opened NativeTypes

    import opened Constants
    
    /**
     *  A proof to  assist with the function method compute_committee
     *
     *  @param  len     A positive integer. 
     *  @param  index   A positive integer. 
     *  @param  count   A positive integer. 
     *  @return         A proof that if count > 0, (len * index / count) is a uint64,
     *                  and (len * (index+1) / count) is a uint64 then 
     *                  len * (index +1) / count >= len * index  / count.
     */
    lemma computeCommitteeLemma(len: nat, index: nat, count: nat)
        requires count > 0
        requires len * index / count  < 0x10000000000000000
        requires len * (index +1) / count < 0x10000000000000000
        ensures len * (index +1) / count >= len * index  / count
    {
        commonDivRule(len * (index +1), len * index, count);
    }

    /**
     *  A proof that if len_indices > 2^22 then at least one committee formed will be of a length that breaches 
     *  the upper bound of MAX_VALIDATORS_PER_COMMITTEE.
     *
     *  @param  len_indices     A positive integer representing the number of active validators. 
     *  @param  CPS             A positive integer representing the number of committees per slot. 
     *  @return                 A proof that if len_indices > 2^22 then at least one committee formed will be of 
     *                          a length that breaches the upper bound of MAX_VALIDATORS_PER_COMMITTEE.
     */
    lemma proveAtLeastOneCommitteeFormedBreachsBound(len_indices: nat, CPS: nat)
        requires TWO_UP_11 as nat * TWO_UP_11 as nat < len_indices 
        requires CPS == max(1, min(MAX_COMMITTEES_PER_SLOT as nat, len_indices/ SLOTS_PER_EPOCH  as nat/ TARGET_COMMITTEE_SIZE as nat) as nat)
        ensures 
            exists cIndex, slot  | 0 <= cIndex < CPS && 0 <= slot < SLOTS_PER_EPOCH as nat :: 
            ((len_indices * ((slot * CPS + cIndex) + 1) / (CPS * SLOTS_PER_EPOCH as nat)) - (len_indices * (slot * CPS + cIndex)  / (CPS * SLOTS_PER_EPOCH as nat)) > MAX_VALIDATORS_PER_COMMITTEE as nat)
    {
        assert CPS == 64;
        
        assert exists cIndex, slot  | 0 <= cIndex < CPS && 0 <= slot < SLOTS_PER_EPOCH as nat :: 
               ((len_indices * ((slot * CPS + cIndex) + 1) / (CPS * SLOTS_PER_EPOCH as nat)) - (len_indices * (slot * CPS + cIndex)  / (CPS * SLOTS_PER_EPOCH as nat)) > MAX_VALIDATORS_PER_COMMITTEE as nat)
               by
               {
                    assert 
                    (len_indices * ((31 * CPS + 63) + 1) / (CPS * SLOTS_PER_EPOCH as nat)) - (len_indices * (31 * CPS + 63)  / (CPS * SLOTS_PER_EPOCH as nat)) > MAX_VALIDATORS_PER_COMMITTEE as nat;
               }
    }

    /**
     *  A proof that if len_indices > 2^22 then at least one committee formed will be of a length that breaches 
     *  the upper bound of MAX_VALIDATORS_PER_COMMITTEE.
     *
     *  @param  len_indices     A positive integer representing the number of active validators. 
     *  @param  CPS             A positive integer representing the number of committees per slot. 
     *  @param  slot            A positive integer representing the slot. 
     *  @param  cIndex          A positive integer representing the committee index. 
     *  @return                 A proof that if len_indices >= ((2^22) + (2^11)) then all committees formed will be of 
     *                          a length that breaches the upper bound of MAX_VALIDATORS_PER_COMMITTEE.
     */
    lemma proveAllCommitteesFormedBreachBound(len_indices: nat, CPS: nat, slot: nat, cIndex: nat)
        requires TWO_UP_5 as nat <= len_indices 
        requires CPS == max(1, min(MAX_COMMITTEES_PER_SLOT as nat, len_indices/ SLOTS_PER_EPOCH  as nat/ TARGET_COMMITTEE_SIZE as nat) as nat)
        requires 0 <= slot < SLOTS_PER_EPOCH as nat// i.e. slot % SPE
        requires 0 <= cIndex < CPS

        ensures var start :=  (len_indices * (slot * CPS + cIndex) ) / (CPS * SLOTS_PER_EPOCH as nat);
                var end := (len_indices * ((slot * CPS + cIndex) + 1)) / (CPS * SLOTS_PER_EPOCH as nat);

                len_indices >= ((TWO_UP_11 * TWO_UP_11) + TWO_UP_11) as nat ==> end - start > MAX_VALIDATORS_PER_COMMITTEE as nat
                // at this point all committees formed will breach the maximum size bound
    {
        var start :=  (len_indices * (slot * CPS + cIndex) ) / (CPS * SLOTS_PER_EPOCH as nat);
        var end := (len_indices * ((slot * CPS + cIndex) + 1)) / (CPS * SLOTS_PER_EPOCH as nat);

        assert len_indices >= ((TWO_UP_11 * TWO_UP_11) + TWO_UP_11) as nat ==> end - start > MAX_VALIDATORS_PER_COMMITTEE as nat;
    }

    /**
     *  A proof that if 32 <= len_indices <= > 2^22 then all committees formed will be of 0 < length <= MAX_VALIDATORS_PER_COMMITTEE.
     *  i.e. a valid length
     *
     *  @param  len_indices     A positive integer representing the number of active validators. 
     *  @param  CPS             A positive integer representing the number of committees per slot. 
     *  @param  slot            A positive integer representing the slot. 
     *  @param  cIndex          A positive integer representing the committee index. 
     *  @return                 A proof that if 32 <= len_indices <= > 2^22 then all committees formed will be of a valid length.
     */
    lemma proveActiveValidatorsSatisfyBounds(len_indices: nat, CPS: nat, slot: nat, cIndex: nat)
        requires TWO_UP_5 as nat <= len_indices <= TWO_UP_11 as nat * TWO_UP_11 as nat // valid range for the number of active validators

        requires CPS == max(1, min(MAX_COMMITTEES_PER_SLOT as nat, len_indices/ SLOTS_PER_EPOCH  as nat/ TARGET_COMMITTEE_SIZE as nat) as nat)
        requires 0 <= slot < SLOTS_PER_EPOCH as nat;
        requires 0 <= cIndex < CPS;

        ensures var start :=  (len_indices * (slot * CPS + cIndex) ) / (CPS * SLOTS_PER_EPOCH as nat);
                var end := (len_indices * ((slot * CPS + cIndex) + 1)) / (CPS * SLOTS_PER_EPOCH as nat);
    
                0 < end - start <= MAX_VALIDATORS_PER_COMMITTEE as nat
    {
        var start :=  (len_indices * (slot * CPS + cIndex) ) / (CPS * SLOTS_PER_EPOCH as nat);
        var end := (len_indices * ((slot * CPS + cIndex) + 1)) / (CPS * SLOTS_PER_EPOCH as nat);

        //assert 63 * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat <= len_indices < 64 * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat ==> CPS == 63;
        //assert TWO_UP_18 as nat - TWO_UP_12 as nat <= len_indices < TWO_UP_18 as nat ==> CPS == 63;

        assert  TWO_UP_18 as nat <= len_indices ==> CPS == 64;
        assert TWO_UP_18 as nat <= len_indices <= TWO_UP_11 as nat * TWO_UP_11 as nat && CPS == 64 ==> 0 < end - start <= MAX_VALIDATORS_PER_COMMITTEE as nat;

        assert 63 * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat <= len_indices < TWO_UP_18 as nat && CPS == 63 ==> 0 < end - start <= MAX_VALIDATORS_PER_COMMITTEE as nat;

        //assert 62 * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat <= len_indices < 63 * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat && CPS == 62 ==> 
        //    0 < (len_indices * ((slot * CPS + cIndex) + 1)) / (CPS * SLOTS_PER_EPOCH as nat) - (len_indices * (slot * CPS + cIndex) ) / (CPS * SLOTS_PER_EPOCH as nat) <= MAX_VALIDATORS_PER_COMMITTEE as nat;

        //assert 61 * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat <= len_indices < 62 * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat && CPS == 61 ==> 
        //    0 < (len_indices * ((slot * CPS + cIndex) + 1)) / (CPS * SLOTS_PER_EPOCH as nat) - (len_indices * (slot * CPS + cIndex) ) / (CPS * SLOTS_PER_EPOCH as nat) <= MAX_VALIDATORS_PER_COMMITTEE as nat;

        assert forall i :: 2 <= i <= 63 && (i-1) * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat <= len_indices < i * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat ==> CPS == i-1 ;
        
        assert forall i :: 2 <= i <= 63 && (i-1) * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat <= len_indices < i * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat && CPS == i-1 ==> 
            0 < end - start <= MAX_VALIDATORS_PER_COMMITTEE as nat;


        assert len_indices < 2 * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat ==> CPS == 1;
        assert TWO_UP_5 as nat <= len_indices < 2 * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat && CPS == 1 ==> 0 < end - start <= MAX_VALIDATORS_PER_COMMITTEE as nat;

        assert TWO_UP_5 as nat <= len_indices <= TWO_UP_11 as nat * TWO_UP_11 as nat ==> 0 < end - start <= MAX_VALIDATORS_PER_COMMITTEE as nat;
    
        //assert TWO_UP_5 as nat <= len_indices <= TWO_UP_11 as nat * TWO_UP_11 as nat && CPS == max(1, min(MAX_COMMITTEES_PER_SLOT as nat, len_indices/ SLOTS_PER_EPOCH  as nat/ TARGET_COMMITTEE_SIZE as nat) as nat) 
        // ==> 
         //   0 < (len_indices * ((slot * CPS + cIndex) + 1)) / (CPS * SLOTS_PER_EPOCH as nat) - (len_indices * (slot * CPS + cIndex) ) / (CPS * SLOTS_PER_EPOCH as nat) <= MAX_VALIDATORS_PER_COMMITTEE as nat;

    }

    /**
     *   A proof to  assist with the function method get_beacon_committee.
     *
     *  @param  len_indices     A positive integer representing the number of active validators. 
     *  @param  CPS             A positive integer representing the number of committees per slot. 
     *  @param  slot            A positive integer representing the slot. 
     *  @param  cIndex          A positive integer representing the committee index. 
     *  @return                 A proof that len_indices * ((slot * CPS + cIndex) + 1) / (CPS * SLOTS_PER_EPOCH as nat) > len_indices * (slot * CPS + cIndex) / (CPS * SLOTS_PER_EPOCH as nat).
     */
    lemma getBeaconCommitteeLemma(len_indices: nat, CPS: nat, slot: nat, cIndex: nat)
        requires TWO_UP_5 as nat <= len_indices 
        requires CPS == max(1, min(MAX_COMMITTEES_PER_SLOT as nat, len_indices/ SLOTS_PER_EPOCH  as nat/ TARGET_COMMITTEE_SIZE as nat) as nat)
        requires 0 <= slot < SLOTS_PER_EPOCH as nat// i.e. slot % SPE
        requires 0 <= cIndex < CPS

        ensures len_indices * ((slot * CPS + cIndex) + 1) / (CPS * SLOTS_PER_EPOCH as nat) > len_indices * (slot * CPS + cIndex) / (CPS * SLOTS_PER_EPOCH as nat);
    {
        natRatioRule(len_indices * ((slot * CPS + cIndex) + 1), len_indices * (slot * CPS + cIndex) , (CPS * SLOTS_PER_EPOCH as nat));

        assert len_indices * ((slot * CPS + cIndex) + 1) - len_indices  * (slot * CPS + cIndex) >=  (CPS  * SLOTS_PER_EPOCH as nat) ==> 
                len_indices * ((slot * CPS + cIndex) + 1) / (CPS  * SLOTS_PER_EPOCH as nat) > len_indices * (slot * CPS + cIndex) / (CPS * SLOTS_PER_EPOCH as nat);

        calc {
            len_indices * ((slot * CPS + cIndex) + 1) - len_indices * (slot * CPS + cIndex);
            {natExpansion(len_indices as nat, (slot * CPS + cIndex));} len_indices * (slot * CPS + cIndex) + len_indices - len_indices * (slot * CPS + cIndex);
            len_indices as nat;
        }
        assert len_indices == len_indices * ((slot * CPS + cIndex) + 1) - len_indices * (slot * CPS + cIndex);

        assert len_indices >= (CPS * SLOTS_PER_EPOCH as nat) <==> len_indices * ((slot * CPS + cIndex) + 1) - len_indices * (slot * CPS + cIndex) >=  (CPS * SLOTS_PER_EPOCH as nat);

        assert  TWO_UP_5 as nat <= len_indices 
            ==> len_indices >= (CPS * SLOTS_PER_EPOCH as nat) 
            ==> len_indices * ((slot * CPS + cIndex) + 1) / (CPS * SLOTS_PER_EPOCH as nat) > len_indices * (slot * CPS + cIndex) / (CPS * SLOTS_PER_EPOCH as nat);
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

    lemma updateBalTotalBySingleDeposit(s: BeaconState, d: Deposit)
        requires s.eth1_deposit_index as int +  1 < 0x10000000000000000 
        requires |s.validators| == |s.balances|
        requires |s.validators| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
        requires total_balances(s.balances) + d.data.amount as int < 0x10000000000000000
        
        ensures total_balances(updateDeposit(s,d).balances) == total_balances(s.balances) + d.data.amount as int < 0x10000000000000000
        //ensures total_balances(updateDeposit(s,d).balances) == total_balances(s.balances) + total_deposits([d]) 
    {
        var pk := seqKeysInValidators(s.validators); 
        if |s.balances| == 0 {
            // Thanks Dafny
        }
        else {
            if d.data.pubkey in pk {
                var index := get_validator_index(pk, d.data.pubkey);
                individualBalanceBoundMaintained(s.balances,d);
                //assert updateDeposit(s,d).balances ==  increase_balance(s,index,d.data.amount).balances;
                //assert increase_balance(s,index,d.data.amount).balances[index] == s.balances[index] + d.data.amount;
                //assert forall i :: 0 <= i < |s.balances| && i != index as int ==> increase_balance(s,index,d.data.amount).balances[i] == s.balances[i];
                //assert total_balances(updateDeposit(s,d).balances) == total_balances(increase_balance(s,index,d.data.amount).balances) ;
                updateExistingBalance(s, index, d.data.amount);
                //assert total_balances(updateDeposit(s,d).balances) == total_balances(s.balances) + d.data.amount as int ;
            }
            else {
                //assert updateDeposit(s,d).balances == s.balances + [d.data.amount];
                distBalancesProp(s.balances,[d.data.amount]);
                //assert total_balances(s.balances + [d.data.amount]) == total_balances(s.balances) + total_balances([d.data.amount]);
            }
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