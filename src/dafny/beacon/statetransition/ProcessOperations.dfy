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

include "../../utils/NativeTypes.dfy"
include "../../utils/NonNativeTypes.dfy"
include "../../utils/Eth2Types.dfy"
include "../forkchoice/ForkChoiceTypes.dfy"
include "../../utils/Helpers.dfy"
include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../validators/Validators.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../Helpers.dfy"
include "StateTransition.s.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "ProcessOperations.s.dfy"

/**
 * State transition function for the Beacon Chain.
 */
module ProcessOperations {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NativeTypes
    import opened NonNativeTypes
    import opened Eth2Types
    import opened ForkChoiceTypes
    import opened Constants
    import opened BeaconChainTypes
    import opened Validators
    import opened AttestationsTypes
    import opened Helpers
    import opened BeaconHelpers
    import opened StateTransitionSpec
    import opened AttestationsHelpers
    import opened ProcessOperationsSpec
    

    /**
     *  Process the operations defined by a block body.
     *  
     *  @param  s   A state.
     *  @param  bb  A block body.
     *  @returns    The state obtained after applying the operations of `bb` to `s`.
     */
    method process_operations(s: BeaconState, bb: BeaconBlockBody)  returns (s' : BeaconState) 
        // proposer slashing preconditions
        requires forall i,j :: 0 <= i < j < |bb.proposer_slashings| && i != j ==> bb.proposer_slashings[i].header_1.proposer_index!= bb.proposer_slashings[j].header_1.proposer_index // ve indices are unique
        
        requires forall i :: 0 <= i < |bb.proposer_slashings| ==> bb.proposer_slashings[i].header_1.slot == bb.proposer_slashings[i].header_2.slot
        requires forall i :: 0 <= i < |bb.proposer_slashings| ==> bb.proposer_slashings[i].header_1.proposer_index == bb.proposer_slashings[i].header_2.proposer_index 
        requires forall i :: 0 <= i < |bb.proposer_slashings| ==> bb.proposer_slashings[i].header_1 == bb.proposer_slashings[i].header_2

        requires forall i :: 0 <= i < |bb.proposer_slashings| ==> bb.proposer_slashings[i].header_1.proposer_index as int < |s.validators|
        requires forall i :: 0 <= i < |bb.proposer_slashings| ==> !s.validators[bb.proposer_slashings[i].header_1.proposer_index].slashed 
        requires forall i :: 0 <= i < |bb.proposer_slashings| ==> s.validators[bb.proposer_slashings[i].header_1.proposer_index].activationEpoch <= get_current_epoch(s) < s.validators[bb.proposer_slashings[i].header_1.proposer_index].withdrawableEpoch

        
        //requires forall i :: i in get_PS_validator_indices(bb.proposer_slashings) ==> 0 <= i < |s.validators| 
        //requires forall i :: i in get_PS_validator_indices(bb.proposer_slashings) ==> !s.validators[i].slashed
        //requires forall i :: i in get_PS_validator_indices(bb.proposer_slashings) ==> s.validators[i].activationEpoch <= get_current_epoch(s) < s.validators[i].withdrawableEpoch

        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires |s.validators| == |s.balances|
        
        //ensures |s.validators| == |updateProposerSlashings(s, bb.proposer_slashings).validators|
        
        // attester slashing preconditions
        // note, with the current is_valid_indexed_attetsation predicate, the state isn't used to determine the result at this time
        // as such it doesn't matter whether the state is s or updateProposerSlashings(s, bb.proposer_slashings) is used in the following preconditions
        // since they are equivalent
        requires forall i :: 0 <= i < |bb.attester_slashings| ==> is_valid_indexed_attestation(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings[i].attestation_1)
        requires forall i :: 0 <= i < |bb.attester_slashings| ==> is_valid_indexed_attestation(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings[i].attestation_2)
        requires forall i :: 0 <= i < |bb.attester_slashings| ==> forall j :: 0 <= j < |bb.attester_slashings[i].attestation_1.attesting_indices| ==> bb.attester_slashings[i].attestation_1.attesting_indices[j] as int < |s.validators|
        requires forall i :: 0 <= i < |bb.attester_slashings| ==> forall j :: 0 <= j < |bb.attester_slashings[i].attestation_2.attesting_indices| ==> bb.attester_slashings[i].attestation_2.attesting_indices[j] as int < |s.validators|
        
        requires forall i :: 0 <= i < |bb.attester_slashings| ==> |sorted_intersection(bb.attester_slashings[i].attestation_1.attesting_indices, bb.attester_slashings[i].attestation_2.attesting_indices)| > 0
        //requires forall i :: 0 <= i < |bb.attester_slashings| ==> 
        //    exists j :: 0 <= j < |sorted_intersection(bb.attester_slashings[i].attestation_1.attesting_indices, bb.attester_slashings[i].attestation_2.attesting_indices)| &&
        //    is_slashable_validator(updateProposerSlashings(s, bb.proposer_slashings).validators[sorted_intersection(bb.attester_slashings[i].attestation_1.attesting_indices, bb.attester_slashings[i].attestation_2.attesting_indices)[j]], get_current_epoch(s))

        //requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        //requires |s.validators| == |s.balances|

        requires forall i :: 0 <= i < |bb.attester_slashings| ==> is_slashable_attestation_data(bb.attester_slashings[i].attestation_1.data, bb.attester_slashings[i].attestation_2.data)

        // process deposit preconditions
        requires s.eth1_deposit_index as int +  |bb.deposits| < 0x10000000000000000 
        requires |s.validators| + |bb.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        //requires |s.validators| == |s.balances|
        requires total_balances(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings).balances) + total_deposits(bb.deposits) < 0x10000000000000000 

        // voluntary exit preconditions
        requires forall i,j :: 0 <= i < j < |bb.voluntary_exits| && i != j ==> bb.voluntary_exits[i].validator_index != bb.voluntary_exits[j].validator_index // ve indices are unique
        requires forall i :: 0 <= i < |bb.voluntary_exits| ==> bb.voluntary_exits[i].validator_index as int < |s.validators| 
        requires forall i :: 0 <= i < |bb.voluntary_exits| ==> get_current_epoch(s) >= bb.voluntary_exits[i].epoch

        //requires forall i :: 0 <= i < |bb.voluntary_exits| ==> is_active_validator(s.validators[bb.voluntary_exits[i].validator_index], get_current_epoch(s))
        requires forall i :: 0 <= i < |bb.voluntary_exits| ==> !updateDeposits(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.deposits).validators[bb.voluntary_exits[i].validator_index].slashed
        requires forall i :: 0 <= i < |bb.voluntary_exits| ==> updateDeposits(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.deposits).validators[bb.voluntary_exits[i].validator_index].activationEpoch <= get_current_epoch(s) < updateDeposits(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.deposits).validators[bb.voluntary_exits[i].validator_index].withdrawableEpoch

        requires forall i :: 0 <= i < |bb.voluntary_exits| ==> updateDeposits(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.deposits).validators[bb.voluntary_exits[i].validator_index].exitEpoch == FAR_FUTURE_EPOCH
        requires forall i :: 0 <= i < |bb.voluntary_exits| ==> get_current_epoch(s) >= updateDeposits(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.deposits).validators[bb.voluntary_exits[i].validator_index].activationEpoch + SHARD_COMMITTEE_PERIOD 

        //requires forall i :: i in get_VolExit_validator_indices(bb.voluntary_exits) ==> 0 <= i < |s.validators| 
        //requires forall i :: i in get_VolExit_validator_indices(bb.voluntary_exits) ==> !s.validators[i].slashed
        //requires forall i :: i in get_VolExit_validator_indices(bb.voluntary_exits) ==> s.validators[i].activationEpoch <= get_current_epoch(s) < s.validators[i].withdrawableEpoch
        //requires forall i :: i in get_VolExit_validator_indices(bb.voluntary_exits) ==> s.validators[i].exitEpoch == FAR_FUTURE_EPOCH
        //requires forall i :: i in get_VolExit_validator_indices(bb.voluntary_exits) ==> get_current_epoch(s) >= s.validators[i].activationEpoch + SHARD_COMMITTEE_PERIOD 
    
        
        
        // post conditions
        ensures |s'.validators| == |s'.balances|
        //ensures s' == updateDeposits(s, bb.deposits)
        //ensures s' == updateDeposits(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.deposits)
        //ensures s' == updateVoluntaryExits(updateDeposits(updateProposerSlashings(s, bb.proposer_slashings), bb.deposits), bb.voluntary_exits)
        ensures s'.slot == s.slot
        ensures s'.latest_block_header == s.latest_block_header
        //ensures s'.validators == s.validators + get_new_validators(s, [], bb.deposits)
        //ensures false
    {
        s':= s;
        var slashed_any := false;

        // process the proposer slashings
        var i := 0;
        assert s' == updateProposerSlashings(s, bb.proposer_slashings[..i]);
        assert s'.slot == s.slot;
        assert s'.latest_block_header == s.latest_block_header;

        assert |s'.validators| == |s'.balances|;
        
        

        while i < |bb.proposer_slashings| 
            decreases |bb.proposer_slashings| - i

            invariant 0 <= i <= |bb.proposer_slashings|
            
            invariant |s'.validators| ==  |s.validators| 
            invariant s' == updateProposerSlashings(s, bb.proposer_slashings[..i])
            
            invariant s'.slot == s.slot
            invariant s'.latest_block_header == s.latest_block_header
            
        {
            assert bb.proposer_slashings[..i+1] == bb.proposer_slashings[..i] + [bb.proposer_slashings[i]];

            //assert forall j :: i <= j < |bb.proposer_slashings| ==> s'.validators[bb.proposer_slashings[j].header_1.proposer_index] == s.validators[bb.proposer_slashings[j].header_1.proposer_index];
            
            //assert bb.proposer_slashings[i].header_1.proposer_index as int < |s'.validators|;
            //assert !s.validators[bb.proposer_slashings[i].header_1.proposer_index].slashed;
            //assert s' == updateProposerSlashings(s, bb.proposer_slashings[..i]); 
            //assert forall j :: 0 <= j < |s.validators| && j !in get_PS_validator_indices(bb.proposer_slashings[..i]) ==> updateProposerSlashings(s, bb.proposer_slashings[..i]).validators[j] == s.validators[j];
            //assert forall j :: 0 <= j < |s.validators| && j !in get_PS_validator_indices(bb.proposer_slashings[..i]) ==> s'.validators[j] == s.validators[j];
            
            helperPSLemma4(bb.proposer_slashings[..i+1]);
            //assert bb.proposer_slashings[i].header_1.proposer_index as int !in get_PS_validator_indices(bb.proposer_slashings[..i]);
            //assert !s'.validators[bb.proposer_slashings[i].header_1.proposer_index].slashed;
            //assert s'.validators[bb.proposer_slashings[i].header_1.proposer_index].activationEpoch <= get_current_epoch(s') < s'.validators[bb.proposer_slashings[i].header_1.proposer_index].withdrawableEpoch;
            
            s' := process_proposer_slashing(s', bb.proposer_slashings[i]);

            i := i + 1;

            
        }
        assert bb.proposer_slashings[..i] == bb.proposer_slashings;
        assert s' == updateProposerSlashings(s, bb.proposer_slashings);

        // process attester slashings
        i := 0;
        assert s' == updateProposerSlashings(s, bb.proposer_slashings);
        assert s'.slot == s.slot;
        assert s'.latest_block_header == s.latest_block_header;

        assert |s'.validators| == |s'.balances|;
        

        while i < |bb.attester_slashings| 
            decreases |bb.attester_slashings| - i

            invariant 0 <= i <= |bb.attester_slashings|

            invariant |s'.validators| ==  |s.validators| 

            //invariant forall j :: 0 <= j < |bb.attester_slashings[..i]| ==> is_valid_indexed_attestation(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings[j].attestation_1)
            //invariant forall j :: 0 <= j < |bb.attester_slashings[..i]| ==> is_valid_indexed_attestation(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings[j].attestation_2)
            invariant s' == updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings[..i])

            invariant s'.slot == s.slot
            invariant s'.latest_block_header == s.latest_block_header //updateProposerSlashings(s, bb.proposer_slashings).latest_block_header == 
        {
            assert bb.attester_slashings[..i+1] == bb.attester_slashings[..i] + [bb.attester_slashings[i]];
            
            valid_indexed_attestation_lemma(updateProposerSlashings(s, bb.proposer_slashings), s', bb.attester_slashings[i].attestation_1);
            assert is_valid_indexed_attestation(s', bb.attester_slashings[i].attestation_1);
            valid_indexed_attestation_lemma(updateProposerSlashings(s, bb.proposer_slashings), s', bb.attester_slashings[i].attestation_2);
            assert is_valid_indexed_attestation(s', bb.attester_slashings[i].attestation_2);
            
            assert |sorted_intersection(bb.attester_slashings[i].attestation_1.attesting_indices, bb.attester_slashings[i].attestation_2.attesting_indices)| > 0;
            //assume exists j :: 0 <= j < |sorted_intersection(bb.attester_slashings[i].attestation_1.attesting_indices, bb.attester_slashings[i].attestation_2.attesting_indices)| &&
            //    is_slashable_validator(s'.validators[sorted_intersection(bb.attester_slashings[i].attestation_1.attesting_indices, bb.attester_slashings[i].attestation_2.attesting_indices)[j]], get_current_epoch(s));
            // TODO: need to prove at least as many unique slashable validators as there are attester_slashings
            //      i.e. change the precondition and maybe use a lemma 

            s', slashed_any := process_attester_slashing(s', bb.attester_slashings[i]);
            i := i + 1;

        }
        assert bb.attester_slashings[..i] == bb.attester_slashings;
        assert s' == updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings);

        
        // check process deposit preconditions
        assert s'.eth1_deposit_index == s.eth1_deposit_index;
        assert s'.eth1_deposit_index as int +  |bb.deposits| < 0x10000000000000000;
        assert total_balances(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings).balances) + total_deposits(bb.deposits) < 0x10000000000000000; 

        //  process deposits in the beacon block body.
        
        i := 0;
        assert s' == updateDeposits(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.deposits[..i]);
        assert total_balances(s'.balances) + total_deposits(bb.deposits[..i]) < 0x10000000000000000 ;
        
        while i < |bb.deposits| 
            decreases |bb.deposits| - i

            invariant 0 <= i <= |bb.deposits|
            invariant s'.eth1_deposit_index == s.eth1_deposit_index + i as uint64
            
            invariant total_balances(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings).balances) + total_deposits(bb.deposits[..i]) < 0x10000000000000000 
            //invariant s'.validators == updateDeposits(s, bb.deposits[..i]).validators
            //invariant s'.balances == updateDeposits(s, bb.deposits[..i]).balances
            
            //invariant total_balances(updateDeposits(s,bb.deposits[..i]).balances) == total_balances(s.balances) + total_deposits(bb.deposits[..i]) < 0x10000000000000000
            
            //invariant s'.slot == s.slot 
            //invariant s'.latest_block_header == s.latest_block_header
            //invariant s'.block_roots == s.block_roots
            //invariant s'.state_roots == s.state_roots

            //invariant |s'.validators| == |s'.balances| 
            //invariant |s'.validators| <= |s.validators| + i
            //invariant |s.validators| + i <= VALIDATOR_REGISTRY_LIMIT as int
            invariant s' == updateDeposits(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.deposits[..i])
            invariant s'.slot == s.slot
            invariant s'.latest_block_header == s.latest_block_header
            //invariant |bb.deposits[..i]| == i

            //invariant |s'.validators| <= |updateDeposits(s,bb.deposits[..i]).validators| <= |s'.validators| + i 
        {
            assert bb.deposits[..i+1] == bb.deposits[..i] + [bb.deposits[i]];
            //assert total_balances(updateDeposits(s, bb.deposits[..i]).balances) + bb.deposits[i].data.amount as int == total_balances(s.balances) + total_deposits(bb.deposits[..i]) + bb.deposits[i].data.amount as int;
            //assert total_deposits(bb.deposits[..i]) + bb.deposits[i].data.amount as int == total_deposits(bb.deposits[..i+1]);
            //assert total_balances(updateDeposits(s, bb.deposits[..i]).balances) + bb.deposits[i].data.amount as int == total_balances(s.balances) + total_deposits(bb.deposits[..i+1]);
            //assert i + 1  <= |bb.deposits|;
            subsetDepositSumProp(bb.deposits, i+1);
            //assert total_deposits(bb.deposits[..i+1]) <= total_deposits(bb.deposits);
            //assert total_balances(updateDeposits(s, bb.deposits[..i]).balances) + bb.deposits[i].data.amount as int < 0x10000000000000000;

            //assert updateDeposit(updateDeposits(s, bb.deposits[..i]),bb.deposits[i]) == updateDeposits(s, bb.deposits[..i+1]);
            
            s':= process_deposit(s', bb.deposits[i]); 
            i := i+1;

        }
        assert bb.deposits[..i] == bb.deposits;
        assert s' == updateDeposits(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.deposits);

        // process voluntary exits
        i := 0;
        assert s' == updateVoluntaryExits(updateDeposits(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.deposits), bb.voluntary_exits[..i]);
        assert s'.slot == s.slot;
        assert s'.latest_block_header == s.latest_block_header;

        assert |s'.validators| == |s'.balances|;
        

        while i < |bb.voluntary_exits| 
            decreases |bb.voluntary_exits| - i

            invariant 0 <= i <= |bb.voluntary_exits|
            invariant s' == updateVoluntaryExits(updateDeposits(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.deposits), bb.voluntary_exits[..i])
            invariant s'.slot == s.slot
            invariant s'.latest_block_header == s.latest_block_header
        {
            helperVolExitLemma4(bb.voluntary_exits[..i+1]);
            assert bb.voluntary_exits[..i+1] == bb.voluntary_exits[..i] + [bb.voluntary_exits[i]];
            //assert bb.voluntary_exits[i].validator_index as int < |s.validators| <= |s'.validators|;
            //assert !s'.validators[bb.voluntary_exits[i].validator_index].slashed;

            //assume s'.validators[bb.voluntary_exits[i].validator_index].activationEpoch <= get_current_epoch(s) < s'.validators[bb.voluntary_exits[i].validator_index].withdrawableEpoch;
            //assume s'.validators[bb.voluntary_exits[i].validator_index].exitEpoch == FAR_FUTURE_EPOCH;
            //assume get_current_epoch(s) >= bb.voluntary_exits[i].epoch;
            //assume get_current_epoch(s) >= s'.validators[bb.voluntary_exits[i].validator_index].activationEpoch + SHARD_COMMITTEE_PERIOD ;

            s' := process_voluntary_exit(s', bb.voluntary_exits[i]);
            i := i + 1;

        }
        assert bb.voluntary_exits[..i] == bb.voluntary_exits;
        assert s' == updateVoluntaryExits(updateDeposits(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.deposits), bb.voluntary_exits);
        

    }

    /**
     *  Process a deposit operation.
     *
     *  @param  s   A state.
     *  @param  d   A deposit.  
     *  @returns    The state obtained depositing of `d` to `s`.
     *  @todo       Finish implementation of this function.
     */
    method process_deposit(s: BeaconState, d : Deposit)  returns (s' : BeaconState)  
        requires |s.validators| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
        requires s.eth1_deposit_index as int + 1 < 0x10000000000000000 
        requires |s.validators| == |s.balances|
        requires total_balances(s.balances) + d.data.amount as int < 0x10000000000000000

        ensures s'.eth1_deposit_index == s.eth1_deposit_index + 1
        //ensures d.data.pubkey !in seqKeysInValidators(s.validators) ==> s'.validators == s.validators + [get_validator_from_deposit(d)]
        //ensures d.data.pubkey in seqKeysInValidators(s.validators) ==> s'.validators == s.validators 
        ensures s' == updateDeposit(s,d)

        //ensures |s'.validators| == |s'.balances|        // maybe include in property lemmas
        //ensures |s.validators| <= |s'.validators| <= |s.validators| + 1 // maybe include in property lemmas
        //ensures |s.balances| <= |s'.balances| <= |s.balances| + 1 // maybe include in property lemmas
        //ensures |s'.validators| <= VALIDATOR_REGISTRY_LIMIT
        
    {
        // note that it is assumed that all new validator deposits are verified
        // ie the step # Verify the deposit signature (proof of possession) which is not checked by the deposit contract
        // is not performed
        var pk := seqKeysInValidators(s.validators);
        s' := s.(
                eth1_deposit_index := (s.eth1_deposit_index as int + 1) as uint64,
                validators := if d.data.pubkey in pk then 
                                    s.validators // unchanged validator members
                                else 
                                    (s.validators + [get_validator_from_deposit(d)]),
                balances := if d.data.pubkey in pk then 
                                    individualBalanceBoundMaintained(s.balances,d);
                                    increase_balance(s,get_validator_index(pk, d.data.pubkey),d.data.amount).balances
                                else 
                                    s.balances + [d.data.amount]
        );
    }


    /**
     *  Process a proposer slashing.
     *
     *  @param  s   A state.
     *  @param  ps  A proposer slashing.  
     *  @returns    The state obtained applying `ps` to `s`.
     *  @todo       Finish implementation of this function.
     */
    method process_proposer_slashing(s: BeaconState, ps : ProposerSlashing)  returns (s' : BeaconState)  
        requires ps.header_1.slot == ps.header_2.slot
        requires ps.header_1.proposer_index == ps.header_2.proposer_index 
        requires ps.header_1 == ps.header_2
        
        requires ps.header_1.proposer_index as int < |s.validators| 
        //requires is_slashable_validator(s.validators[ps.header_1.proposer_index], get_current_epoch(s));
        requires !s.validators[ps.header_1.proposer_index].slashed
        requires s.validators[ps.header_1.proposer_index].activationEpoch <= get_current_epoch(s) < s.validators[ps.header_1.proposer_index].withdrawableEpoch

        
        //requires s.validators[ps.header_1.proposer_index].exitEpoch == FAR_FUTURE_EPOCH
        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires |s.validators| == |s.balances|
        
        ensures s' == updateProposerSlashing(s,ps)
        //ensures forall i :: 0 <= i < |s.validators|  && i != ps.header_1.proposer_index as int ==> s'.validators[i] == s.validators[i]
    {
        // header_1 = proposer_slashing.signed_header_1.message
        // header_2 = proposer_slashing.signed_header_2.message

        // # Verify header slots match
        // assert header_1.slot == header_2.slot
        assert ps.header_1.slot == ps.header_2.slot;


        // # Verify header proposer indices match
        // assert header_1.proposer_index == header_2.proposer_index
        assert ps.header_1.proposer_index == ps.header_2.proposer_index;

        // # Verify the headers are different
        // assert header_1 != header_2
        assert ps.header_1 == ps.header_2;


        // # Verify the proposer is slashable
        var proposer := s.validators[ps.header_1.proposer_index];
        
        //assert is_slashable_validator(proposer, get_current_epoch(s));
        assert is_slashable_validator(proposer, get_current_epoch(s));


        // # Verify signatures
        // for signed_header in (proposer_slashing.signed_header_1, proposer_slashing.signed_header_2):
        //     domain = get_domain(state, DOMAIN_BEACON_PROPOSER, compute_epoch_at_slot(signed_header.message.slot))
        //     signing_root = compute_signing_root(signed_header.message, domain)
        //     assert bls.Verify(proposer.pubkey, signing_root, signed_header.signature)


        assert ps.header_1.proposer_index as int < |s.validators| ;
        assert get_beacon_proposer_index(s) as int < |s.validators|;
        assert |s.validators| == |s.balances|;

        //assert s.validators[ps.header_1.proposer_index].exitEpoch == FAR_FUTURE_EPOCH;
        assert |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0;

        // the whistleblower_index parameter of slash_validator is None in the spec
        // as 'None' isn't possible in Dafny, set the parameter to get_beacon_proposer_index(s)
        // as it would be set to that for 'None' within slash_validator

        s' := slash_validator(s, ps.header_1.proposer_index, get_beacon_proposer_index(s));
    }

    // lemma helper_proposer_lemma(s: BeaconState, ps : ProposerSlashing)
    //     requires ps.header_1.proposer_index as int < |s.validators| 
    //     //requires s.validators[ps.header_1.proposer_index].exitEpoch == FAR_FUTURE_EPOCH
    //     requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
    //     requires |s.validators| == |s.balances|
    //     ensures updateProposerSlashing(s,ps) == slash_validator(s, ps.header_1.proposer_index, get_beacon_proposer_index(s))
    // {

    // }

    method test_assert_seq(n: int) returns (se: seq<int>)
    {
        se := [];

        var i :=0;

        while i < n
        {
            se := se + [i];
            i := i + 1;
        } 
    }

    method test_assert_method(ts: seq<int>) returns (s': seq<int>)
        //requires |ts| > 0
    {
        var se := test_assert_seq(|ts|);
        //var length := |se|-1;
        var i :=0;
        //assert ts[..length] == ts;
        while i < |se|  {
            assert se[..i+1] == se[..i] + [se[i]];
            i := i + 1;
        }
        s' := ts;
    }
    

    // //Attester slashings
    // method process_attester_slashing(s: BeaconState, a: AttesterSlashing) returns (s' : BeaconState) 
    //     requires forall i :: 0 <= i < |a.attestation_1.attesting_indices| ==> a.attestation_1.attesting_indices[i] as int < |s.validators|
    //     requires forall i :: 0 <= i < |a.attestation_2.attesting_indices| ==> a.attestation_2.attesting_indices[i] as int < |s.validators|
    //     requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
    //     requires |s.validators| == |s.balances|
        
    //     ensures if !is_slashable_attestation_data(a.attestation_1.data, a.attestation_2.data) 
    //                 || !is_valid_indexed_attestation(s, a.attestation_1)
    //                 || !is_valid_indexed_attestation(s, a.attestation_2)
    //                 || |sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices)| == 0 then s' == s
    //             else s' == updateAttesterSlashing(s,sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices))
        
    // {
    //     // attestation_1 = attester_slashing.attestation_1
    //     // attestation_2 = attester_slashing.attestation_2

    //     // assert is_slashable_attestation_data(attestation_1.data, attestation_2.data)
    //     // Double vote
    //     //(data_1 != data_2 && data_1.target.epoch == data_2.target.epoch) ||
    //     // Surround vote
    //     //(data_1.source.epoch < data_2.source.epoch && data_2.target.epoch < data_1.target.epoch)

    //     if !is_slashable_attestation_data(a.attestation_1.data, a.attestation_2.data) {
    //         return s;
    //     }
    //     // assert is_valid_indexed_attestation(state, attestation_1)
    //     // Verify indices are sorted and unique, and at least 1
    //     if !is_valid_indexed_attestation(s, a.attestation_1){
    //         return s;
    //     }

    //     // assert is_valid_indexed_attestation(state, attestation_2)
    //     if !is_valid_indexed_attestation(s, a.attestation_2){
    //         return s;
    //     }
        
    //     // Note: attestation_1.attesting_indices should already be a set, 
    //     //      i.e. given is_valid_indexed_attestation(s, a.attestation_1)
    //     if |sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices)| > 0 {
    //         // assert slashed_any
    //         var slashed_any : bool;
    //         var indices := sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices);
    //         s', slashed_any := attester_slashing_helper(s, indices);
    //         //assert slashed_any ==> exists j :: 0 <= j < |indices| && is_slashable_validator(s.validators[indices[j]], get_current_epoch(s)) ;
    //     }
    //     else {
    //         return s;
    //     }
        
    // }

    // method attester_slashing_helper(s: BeaconState, ts: seq<ValidatorIndex>) returns (s' : BeaconState, slashed_any: bool)
    //     //requires |ts| > 0
    //     requires forall i :: 0 <= i < |ts| ==> ts[i] as int < |s.validators|
    //     requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
    //     requires forall i,j :: 0 <= i < j < |ts| ==>  ts[i] < ts[j]
    //     requires |s.validators| == |s.balances|

    //     ensures s' == updateAttesterSlashing(s, ts)
    //     //ensures slashed_any ==> exists j :: 0 <= j < |ts| && is_slashable_validator(s.validators[ts[j]], get_current_epoch(s)) 
    // {
    //     s' := s;
    //     slashed_any := false;
        
    //     var i := 0;
    //     var flag := false;

    //     assert forall j :: 0 <= j < i ==> ts[j] as int < |s.validators|;
    //     assert s' == updateAttesterSlashing(s, ts[..i]);
        
    //     while i < |ts| 
    //         decreases |ts| - i
    //         //invariant |ts| > 0
    //         invariant 0 <= i <= |ts|
    //         invariant |s'.validators| == |s.validators|
    //         invariant |s'.validators| == |s'.balances|
    //         invariant get_current_epoch(s) == get_current_epoch(s')
    //         //invariant a == old(a)
    //         //invariant ts == old(sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices))
    //         //invariant |ts| > 0
            
    //         invariant get_active_validator_indices(s.validators, get_current_epoch(s)) == get_active_validator_indices(s'.validators, get_current_epoch(s));
    //         invariant |get_active_validator_indices(s'.validators, get_current_epoch(s'))| > 0
    //         invariant get_beacon_proposer_index(s) == get_beacon_proposer_index(s')
    //         invariant get_beacon_proposer_index(s') as int < |s'.validators|
    //         invariant i == |ts[..i]|
    //         invariant forall j :: 0 <= j < |ts[..i]| ==> ts[j] as int < |s.validators|
    //         invariant s' == updateAttesterSlashing(s, ts[..i])
    //         invariant s'.slot == s.slot
    //         //invariant s'.latest_block_header == s.latest_block_header
    //     {

    //         //assert ts[i] as int < |s'.validators|;
    //         //assert ts == sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices);
    //         //assert |ts|> 0;
    //         assert ts[..i+1] == ts[..i] + [ts[i]];
    //         //assert s' == updateAttesterSlashing(s, ts[..i]);
            
    //         if (is_slashable_validator(s'.validators[ts[i]], get_current_epoch(s'))) {
    //             //assert s'.validators[ts[i]] == s.validators[ts[i]];
    //             //assert get_current_epoch(s) == get_current_epoch(s');
    //             //assert is_slashable_validator(s'.validators[ts[i]], get_current_epoch(s')) == is_slashable_validator(s.validators[ts[i]], get_current_epoch(s));
    //             //assert ts[i] as int < |s'.validators|; 
    //             slashValidatorPreservesActivateValidators(s', ts[i], get_beacon_proposer_index(s'));
    //             //assert get_active_validator_indices(s'.validators, get_current_epoch(s')) 
    //             //    == get_active_validator_indices(slash_validator(s',indices[i],get_beacon_proposer_index(s')).validators, get_current_epoch(s'));
                
    //             s' := slash_validator(s', ts[i], get_beacon_proposer_index(s'));

    //             slashed_any := true;
    //         }
    //         else {
    //             s' := s';
    //         }
    //         //assert s' == updateAttesterSlashing(s, ts[..i+1]);
    //         i := i+1;
            

    //     }
    //     assert i == |ts|;
    //     assert ts[..i] == ts;
    //     assert s' == updateAttesterSlashing(s, ts);


    //     // for index in sorted(indices):
    //     //     if is_slashable_validator(state.validators[index], get_current_epoch(state)):
    //     //         slash_validator(state, index)
    //     //         slashed_any = True
        
    //     return s', slashed_any;

    // }

    

    method process_attester_slashing(s: BeaconState, a: AttesterSlashing) returns (s' : BeaconState, flag: bool) 
        requires forall i :: 0 <= i < |a.attestation_1.attesting_indices| ==> a.attestation_1.attesting_indices[i] as int < |s.validators|
        requires forall i :: 0 <= i < |a.attestation_2.attesting_indices| ==> a.attestation_2.attesting_indices[i] as int < |s.validators|
        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires |s.validators| == |s.balances|

        requires is_slashable_attestation_data(a.attestation_1.data, a.attestation_2.data)

        requires is_valid_indexed_attestation(s, a.attestation_1)
        requires is_valid_indexed_attestation(s, a.attestation_2)

        // not sure whether there should be at least one in the intersection???
        requires |sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices)| > 0

        // the following should be used when adding a check that slashed_any == true at the end of the method
        //requires exists i :: 0 <= i < |sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices)| &&
        //    is_slashable_validator(s.validators[sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices)[i]], get_current_epoch(s))

        ensures s' == updateAttesterSlashing(s, sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices))
        //ensures flag
    {
        //Double vote
        //(data_1 != data_2 && data_1.target.epoch == data_2.target.epoch) ||
        // Surround vote
        //(data_1.source.epoch < data_2.source.epoch && data_2.target.epoch < data_1.target.epoch)
        assert is_slashable_attestation_data(a.attestation_1.data, a.attestation_2.data);
        
        // assert is_valid_indexed_attestation(state, attestation_1)
        // Verify indices are sorted and unique, and at least 1
        assert is_valid_indexed_attestation(s, a.attestation_1);

        // assert is_valid_indexed_attestation(state, attestation_2)
        assert is_valid_indexed_attestation(s, a.attestation_2);

        s' := s;
        flag := false;
        
        var i := 0;
        
        var origState := s;
        
        var ts := sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices);

        assert forall i :: 0 <= i < |ts| ==> ts[i] as int < |s'.validators|;

        assert s' == updateAttesterSlashing(s, ts[..i]);
        
        while i < |ts| 
            decreases |ts| - i
            invariant 0 <= i <= |ts|
            invariant |s'.validators| == |s.validators|
            invariant |s'.validators| == |s'.balances|
            invariant get_current_epoch(s) == get_current_epoch(s')
            invariant |ts| > 0
            
            invariant get_active_validator_indices(s.validators, get_current_epoch(s)) == get_active_validator_indices(s'.validators, get_current_epoch(s));
            invariant |get_active_validator_indices(s'.validators, get_current_epoch(s'))| > 0
            invariant get_beacon_proposer_index(s) == get_beacon_proposer_index(s')
            invariant get_beacon_proposer_index(s') as int < |s'.validators|
            invariant i == |ts[..i]|
            
            invariant forall j :: 0 <= j < |ts| ==> ts[j] as int < |s'.validators|
            invariant valid_state_indices(s, ts[..i]);
            invariant s' == updateAttesterSlashing(s, ts[..i])
            invariant s'.slot == s.slot
        {
            origState := s';
            
            // if (is_slashable_validator(s'.validators[ts[i]], get_current_epoch(s'))) {
            //     assert (!s'.validators[ts[i]].slashed) && (s'.validators[ts[i]].activationEpoch <= get_current_epoch(s') < s'.validators[ts[i]].withdrawableEpoch);
            //     slashValidatorPreservesActivateValidators(s', ts[i], get_beacon_proposer_index(s'));
            //     s' := slash_validator(s', ts[i], get_beacon_proposer_index(s'));
            //     flag := true;
            // }
            if (is_slashable_validator(origState.validators[ts[i]], get_current_epoch(origState))) {
                assert (!origState.validators[ts[i]].slashed) && (origState.validators[ts[i]].activationEpoch <= get_current_epoch(origState) < origState.validators[ts[i]].withdrawableEpoch);
                slashValidatorPreservesActivateValidators(origState, ts[i], get_beacon_proposer_index(origState));
                s' := slash_validator(origState, ts[i], get_beacon_proposer_index(origState));
                flag := true;
                //slash_validator_lemma(origState, ts[i], get_beacon_proposer_index(origState));

                //assert slash_validator(origState, ts[i], get_beacon_proposer_index(origState)).validators[ts[i]].slashed;
            }
            else {
                  s' := s';
            }
            //assert is_slashable_validator(origState.validators[ts[i]], get_current_epoch(origState)) ==> flag;
            //slash_validator_lemma(origState, ts[i], get_beacon_proposer_index(origState));
            helperIndicesLemma5(ts,i+1);
            helperIndicesLemma7(ts,i);
            assert ts[..i+1] == ts[..i] + [ts[i]];
            helperIndicesLemma4(s,ts, i);
            assert origState == updateAttesterSlashing(s, ts[..i]);
            assert s' == updateAttesterSlashingComp(origState, ts[i]);
            assert s' == updateAttesterSlashingComp(updateAttesterSlashing(s, ts[..i]), ts[i]);
            assert valid_state_indices(s, ts);
            assert 0 < i+1 <= |ts|;
            helperIndicesLemma4(s,ts, i+1);
            assert valid_state_indices(s, ts[..(i+1)]);
            assert |ts[..(i+1)]| != 0;
            assert updateAttesterSlashing(s, ts[..(i+1)]) == updateAttesterSlashingComp(updateAttesterSlashing(s, ts[..i]), ts[i]);
            assert s' == updateAttesterSlashing(s, ts[..(i+1)]);
            i := i+1;
            helperIndicesLemma4(s,ts, i);
            assert valid_state_indices(s, ts[..i]);
            assert s' == updateAttesterSlashing(s, ts[..i]);
            
        }
        // calc ==> {
        //     exists j :: 0 <= j < |sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices)| &&
        //     is_slashable_validator(s.validators[sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices)[j]], get_current_epoch(s));
            
        //     exists j :: 0 <= j < |ts| && is_slashable_validator(s.validators[ts[j]], get_current_epoch(s'));

        //     slashed_any;

        // }
        assert i == |ts|;
        helperIndicesLemma6(ts, i);
        assert ts[..i] == ts;
        assert s' == updateAttesterSlashing(s, ts[..i]);
        assert s' == updateAttesterSlashing(s, ts);
        assert ts == sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices);
        //assert s' == updateAttesterSlashing(s, sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices));

        //assert slashed_any;
        
    }

    //method process_attester_slashing(s: BeaconState, a: AttesterSlashing) returns (s' : BeaconState) 
    // //method process_attester_slashing(s: BeaconState, a: AttesterSlashing, ts: seq<ValidatorIndex>) returns (s' : BeaconState) 
    //     //requires forall i :: 0 <= i < |ts| ==> ts[i] in a.attestation_1.attesting_indices && ts[i] in a.attestation_2.attesting_indices
    //     //requires forall i :: 0 <= i < |ts| ==> ts[i] as int < |s.validators|
    //     //requires |ts| > 0
        
    //     //requires is_slashable_attestation_data(a.attestation_1.data, a.attestation_2.data)
    //     //requires is_valid_indexed_attestation(s, a.attestation_1)
    //     //requires is_valid_indexed_attestation(s, a.attestation_2)

    //     //requires |sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices) | > 0

    //     requires forall i :: 0 <= i < |a.attestation_1.attesting_indices| ==> a.attestation_1.attesting_indices[i] as int < |s.validators|
    //     requires forall i :: 0 <= i < |a.attestation_2.attesting_indices| ==> a.attestation_2.attesting_indices[i] as int < |s.validators|
    //     requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
    //     requires |s.validators| == |s.balances|
    //     //requires forall i :: 0 <= i < |sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices)| ==>
    //     //                                    s.validators[sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices)[i]].exitEpoch == FAR_FUTURE_EPOCH
    //     //ensures s' == s || s' == updateAttesterSlashing(s, sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices))
    // //             (is_valid_indexed_attestation(s, a.attestation_1)
    // //             && is_valid_indexed_attestation(s, a.attestation_2)
    // //             s' == updateAttesterSlashing(s,sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices)))
    // {
    //     // attestation_1 = attester_slashing.attestation_1
    //     // attestation_2 = attester_slashing.attestation_2

    //     // assert is_slashable_attestation_data(attestation_1.data, attestation_2.data)
    //     // Double vote
    //     //(data_1 != data_2 && data_1.target.epoch == data_2.target.epoch) ||
    //     // Surround vote
    //     //(data_1.source.epoch < data_2.source.epoch && data_2.target.epoch < data_1.target.epoch)

    //     if !is_slashable_attestation_data(a.attestation_1.data, a.attestation_2.data) {
    //         return s;
    //     }
    //     // assert is_valid_indexed_attestation(state, attestation_1)
    //     // Verify indices are sorted and unique, and at least 1
    //     if !is_valid_indexed_attestation(s, a.attestation_1){
    //         return s;
    //     }

    //     // assert is_valid_indexed_attestation(state, attestation_2)
    //     if !is_valid_indexed_attestation(s, a.attestation_2){
    //         return s;
    //     }
        
    //     // Note: attestation_1.attesting_indices should already be a set, 
    //     //      i.e. given is_valid_indexed_attestation(s, a.attestation_1)
    //     assert |a.attestation_1.attesting_indices| > 0;
    //     assert |a.attestation_2.attesting_indices| > 0;
    //     assert forall i,j :: 0 <= i < j < |a.attestation_1.attesting_indices| 
    //             ==> a.attestation_1.attesting_indices[i] < a.attestation_1.attesting_indices[j];
    //     assert forall i,j :: 0 <= i < j < |a.attestation_2.attesting_indices| 
    //             ==> a.attestation_2.attesting_indices[i] < a.attestation_2.attesting_indices[j];

    //     // indices = set(attestation_1.attesting_indices).intersection(attestation_2.attesting_indices)
    //     var ts := sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices);
    //     assert ts == sorted_intersection_fn(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices);

    //     //ghost var ts' := ts;
    //     //assume |ts| > 0;

    //     //assert forall i :: 0 <= i < |ts| ==> ts[i] in a.attestation_1.attesting_indices && ts[i] in a.attestation_2.attesting_indices;
    //     //assert forall i :: 0 <= i < |ts| ==> ts[i] as int < |s.validators|;
    //     assume |ts| > 0;

    //     s' := s;
    //     assert forall i :: 0 <= i < |ts| ==> ts[i] as int < |s.validators|;
    //     assert forall i :: 0 <= i < |ts| ==> ts[i] as int < |s'.validators|;
    //     assert |get_active_validator_indices(s'.validators, get_current_epoch(s'))| > 0;

    //     //assert forall i :: 0 <= i < |sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices)| ==>
    //     //                                    s'.validators[sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices)[i]].exitEpoch == FAR_FUTURE_EPOCH;
  
    //     //assert forall i :: 0 <= i < |indices| ==> s'.validators[indices[i]].exitEpoch == FAR_FUTURE_EPOCH;
        
    //     var i := 0;
    //     var slashed_any := false;
    //     var flag := false;

    //     assert s' == updateAttesterSlashing(s, ts[..i]);
    //     assert is_valid_indexed_attestation(s, a.attestation_1);
    //     assert is_valid_indexed_attestation(s, a.attestation_2);
    //     assert ts == sorted_intersection_fn(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices);
    //     assert |ts| > 0;
    //     assert ts[..i+1] == ts[..i] + [ts[i]];
        
    //     while i < |ts| 
    //         decreases |ts| - i
    //         //invariant |ts| > 0
    //         invariant 0 <= i <= |ts|
    //         invariant |s'.validators| == |s.validators|
    //         invariant |s'.validators| == |s'.balances|
    //         invariant get_current_epoch(s) == get_current_epoch(s')
    //         //invariant a == old(a)
    //         //invariant ts == old(sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices))
    //         invariant |ts| > 0
            
    //         invariant get_active_validator_indices(s.validators, get_current_epoch(s)) == get_active_validator_indices(s'.validators, get_current_epoch(s));
    //         invariant |get_active_validator_indices(s'.validators, get_current_epoch(s'))| > 0
    //         invariant get_beacon_proposer_index(s) == get_beacon_proposer_index(s')
    //         invariant get_beacon_proposer_index(s') as int < |s'.validators|
    //         //invariant i == |ts[..i]|
    //         //invariant forall j :: 0 <= j < |ts[..i]| ==> ts[j] as int < |s.validators|
    //         //invariant s' == updateAttesterSlashing(s, ts[..i])
    //         invariant s'.slot == s.slot
    //         //invariant s'.latest_block_header == s.latest_block_header
    //     {
    //         assert forall j,k :: 0 <= j < k < |a.attestation_1.attesting_indices| 
    //             ==> a.attestation_1.attesting_indices[j] < a.attestation_1.attesting_indices[k];
    //         assert forall j,k :: 0 <= j < k < |a.attestation_2.attesting_indices| 
    //             ==> a.attestation_2.attesting_indices[j] < a.attestation_2.attesting_indices[k];
    //         //assert ts == sorted_intersection_fn(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices);
    //         assert 0 <= i < |ts|;
    //         assert 0 <= i+1 <= |ts|;

    //         //assert ts[i] as int < |s'.validators|;
    //         //assert ts == sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices);
    //         //assert |ts|> 0;
    //         assert ts[..i+1] == ts[..i] + [ts[i]];
    //         //assert s' == updateAttesterSlashing(s, ts[..i]);
            
    //         // if (is_slashable_validator(s'.validators[ts[i]], get_current_epoch(s'))) {
    //         //     //assert ts[i] as int < |s'.validators|; 
    //         //     slashValidatorPreservesActivateValidators(s', ts[i], get_beacon_proposer_index(s'));
    //         //     //assert get_active_validator_indices(s'.validators, get_current_epoch(s')) 
    //         //     //    == get_active_validator_indices(slash_validator(s',indices[i],get_beacon_proposer_index(s')).validators, get_current_epoch(s'));
                
    //         //     s' := slash_validator(s', ts[i], get_beacon_proposer_index(s'));

    //         //     //slashed_any := true;
    //         // }
    //         // else {
    //         //     s' := s';
    //         // }
    //         //assert s' == updateAttesterSlashing(s, ts[..i+1]);
    //         i := i+1;
            

    //     }
    //     assert i == |ts|;
    //     assert ts[..i] == ts;
    //     //assert s' == updateAttesterSlashing(s, ts);


    //     // for index in sorted(indices):
    //     //     if is_slashable_validator(state.validators[index], get_current_epoch(state)):
    //     //         slash_validator(state, index)
    //     //         slashed_any = True
        
    //     return s';
    //     // assert slashed_any

        
    // }

    // Voluntary exits
    method process_voluntary_exit(s: BeaconState, voluntary_exit: VoluntaryExit) returns (s' : BeaconState) 
        requires |s.validators| == |s.balances|
        requires voluntary_exit.validator_index as int < |s.validators|
        //requires is_active_validator(s.validators[voluntary_exit.validator_index], get_current_epoch(s))
        requires !s.validators[voluntary_exit.validator_index].slashed
        requires s.validators[voluntary_exit.validator_index].activationEpoch <= get_current_epoch(s) < s.validators[voluntary_exit.validator_index].withdrawableEpoch

        requires s.validators[voluntary_exit.validator_index].exitEpoch == FAR_FUTURE_EPOCH
        requires get_current_epoch(s) >= voluntary_exit.epoch
        requires get_current_epoch(s) >= s.validators[voluntary_exit.validator_index].activationEpoch + SHARD_COMMITTEE_PERIOD 
        
        ensures s' == updateVoluntaryExit(s, voluntary_exit)
    {
        var validator := s.validators[voluntary_exit.validator_index];

        // NOTE: If any of the spec asserts fail then the state is unchanged and the voluntary exit not implemented

        // # Verify the validator is active
        //assert is_active_validator(validator, get_current_epoch(s)); 
        assert is_active_validator(validator, get_current_epoch(s));

        // # Verify exit has not been initiated
        // assert validator.exit_epoch == FAR_FUTURE_EPOCH; 
        assert validator.exitEpoch == FAR_FUTURE_EPOCH;

        // # Exits must specify an epoch when they become valid; they are not valid before then
        // assert get_current_epoch(state) >= voluntary_exit.epoch; 
        assert get_current_epoch(s) >= voluntary_exit.epoch;

        // # Verify the validator has been active long enough
        // assert get_current_epoch(state) >= validator.activation_epoch + SHARD_COMMITTEE_PERIOD; 
        assert get_current_epoch(s) >= validator.activationEpoch + SHARD_COMMITTEE_PERIOD;

        // # Verify signature
        // Note: Not implemented as this stage
        // domain = get_domain(state, DOMAIN_VOLUNTARY_EXIT, voluntary_exit.epoch)
        // signing_root = compute_signing_root(voluntary_exit, domain)
        // assert bls.Verify(validator.pubkey, signing_root, signed_voluntary_exit.signature)

        // # Initiate exit
        s' := initiate_validator_exit(s, voluntary_exit.validator_index);
    }


       



}