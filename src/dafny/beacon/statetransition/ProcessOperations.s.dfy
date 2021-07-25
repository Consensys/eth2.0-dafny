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
include "../../utils/Eth2Types.dfy"
include "../../utils/Helpers.dfy"
include "../../utils/MathHelpers.dfy"
include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../validators/Validators.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../Helpers.dfy"
include "../Helpers.s.dfy"
include "../../ssz/Serialise.dfy"


/**
 *  Proofs for process operations
 */
module ProcessOperationsSpec {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NativeTypes
    import opened Eth2Types
    import opened Constants
    import opened BeaconChainTypes
    import opened Validators
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened BeaconHelpers
    import opened BeaconHelperSpec
    import opened MathHelpers
    import opened SSZ

    predicate isValidProposerSlashings(s: BeaconState, bb: BeaconBlockBody)
        requires minimumActiveValidators(s)
        requires  |s.validators| == |s.balances|
    {
        // proposer slashing preconditions
        (forall i,j :: 0 <= i < j < |bb.proposer_slashings| && i != j ==> bb.proposer_slashings[i].header_1.proposer_index!= bb.proposer_slashings[j].header_1.proposer_index) // ve indices are unique
        &&
        (forall i :: 0 <= i < |bb.proposer_slashings| ==> 
            bb.proposer_slashings[i].header_1.slot == bb.proposer_slashings[i].header_2.slot
            && bb.proposer_slashings[i].header_1.proposer_index == bb.proposer_slashings[i].header_2.proposer_index
            && bb.proposer_slashings[i].header_1 == bb.proposer_slashings[i].header_2
            && bb.proposer_slashings[i].header_1.proposer_index as int < |s.validators| 
            && !s.validators[bb.proposer_slashings[i].header_1.proposer_index].slashed 
            && s.validators[bb.proposer_slashings[i].header_1.proposer_index].activation_epoch <= get_current_epoch(s) < s.validators[bb.proposer_slashings[i].header_1.proposer_index].withdrawable_epoch)
    }

    predicate isValidAttesterSlashings(s: BeaconState, bb: BeaconBlockBody)
        requires minimumActiveValidators(s)
        requires  |s.validators| == |s.balances|
    {
        // attester slashing preconditions
        (forall i :: 0 <= i < |bb.attester_slashings| ==> 
            forall j :: 0 <= j < |bb.attester_slashings[i].attestation_1.attesting_indices| ==> bb.attester_slashings[i].attestation_1.attesting_indices[j] as int < |s.validators| )

        && (forall i :: 0 <= i < |bb.attester_slashings| ==> 
            forall j :: 0 <= j < |bb.attester_slashings[i].attestation_2.attesting_indices| ==> bb.attester_slashings[i].attestation_2.attesting_indices[j] as int < |s.validators|)
            
        && (forall i :: 0 <= i < |bb.attester_slashings| ==> 
            && is_valid_indexed_attestation(s, bb.attester_slashings[i].attestation_1)
            && is_valid_indexed_attestation(s, bb.attester_slashings[i].attestation_2)
            && |sorted_intersection(bb.attester_slashings[i].attestation_1.attesting_indices, bb.attester_slashings[i].attestation_2.attesting_indices)| > 0
            && is_slashable_attestation_data(bb.attester_slashings[i].attestation_1.data, bb.attester_slashings[i].attestation_2.data)
            && is_valid_indexed_attestation(s, bb.attester_slashings[i].attestation_1)
            && is_valid_indexed_attestation(s, bb.attester_slashings[i].attestation_2)
            && |sorted_intersection(bb.attester_slashings[i].attestation_1.attesting_indices, bb.attester_slashings[i].attestation_2.attesting_indices)| > 0
        )
    }

    predicate isValidAttestations(s: BeaconState, bb: BeaconBlockBody)
        requires minimumActiveValidators(s)
        requires  |s.validators| == |s.balances|
    {
        // process attestation preconditions
        |bb.attestations| as nat <= MAX_ATTESTATIONS as nat
        && (forall i:: 0 <= i < |bb.attestations| ==> attestationIsWellFormed(s, bb.attestations[i]))
        && |s.current_epoch_attestations| as nat + |bb.attestations| as nat <= MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
        && |s.previous_epoch_attestations| as nat + |bb.attestations| as nat <= MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
    }

    predicate isValidDeposits(s: BeaconState, bb: BeaconBlockBody)
        requires minimumActiveValidators(s)
        requires  |s.validators| == |s.balances|
    {
        // process deposit preconditions
        (s.eth1_deposit_index as int +  |bb.deposits| < 0x10000000000000000 )
        && (|s.validators| + |bb.deposits| <= VALIDATOR_REGISTRY_LIMIT as int)
        && (total_balances(s.balances) + total_deposits(bb.deposits) < 0x10000000000000000 )
    }

    predicate isValidVoluntaryExits(s: BeaconState, bb: BeaconBlockBody)
        requires minimumActiveValidators(s)
        requires  |s.validators| == |s.balances|
    {
        // voluntary exit preconditions
        (forall i,j :: 0 <= i < j < |bb.voluntary_exits| && i != j ==> bb.voluntary_exits[i].validator_index != bb.voluntary_exits[j].validator_index )// ve indices are unique
        && (forall i :: 0 <= i < |bb.voluntary_exits| ==> 
             bb.voluntary_exits[i].validator_index as int < |s.validators| 
             && get_current_epoch(s) >= bb.voluntary_exits[i].epoch
             && !s.validators[bb.voluntary_exits[i].validator_index].slashed
             && s.validators[bb.voluntary_exits[i].validator_index].activation_epoch <= get_current_epoch(s) < s.validators[bb.voluntary_exits[i].validator_index].withdrawable_epoch
             && s.validators[bb.voluntary_exits[i].validator_index].exitEpoch == FAR_FUTURE_EPOCH
             && (get_current_epoch(s) as nat >= s.validators[bb.voluntary_exits[i].validator_index].activation_epoch as nat + SHARD_COMMITTEE_PERIOD as nat)
            )
    }

    predicate isValidBeaconBlockBody(s: BeaconState, bb: BeaconBlockBody)
        requires minimumActiveValidators(s)
        requires  |s.validators| == |s.balances|
        // Note: A proof could be constructed to show that the intermediate states apply for s as well.
        //      i.e. try to show the preconditions based on state s
    {
        isValidProposerSlashings(s, bb)
        && isValidAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb)
        && isValidAttestations(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb)
        && isValidDeposits(updateAttestations(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.attestations),bb)
        && isValidVoluntaryExits(updateDeposits(updateAttestations(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.attestations),bb.deposits),bb)
    }

    function updateOperations(s: BeaconState, bb: BeaconBlockBody): BeaconState
        requires  |s.validators| == |s.balances|
        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires isValidBeaconBlockBody(s, bb)

        ensures updateOperations(s, bb) == updateVoluntaryExits(updateDeposits(updateAttestations(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.attestations), bb.deposits), bb.voluntary_exits)
    {
        //assert isValidProposerSlashings(s, bb);
        var s1 := updateProposerSlashings(s, bb.proposer_slashings);
        assert s1 == updateProposerSlashings(s, bb.proposer_slashings);
        //assert get_current_epoch(s1) == get_current_epoch(s);
        
        var s2 := updateAttesterSlashings(s1, bb.attester_slashings);
        assert s2 == updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings);
        
        var s3 := updateAttestations(s2, bb.attestations);
        assert s3 == updateAttestations(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.attestations);
        
        var s4 := updateDeposits(s3, bb.deposits);
        assert s4 == updateDeposits(updateAttestations(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.attestations), bb.deposits);

         var s5 := updateVoluntaryExits(s4, bb.voluntary_exits);
        assert s5 == updateVoluntaryExits(updateDeposits(updateAttestations(updateAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb.attester_slashings), bb.attestations), bb.deposits), bb.voluntary_exits);
        
        s5
    }

    
    /**
     *  Take into account deposits in a block.
     *
     *  @param  s           A beacon state.
     *  @param  deposits    A list of deposits from a block body.
     *  @returns            The state obtained after taking account the deposits in `body` from state `s` 
     */
    function updateDeposits(s: BeaconState, deposits: seq<Deposit>) : BeaconState 
        requires minimumActiveValidators(s)
        requires s.eth1_deposit_index as int +  |deposits| < 0x10000000000000000 
        requires |s.validators| == |s.balances|
        requires |s.validators| + |deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        //requires forall i,j :: 0 <= i < j < |s.validators| ==> s.validators[i].pubkey != s.validators[j].pubkey

        requires total_balances(s.balances) + total_deposits(deposits) < 0x10000000000000000 // less than total eth
        //requires forall i :: 0 <= i < |s.validators| ==> s.balances[i] as int + get_deposit_total(s.validators[i].pubkey, deposits) as int < 0x10000000000000000
        
        //ensures updateDeposits(s, deposits).slot == s.slot 
        //ensures updateDeposits(s, deposits).latest_block_header == s.latest_block_header
        //ensures updateDeposits(s, deposits).block_roots == s.block_roots
        //ensures updateDeposits(s, deposits).state_roots == s.state_roots

        ensures updateDeposits(s, deposits).eth1_deposit_index == s.eth1_deposit_index  + |deposits| as uint64 
        ensures |s.validators| <= |updateDeposits(s,deposits).validators| <= |s.validators| + |deposits| 
        
        // include properties ???
        //ensures |updateDeposits(s,deposits).validators| == |updateDeposits(s,deposits).balances|        
        //ensures |s.balances| <= |updateDeposits(s,deposits).balances| <= |s.balances| + |deposits| 

        ensures total_balances(updateDeposits(s,deposits).balances) == total_balances(s.balances) + total_deposits(deposits)
        ensures get_current_epoch(updateDeposits(s, deposits)) == get_current_epoch(s)
        ensures minimumActiveValidators(updateDeposits(s, deposits))
        
         decreases |deposits|
    {
        if |deposits| == 0 then s
        else 
            //assert |deposits| > 0;
            //assert forall i :: 0 <= i < |s.validators| ==> s.balances[i] as int + get_deposit_total(s.validators[i].pubkey, deposits) as int < 0x10000000000000000
            //assert total_balances(s.balances) + total_deposits(deposits[..|deposits|-1]) < 0x10000000000000000 ;
            //assert total_deposits(deposits[..|deposits|-1]) + total_deposits([deposits[|deposits|-1]]) == total_deposits(deposits) ;
            //updateDeposits(s,deposits[..|deposits|-1])
            //assert total_balances(s.balances) + total_deposits([deposits[|deposits|-1]]) < 0x10000000000000000;
            //updateBalancesLemma(s,deposits);
            //assert total_balances(s.balances) + total_deposits(deposits[..|deposits|-1]) < 0x10000000000000000;
            //assert deposits[|deposits|-1].data.amount as int < total_deposits(deposits);
            //assert total_balances(updateDeposits(s,deposits[..|deposits|-1]).balances) + deposits[|deposits|-1].data.amount as int < 0x10000000000000000;

            updateBalTotalBySingleDeposit(updateDeposits(s,deposits[..|deposits|-1]), deposits[|deposits|-1]);

            updateDeposit(updateDeposits(s,deposits[..|deposits|-1]),deposits[|deposits|-1])
    }

    /**
     *  Take into account a single deposit from a block.
     *
     *  @param  s       A beacon state.
     *  @param  d       A single deposit.
     *  @returns        The state obtained after taking account the deposit `d` from state `s` 
     */
    function updateDeposit(s: BeaconState, d: Deposit) : BeaconState 
        requires s.eth1_deposit_index as int +  1 < 0x10000000000000000 
        requires |s.validators| == |s.balances|
        requires |s.validators| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
        requires total_balances(s.balances) + d.data.amount as int < 0x10000000000000000
        
        //requires d.data.pubkey in seqKeysInValidators(s.validators) ==> s.balances[get_validator_index(seqKeysInValidators(s.validators), d.data.pubkey)] as int + d.data.amount as int < 0x10000000000000000
        
        ensures d.data.pubkey !in seqKeysInValidators(s.validators) ==> updateDeposit(s,d).validators == s.validators + [get_validator_from_deposit(d)]
        ensures d.data.pubkey in seqKeysInValidators(s.validators)  ==> updateDeposit(s,d).validators == s.validators 
        
        ensures updateDeposit(s,d).eth1_deposit_index == s.eth1_deposit_index + 1
        //ensures updateDeposit(s,d).slot == s.slot
        //ensures updateDeposit(s,d).latest_block_header == s.latest_block_header
        //ensures updateDeposit(s,d).block_roots == s.block_roots
        //ensures updateDeposit(s,d).state_roots == s.state_roots

        ensures |updateDeposit(s,d).validators| == |updateDeposit(s,d).balances|        // maybe include in property lemmas
        ensures |s.validators| <= |updateDeposit(s,d).validators| <= |s.validators| + 1 // maybe include in property lemmas
        ensures |s.balances| <= |updateDeposit(s,d).balances| <= |s.balances| + 1 // maybe include in property lemmas
        ensures forall i :: 0 <= i < |s.balances| ==> s.balances[i] <= updateDeposit(s,d).balances[i]
        //ensures total_balances(updateDeposit(s,d).balances) == total_balances(s.balances) + d.data.amount as int < 0x10000000000000000
        // in lemma
        
    {
        var pk := seqKeysInValidators(s.validators); 
        
        s.(
            eth1_deposit_index := (s.eth1_deposit_index as int + 1) as uint64,
            validators := if d.data.pubkey in pk then 
                                s.validators // unchanged validator members
                            else 
                                validator_append(s.validators, get_validator_from_deposit(d)), //(s.validators + [get_validator_from_deposit(d)]),
            balances := if d.data.pubkey in pk then 
                                individualBalanceBoundMaintained(s.balances,d);
                                //assert s.balances[get_validator_index(pk, d.data.pubkey)] as int + d.data.amount as int < 0x10000000000000000;
                                increase_balance(s,get_validator_index(pk, d.data.pubkey),d.data.amount).balances
                            else 
                                balance_append(s.balances, d.data.amount) //s.balances + [d.data.amount]
        )
    }



    

    ///////////////////////
    predicate attestationIsWellFormed(s: BeaconState, a: Attestation)
    {
        get_previous_epoch(s) <= a.data.target.epoch <= get_current_epoch(s)  
        /** Epoch of target matches epoch of the slot the attestation is made. */
        && a.data.target.epoch == compute_epoch_at_slot(a.data.slot)
        /** Attestation is not too old and not too recent. */
        && a.data.slot as nat + MIN_ATTESTATION_INCLUSION_DELAY as nat <= s.slot as nat <= a.data.slot as nat + SLOTS_PER_EPOCH as nat
        
        && a.data.index < get_committee_count_per_slot(s, a.data.target.epoch)
        // Preconditions for get_beacon_committee
        && TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        && a.data.index < TWO_UP_6 // this comes from the assert on attestations in process_attestations
        // same as above
        //&& a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) // at most 64 committees per slot 
    
        && |a.aggregation_bits| == |get_beacon_committee(s, a.data.slot, a.data.index)|
        
        && (if a.data.target.epoch == get_current_epoch(s) then  
            a.data.source == s.current_justified_checkpoint
           else 
            a.data.source == s.previous_justified_checkpoint)

    }

    function updateAttestation(s: BeaconState, a: Attestation) : BeaconState
        requires attestationIsWellFormed(s, a)
        requires |s.current_epoch_attestations| < MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
        requires |s.previous_epoch_attestations| < MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
        requires minimumActiveValidators(s)
        ensures minimumActiveValidators(updateAttestation(s, a))
        ensures |updateAttestation(s, a).current_epoch_attestations| + |updateAttestation(s, a).previous_epoch_attestations| ==
                |s.current_epoch_attestations| + |s.previous_epoch_attestations| + 1
        ensures |s.current_epoch_attestations| <= |updateAttestation(s, a).current_epoch_attestations| <= |s.current_epoch_attestations| + 1
        ensures |s.previous_epoch_attestations| <=|updateAttestation(s, a).previous_epoch_attestations| <= |s.previous_epoch_attestations| + 1

        ensures updateAttestation(s, a) == s.(current_epoch_attestations := updateAttestation(s, a).current_epoch_attestations) ||
                 updateAttestation(s, a) == s.(previous_epoch_attestations := updateAttestation(s, a).previous_epoch_attestations)
        ensures updateAttestation(s, a).validators == s.validators
        ensures updateAttestation(s, a).balances == s.balances
        ensures updateAttestation(s, a).slot == s.slot
        ensures updateAttestation(s, a).current_justified_checkpoint == s.current_justified_checkpoint
        ensures updateAttestation(s, a).previous_justified_checkpoint == s.previous_justified_checkpoint
        ensures updateAttestation(s, a).eth1_deposit_index == s.eth1_deposit_index

    {
        // data = attestation.data
        assert get_previous_epoch(s) <= a.data.target.epoch <=  get_current_epoch(s);
        assert a.data.target.epoch == compute_epoch_at_slot(a.data.slot);
        assert a.data.slot as nat + MIN_ATTESTATION_INCLUSION_DELAY as nat <= s.slot as nat <= a.data.slot as nat + SLOTS_PER_EPOCH as nat;
        assert a.data.index < get_committee_count_per_slot(s, a.data.target.epoch);

        var committee := get_beacon_committee(s, a.data.slot, a.data.index);
        assert |a.aggregation_bits| == |committee|;

        var pending_attestation := PendingAttestation(
            a.aggregation_bits, 
            a.data, 
            (s.slot - a.data.slot), 
            get_beacon_proposer_index(s) 
        );

        if a.data.target.epoch == get_current_epoch(s) then
            //  Add a to current attestations
            assert a.data.source == s.current_justified_checkpoint;
            s.(
                current_epoch_attestations := s.current_epoch_attestations + [pending_attestation]
            )
            // s.current_epoch_attestations.append(pending_attestation)
        
        else 
            assert a.data.source == s.previous_justified_checkpoint;
            s.(
                previous_epoch_attestations := s.previous_epoch_attestations + [pending_attestation]
            )
        
            // s.previous_epoch_attestations.append(pending_attestation)
            
        // # Verify signature
        // Not implemented as part of the simplificiation
        //assert is_valid_indexed_attestation(s', get_indexed_attestation(s', a));
    }

    function updateAttestations(s: BeaconState, a: seq<Attestation>) : BeaconState
        requires |s.validators| == |s.balances|
        requires |a| as nat <= MAX_ATTESTATIONS as nat
        requires forall i:: 0 <= i < |a| ==> attestationIsWellFormed(s, a[i])
        requires |s.current_epoch_attestations| as nat + |a| as nat <= MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
        requires |s.previous_epoch_attestations| as nat + |a| as nat <= MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
        requires minimumActiveValidators(s)
        
        ensures |updateAttestations(s,a).validators| == |updateAttestations(s,a).balances|
        ensures |updateAttestations(s,a).current_epoch_attestations| + |updateAttestations(s,a).previous_epoch_attestations| ==
                |s.current_epoch_attestations| + |s.previous_epoch_attestations| + |a|
        ensures |updateAttestations(s,a).current_epoch_attestations| <= |s.current_epoch_attestations| + |a|;
        ensures |updateAttestations(s,a).previous_epoch_attestations| <= |s.previous_epoch_attestations| + |a|;

        ensures minimumActiveValidators(updateAttestations(s, a))
        ensures updateAttestations(s, a).validators == s.validators
        ensures updateAttestations(s, a).slot == s.slot
        ensures updateAttestations(s, a).current_justified_checkpoint == s.current_justified_checkpoint
        ensures updateAttestations(s, a).previous_justified_checkpoint == s.previous_justified_checkpoint
        // could add an ensures to demonstrate the fields changed i.e. current_epoch_attestations etc
        ensures updateAttestations(s, a).eth1_deposit_index == s.eth1_deposit_index
    {
        if |a| == 0 then s
        else 

            // data = attestation.data
            var index := |a| -1;
            // these should allow follow from the original preconditions
            // assert |a[..index]| as nat <= MAX_ATTESTATIONS as nat;
            // assert forall i:: 0 <= i < |a[..index]| ==> attestationIsWellFormed(s, a[i]);
            // assert |s.current_epoch_attestations| as nat + |a[..index]| as nat <= MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat ;
            // assert |s.previous_epoch_attestations| as nat + |a[..index]| as nat <= MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat ;
            // assert minimumActiveValidators(s);

            var s1 := updateAttestations(s,a[..index]);

            // these relate to the nested state == updateAttestations(s,a[..index])
            // assert s1.validators == s.validators;
            // assert s1.slot == s.slot;
            // assert s1.current_justified_checkpoint == s.current_justified_checkpoint;
            // assert s1.previous_justified_checkpoint == s.previous_justified_checkpoint;
            AttestationHelperLemma(s, s1, a[index]);

            //assert attestationIsWellFormed(s1, a[index]);

            assert |s1.current_epoch_attestations| + |s1.previous_epoch_attestations| ==
                |s.current_epoch_attestations| + |s.previous_epoch_attestations| + |a[..index]|;
            assert |s1.current_epoch_attestations| <= |s.current_epoch_attestations| + |a[..index]|;
            assert |s1.previous_epoch_attestations| <= |s.previous_epoch_attestations| + |a[..index]|;

            assert |a[..index]| < |a|;
            assert |updateAttestations(s,a[..index]).current_epoch_attestations| < MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat ;
            assert |updateAttestations(s,a[..index]).previous_epoch_attestations| < MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat ;
            assert minimumActiveValidators(updateAttestations(s,a[..index]));

            updateAttestation(s1, a[index])
    }

    function updateVoluntaryExit(s: BeaconState, voluntary_exit: VoluntaryExit) : BeaconState
        requires |s.validators| == |s.balances|
        requires voluntary_exit.validator_index as int < |s.validators| 
        //requires minimumActiveValidators(s)
        // requires is_active_validator(s.validators[voluntary_exit.validator_index], get_current_epoch(s))
        // (!v.slashed) && (v.activation_epoch <= epoch < v.withdrawable_epoch)
        requires !s.validators[voluntary_exit.validator_index].slashed
        requires s.validators[voluntary_exit.validator_index].activation_epoch <= get_current_epoch(s) < s.validators[voluntary_exit.validator_index].withdrawable_epoch

        requires s.validators[voluntary_exit.validator_index].exitEpoch == FAR_FUTURE_EPOCH
        requires get_current_epoch(s) >= voluntary_exit.epoch
        requires get_current_epoch(s) >= s.validators[voluntary_exit.validator_index].activation_epoch + SHARD_COMMITTEE_PERIOD 
        
        // the next requires is to prevent overflow
        //requires max_epoch(get_exit_epochs(s.validators) + [compute_activation_exit_epoch(get_current_epoch(s))]) as int + 1 + MIN_VALIDATOR_WITHDRAWABILITY_DELAY < 0x10000000000000000
        
        ensures |updateVoluntaryExit(s, voluntary_exit).validators| == |s.validators| 
        ensures |updateVoluntaryExit(s, voluntary_exit).validators| == |s.balances| 
        ensures forall i :: 0 <= i < |s.validators| && i != voluntary_exit.validator_index as int ==> updateVoluntaryExit(s, voluntary_exit).validators[i] == s.validators[i]
        //ensures forall i :: 0 <= i < |s.validators| && i != voluntary_exit.validator_index as int ==> updateVoluntaryExit(s, voluntary_exit).validators[i].exitEpoch == s.validators[i].exitEpoch
        
        ensures updateVoluntaryExit(s, voluntary_exit) == initiate_validator_exit(s, voluntary_exit.validator_index)
        ensures get_current_epoch(updateVoluntaryExit(s, voluntary_exit)) == get_current_epoch(s)
        ensures get_current_epoch(s) >= updateVoluntaryExit(s, voluntary_exit).validators[voluntary_exit.validator_index].activation_epoch + SHARD_COMMITTEE_PERIOD 
        ensures forall i :: 0 <= i < |s.validators| ==> updateVoluntaryExit(s, voluntary_exit).validators[i].activation_epoch == s.validators[i].activation_epoch
        ensures minimumActiveValidators(updateVoluntaryExit(s, voluntary_exit))
        // ensures active validators haven't changed??
    {
        
        var exit_epochs := get_exit_epochs(s.validators);
        
        var exit_queue_epoch := max_epoch(exit_epochs + [compute_activation_exit_epoch(get_current_epoch(s))]);

        assert compute_activation_exit_epoch(get_current_epoch(s)) > get_current_epoch(s);
        assert compute_activation_exit_epoch(get_current_epoch(s)) in (exit_epochs + [compute_activation_exit_epoch(get_current_epoch(s))]);
        assert max_epoch(exit_epochs + [compute_activation_exit_epoch(get_current_epoch(s))]) >= compute_activation_exit_epoch(get_current_epoch(s)); 
        assert max_epoch(exit_epochs + [compute_activation_exit_epoch(get_current_epoch(s))]) > get_current_epoch(s);
        assert exit_queue_epoch > get_current_epoch(s);

        var exit_queue_churn := |get_queue_churn(s.validators, exit_queue_epoch)|;
        var validator_churn_limit := get_validator_churn_limit(s);
        var index := voluntary_exit.validator_index;
        
        assume exit_queue_epoch as int + 1 + MIN_VALIDATOR_WITHDRAWABILITY_DELAY as nat < 0x10000000000000000; 
        assert minimumActiveValidators(s);
        assert exists v :: 0 <= v < |s.validators| && s.validators[v].activation_epoch <= get_current_epoch(s) < s.validators[v].exitEpoch;
        
        var s1 := if exit_queue_churn  >= get_validator_churn_limit(s) as nat then 
                s.(validators := s.validators[index as int := s.validators[index].(exitEpoch := exit_queue_epoch + 1 as Epoch,
                                                                    withdrawable_epoch := (exit_queue_epoch as nat + 1 + MIN_VALIDATOR_WITHDRAWABILITY_DELAY as nat) as Epoch)])
                else
                s.(validators := s.validators[index as int := s.validators[index].(exitEpoch := exit_queue_epoch,
                                                                    withdrawable_epoch := (exit_queue_epoch as nat + MIN_VALIDATOR_WITHDRAWABILITY_DELAY as nat) as Epoch)]);
        
        assert forall v :: 0 <= v < |s1.validators| ==>  s1.validators[v].activation_epoch ==  s.validators[v].activation_epoch;
        assert forall v :: 0 <= v < |s1.validators| ==>  s1.validators[v].exitEpoch > get_current_epoch(s1) || s1.validators[v].exitEpoch == s1.validators[v].exitEpoch;
        assert exists v :: 0 <= v < |s1.validators| && s1.validators[v].activation_epoch <= get_current_epoch(s1) < s1.validators[v].exitEpoch;
        assert minimumActiveValidators(s1);
        s1

    }

    
    
    function {:timeLimitMultiplier 1} updateVoluntaryExits(s: BeaconState, ve: seq<VoluntaryExit>) : BeaconState
        requires minimumActiveValidators(s)
        requires forall i,j :: 0 <= i < j < |ve| && i != j ==> ve[i].validator_index != ve[j].validator_index // ve indices are unique
        requires |s.validators| == |s.balances|
        requires forall i :: 0 <= i < |ve| ==> get_current_epoch(s) >= ve[i].epoch
        
        requires forall i :: 0 <= i < |ve| ==> ve[i].validator_index as int < |s.validators| 
        //requires forall i :: 0 <= i < |ve| ==> is_active_validator(s.validators[ve[i].validator_index], get_current_epoch(s))
        requires forall i :: 0 <= i < |ve| ==> !s.validators[ve[i].validator_index].slashed
        requires forall i :: 0 <= i < |ve| ==> s.validators[ve[i].validator_index].activation_epoch <= get_current_epoch(s) < s.validators[ve[i].validator_index].withdrawable_epoch

        requires forall i :: 0 <= i < |ve| ==> s.validators[ve[i].validator_index].exitEpoch == FAR_FUTURE_EPOCH
        requires forall i :: 0 <= i < |ve| ==> s.validators[ve[i].validator_index].activation_epoch as nat + SHARD_COMMITTEE_PERIOD as nat <= get_current_epoch(s) as nat < 0x10000000000000000 

        //requires forall i :: i in get_VolExit_validator_indices(ve) ==> 0 <= i < |s.validators| 
        
        // //requires forall i :: i in get_VolExit_validator_indices(ve) ==> is_active_validator(s.validators[i], get_current_epoch(s))
        //requires forall i :: i in get_VolExit_validator_indices(ve) ==> !s.validators[i].slashed
        //requires forall i :: i in get_VolExit_validator_indices(ve) ==> s.validators[i].activation_epoch <= get_current_epoch(s) < s.validators[i].withdrawable_epoch

        //requires forall i :: i in get_VolExit_validator_indices(ve) ==> s.validators[i].exitEpoch == FAR_FUTURE_EPOCH
        //requires forall i :: i in get_VolExit_validator_indices(ve) ==> get_current_epoch(s) >= s.validators[i].activation_epoch + SHARD_COMMITTEE_PERIOD 
    
        ensures |updateVoluntaryExits(s, ve).validators| == |s.validators|
        ensures |updateVoluntaryExits(s, ve).validators| == |updateVoluntaryExits(s, ve).balances|
        ensures updateVoluntaryExits(s, ve).slot == s.slot
        ensures get_current_epoch(updateVoluntaryExits(s, ve)) == get_current_epoch(s)
        ensures forall i :: 0 <= i < |s.validators| ==> updateVoluntaryExits(s, ve).validators[i].activation_epoch == s.validators[i].activation_epoch

        ensures forall i :: 0 <= i < |s.validators| && i !in get_VolExit_validator_indices(ve) ==> updateVoluntaryExits(s, ve).validators[i] == s.validators[i]
        ensures minimumActiveValidators(updateVoluntaryExits(s, ve))
        //ensures forall i :: 0 <= i < |s.validators| && i !in get_VolExit_validator_indices(ve) ==> updateVoluntaryExits(s, ve).validators[i].exitEpoch == s.validators[i].exitEpoch
        //ensures forall i :: 0 <= i < |s.validators| && i !in get_VolExit_validator_indices(ve) ==> updateVoluntaryExits(s, ve).validators[i].slashed == s.validators[i].slashed
        //ensures forall i :: 0 <= i < |s.validators| && i !in get_VolExit_validator_indices(ve) ==> updateVoluntaryExits(s, ve).validators[i].withdrawable_epoch == s.validators[i].withdrawable_epoch
        //ensures forall i :: 0 <= i < |s.validators| ==> forall j :: 0 <= j < |ve| && i != ve[j].validator_index as int ==> updateVoluntaryExits(s, ve).validators[i].exitEpoch == s.validators[i].exitEpoch

        //ensures forall i :: 0 <= i < |ve| ==> get_current_epoch(s) >= updateVoluntaryExits(s, ve).validators[ve[i].validator_index].activation_epoch + SHARD_COMMITTEE_PERIOD
        //ensures forall i :: 0 <= i < |ve| ==> is_active_validator(updateVoluntaryExits(s,ve).validators[ve[i].validator_index], get_current_epoch(s))
        decreases |ve|
    {
        if |ve| == 0 then 
            //assert get_VolExit_validator_indices(ve) == [];
            //assert forall i :: 0 <= i < |s.validators| && i !in get_VolExit_validator_indices(ve) ==> updateVoluntaryExits(s, ve).validators[i].exitEpoch == s.validators[i].exitEpoch;
            s
        // else if |ve| == 1 then
        //     assert |ve[..|ve|-1]| == 0;
        //     assert updateVoluntaryExits(s,ve[..|ve|-1]) == s;
        //     assert forall i :: 0 <= i < |s.validators| && i !in get_VolExit_validator_indices(ve) ==> updateVoluntaryExits(s, ve).validators[i].exitEpoch == s.validators[i].exitEpoch;
        //     updateVoluntaryExit(s, ve[|ve|-1])

        else
            helperVoluntaryExitLemma3(s, ve);
            helperVoluntaryExitLemma2(s, ve);
            assert forall i :: i in get_VolExit_validator_indices(ve[..|ve|-1]) ==> 0 <= i < |s.validators|; 

            assert forall i :: i in get_VolExit_validator_indices(ve[..|ve|-1]) ==> !s.validators[i].slashed;
            assert forall i :: i in get_VolExit_validator_indices(ve[..|ve|-1]) ==> s.validators[i].activation_epoch <= get_current_epoch(s) < s.validators[i].withdrawable_epoch;
            assert forall i :: i in get_VolExit_validator_indices(ve[..|ve|-1]) ==> s.validators[i].exitEpoch == FAR_FUTURE_EPOCH;
            assert forall i :: i in get_VolExit_validator_indices(ve[..|ve|-1]) ==> get_current_epoch(s) >= s.validators[i].activation_epoch + SHARD_COMMITTEE_PERIOD;
            //assert forall i :: 0 <= i < |s.validators| && i !in get_VolExit_validator_indices(ve[..|ve|-1]) ==> 
            //    updateVoluntaryExits(s,ve[..|ve|-1]).validators[i].exitEpoch == s.validators[i].exitEpoch;

            // assert forall i :: 0 <= i < |s.validators| && i !in get_VolExit_validator_indices(ve[..|ve|-1]) ==> updateVoluntaryExits(s, ve[..|ve|-1]).validators[i].slashed == s.validators[i].slashed;
            // assert ve[|ve|-1].validator_index as int !in get_VolExit_validator_indices(ve[..|ve|-1]) ==> 
            //     updateVoluntaryExits(s, ve[..|ve|-1]).validators[ve[|ve|-1].validator_index].slashed  == s.validators[ve[|ve|-1].validator_index].slashed;
            // assert !s.validators[ve[|ve|-1].validator_index].slashed;

            // assert forall i :: 0 <= i < |s.validators| && i !in get_VolExit_validator_indices(ve[..|ve|-1]) ==> updateVoluntaryExits(s, ve[..|ve|-1]).validators[i].exitEpoch == s.validators[i].exitEpoch;
            // assert ve[|ve|-1].validator_index as int !in get_VolExit_validator_indices(ve[..|ve|-1]) ==> 
            //     updateVoluntaryExits(s, ve[..|ve|-1]).validators[ve[|ve|-1].validator_index].exitEpoch  == s.validators[ve[|ve|-1].validator_index].exitEpoch;
            // assert ve[|ve|-1].validator_index as int in get_VolExit_validator_indices(ve) ==> s.validators[ve[|ve|-1].validator_index].exitEpoch == FAR_FUTURE_EPOCH;

            assert |updateVoluntaryExits(s,ve[..|ve|-1]).validators| == |s.validators|;
            mappingVolExitIndices(ve);
            subsetMappingVolExitIndices(ve, |ve|-1);
            //assume ve[|ve|-1].validator_index as int < |updateVoluntaryExits(s,ve[..|ve|-1]).validators|;
            //assert forall i :: i in get_VolExit_validator_indices(ve) ==> i < |s.validators|;  // from requires
            assert ve[|ve|-1].validator_index as int in get_VolExit_validator_indices(ve);

            //assume get_current_epoch(updateVoluntaryExits(s,ve[..|ve|-1])) >= ve[|ve|-1].epoch;
            assert get_current_epoch(updateVoluntaryExits(s,ve[..|ve|-1])) == get_current_epoch(s);
            assert get_current_epoch(s) >= ve[|ve|-1].epoch; // from requires

            helperVoluntaryExitLemma(updateVoluntaryExits(s,ve[..|ve|-1]), ve[|ve|-1]);
            updateVoluntaryExit(updateVoluntaryExits(s,ve[..|ve|-1]), ve[|ve|-1])
    }

    
    

    



    function updateProposerSlashing(s: BeaconState, ps : ProposerSlashing) : BeaconState 
        requires ps.header_1.slot == ps.header_2.slot
        requires ps.header_1.proposer_index == ps.header_2.proposer_index 
        requires ps.header_1 == ps.header_2
        requires ps.header_1.proposer_index as int < |s.validators| 
        //requires is_slashable_validator(s.validators[ps.header_1.proposer_index], get_current_epoch(s));
        requires !s.validators[ps.header_1.proposer_index].slashed
        requires s.validators[ps.header_1.proposer_index].activation_epoch <= get_current_epoch(s) < s.validators[ps.header_1.proposer_index].withdrawable_epoch

        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires |s.validators| == |s.balances|

        ensures |s.validators| == |updateProposerSlashing(s, ps).validators| 
        ensures |s.balances| == |updateProposerSlashing(s, ps).balances| 
        
        ensures forall i :: 0 <= i < |s.validators| && i != ps.header_1.proposer_index as int ==> updateProposerSlashing(s, ps).validators[i] == s.validators[i]
        //ensures forall i :: 0 <= i < |s.validators| && i != ps.header_1.proposer_index as int ==> updateProposerSlashing(s, ps).validators[i].exitEpoch == s.validators[i].exitEpoch
        //ensures forall i :: 0 <= i < |s.validators| && i != ps.header_1.proposer_index as int ==> updateProposerSlashing(s, ps).validators[i].withdrawable_epoch == s.validators[i].withdrawable_epoch
        //ensures forall i :: 0 <= i < |s.validators| && i != ps.header_1.proposer_index as int ==> updateProposerSlashing(s, ps).validators[i].slashed == s.validators[i].slashed


        ensures updateProposerSlashing(s, ps) == slash_validator(s, ps.header_1.proposer_index, get_beacon_proposer_index(s))
        ensures get_current_epoch(updateProposerSlashing(s, ps)) == get_current_epoch(s)
        ensures forall i :: 0 <= i < |s.validators| ==> updateProposerSlashing(s, ps).validators[i].activation_epoch == s.validators[i].activation_epoch
       
        ensures updateProposerSlashing(s, ps).slot == s.slot
        ensures updateProposerSlashing(s, ps).eth1_deposit_index == s.eth1_deposit_index
        ensures updateProposerSlashing(s, ps).latest_block_header == s.latest_block_header
        
        //ensures get_current_epoch(s) >= updateVoluntaryExit(s, voluntary_exit).validators[voluntary_exit.validator_index].activation_epoch + SHARD_COMMITTEE_PERIOD 
    {
        slash_validator(s, ps.header_1.proposer_index, get_beacon_proposer_index(s))
        // maybe expand???
    }

    

    function updateProposerSlashings(s: BeaconState, ps : seq<ProposerSlashing>) : BeaconState
        requires minimumActiveValidators(s)
        requires forall i,j :: 0 <= i < j < |ps| && i != j ==> ps[i].header_1.proposer_index!= ps[j].header_1.proposer_index // ve indices are unique
        
        requires forall i :: 0 <= i < |ps| ==> ps[i].header_1.slot == ps[i].header_2.slot
        requires forall i :: 0 <= i < |ps| ==> ps[i].header_1.proposer_index == ps[i].header_2.proposer_index 
        requires forall i :: 0 <= i < |ps| ==> ps[i].header_1 == ps[i].header_2
        requires forall i :: 0 <= i < |ps| ==> ps[i].header_1.proposer_index as int < |s.validators| 
        requires forall i :: 0 <= i < |ps| ==> !s.validators[ps[i].header_1.proposer_index].slashed 
        requires forall i :: 0 <= i < |ps| ==> s.validators[ps[i].header_1.proposer_index].activation_epoch <= get_current_epoch(s) < s.validators[ps[i].header_1.proposer_index].withdrawable_epoch

        
        //requires forall i :: 0 <= i < |ps| ==> is_slashable_validator(s.validators[ps[i].header_1.proposer_index], get_current_epoch(s));
        //requires forall i :: i in get_PS_validator_indices(ps) ==> 0 <= i < |s.validators| //this should be the same as the previous requires!
        //requires forall i :: i in get_PS_validator_indices(ps) ==> !s.validators[i].slashed
        //requires forall i :: i in get_PS_validator_indices(ps) ==> s.validators[i].activation_epoch <= get_current_epoch(s) < s.validators[i].withdrawable_epoch
        
        
        //requires forall i :: 0 <= i < |ps| ==> !s.validators[ps[i].header_1.proposer_index].slashed
        //requires forall i :: 0 <= i < |ps| ==> s.validators[ps[i].header_1.proposer_index].activation_epoch <= get_current_epoch(s) < s.validators[ps[i].header_1.proposer_index].withdrawable_epoch


        //requires forall i :: 0 <= i < |ps| ==> s.validators[ps[i].header_1.proposer_index].exitEpoch == FAR_FUTURE_EPOCH
        // not required for proposer slashings (but is for vol exits)
        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires |s.validators| == |s.balances|

        ensures |updateProposerSlashings(s, ps).validators| == |s.validators|
        ensures |updateProposerSlashings(s, ps).validators| == |updateProposerSlashings(s, ps).balances|

        ensures get_current_epoch(updateProposerSlashings(s, ps)) == get_current_epoch(s)
        ensures forall i :: 0 <= i < |s.validators| ==> updateProposerSlashings(s, ps).validators[i].activation_epoch == s.validators[i].activation_epoch
        //ensures forall i :: 0 <= i < |s.validators| ==> forall j :: 0 <= j < |ps| && i != ps[j].header_1.proposer_index as int ==> updateProposerSlashings(s, ps).validators[i].exitEpoch == s.validators[i].exitEpoch
        //ensures forall i :: 0 <= i < |s.validators| ==> forall j :: 0 <= j < |ps| && i != ps[j].header_1.proposer_index as int ==> updateProposerSlashings(s, ps).validators[i].withdrawable_epoch == s.validators[i].withdrawable_epoch
        //ensures forall i :: 0 <= i < |s.validators| ==> forall j :: 0 <= j < |ps| && i != ps[j].header_1.proposer_index as int ==> updateProposerSlashings(s, ps).validators[i].slashed == s.validators[i].slashed

        ensures |get_active_validator_indices(updateProposerSlashings(s, ps).validators, get_current_epoch(s))| > 0
        ensures forall i :: 0 <= i < |s.validators| && i !in get_PS_validator_indices(ps) ==> updateProposerSlashings(s, ps).validators[i] == s.validators[i]
        

        ensures updateProposerSlashings(s, ps).slot == s.slot
        ensures updateProposerSlashings(s, ps).eth1_deposit_index == s.eth1_deposit_index
        ensures updateProposerSlashings(s, ps).latest_block_header == s.latest_block_header
        ensures minimumActiveValidators(updateProposerSlashings(s, ps))

        decreases |ps|

    {
        if |ps| == 0 then s
        else
            helperPSLemma3(s, ps);
            helperPSLemma2(s, ps);
            assert forall i :: i in get_PS_validator_indices(ps[..|ps|-1]) ==> 0 <= i < |s.validators|; 
            assert forall i :: i in get_PS_validator_indices(ps[..|ps|-1]) ==> !s.validators[i].slashed;
            assert forall i :: i in get_PS_validator_indices(ps[..|ps|-1]) ==> s.validators[i].activation_epoch <= get_current_epoch(s) < s.validators[i].withdrawable_epoch;
            //assert forall i :: i in get_PS_validator_indices(ps[..|ps|-1]) ==> get_current_epoch(s) >= s.validators[i].activation_epoch + SHARD_COMMITTEE_PERIOD;
            assert |updateProposerSlashings(s,ps[..|ps|-1]).validators| == |s.validators|;
            mappingPSIndices(ps);
            subsetMappingPSIndices(ps, |ps|-1);
            //assume ve[|ve|-1].validator_index as int < |updateVoluntaryExits(s,ve[..|ve|-1]).validators|;
            //assert forall i :: i in get_VolExit_validator_indices(ve) ==> i < |s.validators|;  // from requires
            assert ps[|ps|-1].header_1.proposer_index as int in get_PS_validator_indices(ps);

            //assume get_current_epoch(updateVoluntaryExits(s,ve[..|ve|-1])) >= ve[|ve|-1].epoch;
            assert get_current_epoch(updateProposerSlashings(s,ps[..|ps|-1])) == get_current_epoch(s);
            
            //assert get_current_epoch(s) >= ps[|ps|-1].epoch; // from requires

            helperPSLemma(updateProposerSlashings(s,ps[..|ps|-1]), ps[|ps|-1]);
            updateProposerSlashingLemma(updateProposerSlashings(s,ps[..|ps|-1]), ps[|ps|-1]);
            //ensures |get_active_validator_indices(updateProposerSlashing(s, ps).validators, get_current_epoch(s))| > 0

            updateProposerSlashing(updateProposerSlashings(s,ps[..|ps|-1]), ps[|ps|-1])

    }

    
    /////////////////////////////////////////////////////////////////////////////////////

    function updateAttesterSlashings(s: BeaconState, a: seq<AttesterSlashing>) : BeaconState 
        requires forall i :: 0 <= i < |a| ==> is_valid_indexed_attestation(s, a[i].attestation_1)
        requires forall i :: 0 <= i < |a| ==> is_valid_indexed_attestation(s, a[i].attestation_2)
        requires forall i :: 0 <= i < |a| ==> forall j :: 0 <= j < |a[i].attestation_1.attesting_indices| ==> a[i].attestation_1.attesting_indices[j] as int < |s.validators|
        requires forall i :: 0 <= i < |a| ==> forall j :: 0 <= j < |a[i].attestation_2.attesting_indices| ==> a[i].attestation_2.attesting_indices[j] as int < |s.validators|
        //requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires minimumActiveValidators(s)
        requires |s.validators| == |s.balances|

        // explicitly show we only slash those n the intersection

        ensures |s.validators| == |updateAttesterSlashings(s, a).validators| 
        ensures |updateAttesterSlashings(s, a).validators| == |updateAttesterSlashings(s, a).balances| 
        ensures updateAttesterSlashings(s, a).slot == s.slot
        ensures updateAttesterSlashings(s, a).eth1_deposit_index == s.eth1_deposit_index
        ensures updateAttesterSlashings(s, a).latest_block_header == s.latest_block_header
       
        //ensures |get_active_validator_indices(updateAttesterSlashings(s, a).validators, get_current_epoch(updateAttesterSlashings(s, a)))| > 0
        ensures minimumActiveValidators(updateAttesterSlashings(s, a))
        //decreases indices
    {
        if |a| == 0 then 
            s
        else  
            updateAttesterSlashing(updateAttesterSlashings(s, a[..|a|-1]), sorted_intersection(a[|a|-1].attestation_1.attesting_indices, a[|a|-1].attestation_2.attesting_indices))

    }

    
    
    function updateAttesterSlashing(s: BeaconState, indices: seq<uint64>) : BeaconState 
        
        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires |s.validators| == |s.balances|
        requires valid_state_indices(s,indices)
        //requires forall i :: 0 <= i < |indices| ==> indices[i] as int < |s.validators| 

        ensures |s.validators| == |updateAttesterSlashing(s, indices).validators| 
        ensures |updateAttesterSlashing(s, indices).validators| == |updateAttesterSlashing(s, indices).balances| 

        
        ensures updateAttesterSlashing(s, indices).slot == s.slot
        ensures updateAttesterSlashing(s, indices).eth1_deposit_index == s.eth1_deposit_index
        ensures updateAttesterSlashing(s, indices).latest_block_header == s.latest_block_header
        
        ensures |get_active_validator_indices(updateAttesterSlashing(s, indices).validators, get_current_epoch(updateAttesterSlashing(s, indices)))| > 0
        decreases indices
    {
        if |indices| == 0 then 
            s
        else 
            //slashValidatorPreservesActivateValidators(s, indices[|indices|-1], get_beacon_proposer_index(s));
            updateAttesterSlashingComp(updateAttesterSlashing(s, indices[..|indices|-1]), indices[|indices|-1] as ValidatorIndex)
            
    }

    function updateAttesterSlashingComp(s: BeaconState, slash_index: ValidatorIndex) : BeaconState 
        requires slash_index as int < |s.validators| 
        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires |s.validators| == |s.balances|
        ensures |updateAttesterSlashingComp(s, slash_index).validators| == |s.validators| 
        ensures |updateAttesterSlashingComp(s, slash_index).validators| == |updateAttesterSlashingComp(s, slash_index).balances| 
        ensures updateAttesterSlashingComp(s, slash_index).slot == s.slot
        ensures updateAttesterSlashingComp(s, slash_index).eth1_deposit_index == s.eth1_deposit_index
        
        ensures |get_active_validator_indices(updateAttesterSlashingComp(s, slash_index).validators, get_current_epoch(updateAttesterSlashingComp(s, slash_index)))| > 0
    {
        if is_slashable_validator(s.validators[slash_index], get_current_epoch(s)) then
            slashValidatorPreservesActivateValidators(s, slash_index, get_beacon_proposer_index(s));
            slash_validator(s, slash_index, get_beacon_proposer_index(s))
        else
            s
    }

    

    
    


   
    

    
    

}