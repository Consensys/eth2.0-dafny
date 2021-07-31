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

//  @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /timeLimit:50 /noCheating:0

include "../../utils/NativeTypes.dfy"
include "../../utils/Eth2Types.dfy"
include "../../utils/Helpers.dfy"
include "../../utils/MathHelpers.dfy"
include "../../utils/SeqHelpers.dfy"
include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../validators/Validators.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../Helpers.dfy"
include "../Helpers.s.dfy"
include "../Helpers.p.dfy"
include "../../ssz/Serialise.dfy"
include "ProcessOperations.p.dfy"


/**
 * Process operations functional specification.
 */
module ProcessOperationsSpec {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NativeTypes
    import opened Eth2Types
    import opened Constants
    import opened BeaconChainTypes
    import opened Validators
    import opened AttestationsTypes
    import opened BeaconHelpers
    import opened BeaconHelperProofs
    import opened BeaconHelperSpec
    import opened MathHelpers
    import opened SeqHelpers
    import opened SSZ
    import opened ProcessOperationsProofs

    //  Specifications of predicates and functions related to the process operation methods.
    //  e.g. process_proposer_slashing, process_deposit, etc
    //  For each process operations method there is a corresponding functional equivalent,
    //  as well as another functional representation of the processing of a sequence of such values.
    //  e.g. process_proposer_slashing --> updateProposerSlashing and updateProposerSlashings.
    //  The predicates are used to represent preconditions for the various components.

    // Predicates

    /**
     *  Check preconditions for a sequence of proposer slashings.
     *  
     *  @param  s       A beacon state.
     *  @param  bb      A beacon block body. 
     *  @returns        True if all bb.proposer_slashings[i] satisfy the preconditions
     *                  of process_proposer_slashing & updateProposerSlashings.
     */
    predicate isValidProposerSlashings(s: BeaconState, bb: BeaconBlockBody)
        requires minimumActiveValidators(s)
        requires  |s.validators| == |s.balances|
    {
        // proposer slashing preconditions
        (forall i,j :: 0 <= i < j < |bb.proposer_slashings| && i != j 
            ==> bb.proposer_slashings[i].header_1.proposer_index 
                != bb.proposer_slashings[j].header_1.proposer_index) // ve indices are unique
        &&
        (forall i :: 0 <= i < |bb.proposer_slashings| ==> 
            bb.proposer_slashings[i].header_1.slot == bb.proposer_slashings[i].header_2.slot
            && bb.proposer_slashings[i].header_1.proposer_index 
                == bb.proposer_slashings[i].header_2.proposer_index
            && bb.proposer_slashings[i].header_1 == bb.proposer_slashings[i].header_2
            && bb.proposer_slashings[i].header_1.proposer_index as int < |s.validators| 
            && !s.validators[bb.proposer_slashings[i].header_1.proposer_index].slashed 
            && s.validators[bb.proposer_slashings[i].header_1.proposer_index].activation_epoch 
                <= get_current_epoch(s) 
                < s.validators[bb.proposer_slashings[i].header_1.proposer_index].withdrawable_epoch)
    }

    /**
     *  Check preconditions for a sequence of attester slashings.
     *  
     *  @param  s       A beacon state.
     *  @param  bb      A beacon block body. 
     *  @returns        True if all bb.attester_slashings[i] satisfy the preconditions
     *                  of process_attester_slashing & updateAttesterSlashings.
     */
    predicate isValidAttesterSlashings(s: BeaconState, bb: BeaconBlockBody)
        requires minimumActiveValidators(s)
        requires  |s.validators| == |s.balances|
    {
        // attester slashing preconditions
        (forall i :: 0 <= i < |bb.attester_slashings| ==> 
            forall j :: 0 <= j < |bb.attester_slashings[i].attestation_1.attesting_indices| 
                ==> bb.attester_slashings[i].attestation_1.attesting_indices[j] as int < |s.validators| )

        && (forall i :: 0 <= i < |bb.attester_slashings| ==> 
            forall j :: 0 <= j < |bb.attester_slashings[i].attestation_2.attesting_indices| 
                ==> bb.attester_slashings[i].attestation_2.attesting_indices[j] as int < |s.validators|)
            
        && (forall i :: 0 <= i < |bb.attester_slashings| ==> 
            var a1 := bb.attester_slashings[i].attestation_1;
            var a2 := bb.attester_slashings[i].attestation_2;
            && is_valid_indexed_attestation(a1)
            && is_valid_indexed_attestation(a2)
            && |sorted_intersection(a1.attesting_indices, a2.attesting_indices)| > 0
            && is_slashable_attestation_data(a1.data, a2.data)
            && |sorted_intersection(a1.attesting_indices, a2.attesting_indices)| > 0
        )
    }

    /**
     *  Check preconditions for a sequence of attestations.
     *  
     *  @param  s       A beacon state.
     *  @param  bb      A beacon block body. 
     *  @returns        True if all bb.attestations[i] satisfy the preconditions
     *                  of process_attestation & updateAttestations.
     */
    predicate isValidAttestations(s: BeaconState, bb: BeaconBlockBody)
        requires minimumActiveValidators(s)
        requires  |s.validators| == |s.balances|
    {
        // process attestation preconditions
        |bb.attestations| as nat <= MAX_ATTESTATIONS as nat
        && (forall i:: 0 <= i < |bb.attestations| ==> attestationIsWellFormed(s, bb.attestations[i]))
        && |s.current_epoch_attestations| as nat + |bb.attestations| as nat 
            <= MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
        && |s.previous_epoch_attestations| as nat + |bb.attestations| as nat 
            <= MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
    }

    /**
     *  Check preconditions for a sequence of deposits.
     *  
     *  @param  s       A beacon state.
     *  @param  bb      A beacon block body. 
     *  @returns        True if bb.deposits satisfies the preconditions of process_deposit
     *                  & updateDeposits.
     */
    predicate isValidDeposits(s: BeaconState, bb: BeaconBlockBody)
        requires minimumActiveValidators(s)
        requires  |s.validators| == |s.balances|
    {
        // process deposit preconditions
        (s.eth1_deposit_index as int +  |bb.deposits| < 0x10000000000000000 )
        && (|s.validators| + |bb.deposits| <= VALIDATOR_REGISTRY_LIMIT as int)
        && (total_balances(s.balances) + total_deposits(bb.deposits) < 0x10000000000000000 )
    }

    /**
     *  Check preconditions for a sequence of voluntary exits.
     *  
     *  @param  s       A beacon state.
     *  @param  bb      A beacon block body. 
     *  @returns        True if all bb.voluntary_exits[i] satisfy the preconditions
     *                  of process_voluntary_exit & updateVoluntaryExits.
     */
    predicate isValidVoluntaryExits(s: BeaconState, bb: BeaconBlockBody)
        requires minimumActiveValidators(s)
        requires  |s.validators| == |s.balances|
    {
        // voluntary exit preconditions
        // indices are unique
        (forall i,j :: 0 <= i < j < |bb.voluntary_exits| && i != j 
            ==> bb.voluntary_exits[i].validator_index != bb.voluntary_exits[j].validator_index )
        
        && (forall i :: 0 <= i < |bb.voluntary_exits| ==> 
             bb.voluntary_exits[i].validator_index as int < |s.validators| 
             && get_current_epoch(s) >= bb.voluntary_exits[i].epoch
             && !s.validators[bb.voluntary_exits[i].validator_index].slashed
             && s.validators[bb.voluntary_exits[i].validator_index].activation_epoch 
                <= get_current_epoch(s) 
                < s.validators[bb.voluntary_exits[i].validator_index].withdrawable_epoch
             && s.validators[bb.voluntary_exits[i].validator_index].exitEpoch == FAR_FUTURE_EPOCH
             && (get_current_epoch(s) as nat 
                >= s.validators[bb.voluntary_exits[i].validator_index].activation_epoch as nat 
                    + SHARD_COMMITTEE_PERIOD as nat)
            )
    }

    /**
     *  Check preconditions required for a beacon block body to be processed.
     *  
     *  @param  s       A beacon state.
     *  @param  bb      A beacon block body. 
     *  @returns        True if all bb satisfies the preconditions of process_operations/updateOperations.
     *     
     *  @notes          A proof could be constructed to show that the intermediate states apply a s.
     *                  i.e. simplify to remove updateAttesterSlashings, updateAttestations, etc.
     */
    predicate isValidBeaconBlockBody(s: BeaconState, bb: BeaconBlockBody)
        requires minimumActiveValidators(s)
        requires  |s.validators| == |s.balances|
    {
        isValidProposerSlashings(s, bb)
        && isValidAttesterSlashings(updateProposerSlashings(s, bb.proposer_slashings), bb)
        && isValidAttestations(
                updateAttesterSlashings(
                    updateProposerSlashings(s, bb.proposer_slashings), 
                    bb.attester_slashings), 
                bb)
        && isValidDeposits(
                updateAttestations(
                    updateAttesterSlashings(
                        updateProposerSlashings(s, bb.proposer_slashings), 
                        bb.attester_slashings), 
                    bb.attestations),
                bb)
        && isValidVoluntaryExits(
                updateDeposits(
                    updateAttestations(
                        updateAttesterSlashings(
                            updateProposerSlashings(s, bb.proposer_slashings), 
                            bb.attester_slashings), 
                        bb.attestations),
                    bb.deposits),
                bb)
    }


    // Functional equivalents

    /**
     *  The functional equivalent of process_operations.
     *  
     *  @param  s       A beacon state.
     *  @param  bb      A beacon block body. 
     *  @returns        A new state obtained from processing operations.        
     */
    function updateOperations(s: BeaconState, bb: BeaconBlockBody): BeaconState
        requires  |s.validators| == |s.balances|
        //requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires minimumActiveValidators(s)
        requires isValidBeaconBlockBody(s, bb)

        ensures updateOperations(s, bb) == updateVoluntaryExits(
                                            updateDeposits(
                                                updateAttestations(
                                                    updateAttesterSlashings(
                                                        updateProposerSlashings(s, bb.proposer_slashings), 
                                                        bb.attester_slashings), 
                                                    bb.attestations), 
                                                bb.deposits), 
                                            bb.voluntary_exits)
        ensures minimumActiveValidators(updateOperations(s, bb))
        ensures updateOperations(s, bb).slot == s.slot;
        ensures updateOperations(s, bb).latest_block_header == s.latest_block_header;
    {
        //assert isValidProposerSlashings(s, bb);
        var s1 := updateProposerSlashings(s, bb.proposer_slashings);
        assert s1 == updateProposerSlashings(s, bb.proposer_slashings);
        //assert get_current_epoch(s1) == get_current_epoch(s);
        
        var s2 := updateAttesterSlashings(s1, bb.attester_slashings);
        assert s2 == updateAttesterSlashings(
                        updateProposerSlashings(s, bb.proposer_slashings), 
                        bb.attester_slashings);
        
        var s3 := updateAttestations(s2, bb.attestations);
        assert s3 == updateAttestations(
                        updateAttesterSlashings(
                            updateProposerSlashings(s, bb.proposer_slashings), 
                            bb.attester_slashings), 
                        bb.attestations);
        
        var s4 := updateDeposits(s3, bb.deposits);
        assert s4 == updateDeposits(
                        updateAttestations(
                            updateAttesterSlashings(
                                updateProposerSlashings(s, bb.proposer_slashings), 
                                bb.attester_slashings), 
                            bb.attestations), 
                        bb.deposits);

        var s5 := updateVoluntaryExits(s4, bb.voluntary_exits);
        assert s5 == updateVoluntaryExits(
                        updateDeposits(
                            updateAttestations(
                                updateAttesterSlashings(
                                    updateProposerSlashings(s, bb.proposer_slashings), 
                                    bb.attester_slashings), 
                                bb.attestations), 
                            bb.deposits), 
                        bb.voluntary_exits);
        
        s5
    }

    /**
     *  The functional equivalent of process_proposer_slashing.
     *  
     *  @param  s       A beacon state.
     *  @param  ps      A proposer slashing. 
     *  @returns        A new state obtained from processing a proposer slashing.        
     */
     function updateProposerSlashing(s: BeaconState, ps : ProposerSlashing) : BeaconState 
        // |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires minimumActiveValidators(s)
        requires ps.header_1.slot == ps.header_2.slot
        requires ps.header_1.proposer_index == ps.header_2.proposer_index 
        requires ps.header_1 == ps.header_2
        requires ps.header_1.proposer_index as int < |s.validators| 
        //requires is_slashable_validator(s.validators[ps.header_1.proposer_index], get_current_epoch(s));
        requires !s.validators[ps.header_1.proposer_index].slashed
        requires s.validators[ps.header_1.proposer_index].activation_epoch 
                    <= get_current_epoch(s) 
                    < s.validators[ps.header_1.proposer_index].withdrawable_epoch
        requires |s.validators| == |s.balances|

        ensures |s.validators| == |updateProposerSlashing(s, ps).validators| 
        ensures |s.balances| == |updateProposerSlashing(s, ps).balances| 
        ensures forall i :: 0 <= i < |s.validators| && i != ps.header_1.proposer_index as int 
                    ==> updateProposerSlashing(s, ps).validators[i] 
                        == s.validators[i]
        ensures updateProposerSlashing(s, ps) 
                == slash_validator(s, ps.header_1.proposer_index, get_beacon_proposer_index(s))
        ensures get_current_epoch(updateProposerSlashing(s, ps)) == get_current_epoch(s)
        ensures forall i :: 0 <= i < |s.validators| 
                    ==> updateProposerSlashing(s, ps).validators[i].activation_epoch 
                        == s.validators[i].activation_epoch
        ensures updateProposerSlashing(s, ps).slot == s.slot
        ensures updateProposerSlashing(s, ps).eth1_deposit_index == s.eth1_deposit_index
        ensures updateProposerSlashing(s, ps).latest_block_header == s.latest_block_header
        ensures minimumActiveValidators(updateProposerSlashing(s, ps))
    {
        var s' := slash_validator(s, ps.header_1.proposer_index, get_beacon_proposer_index(s));
        s'
    }

    /**
     *  The functional equivalent of processing a sequence of proposer slashings.
     *  
     *  @param  s       A beacon state.
     *  @param  ps      A sequence of proposer slashings. 
     *  @returns        A new state obtained from processing ps.        
     */
    function updateProposerSlashings(s: BeaconState, ps : seq<ProposerSlashing>) : BeaconState
        requires minimumActiveValidators(s)
        requires forall i,j :: 0 <= i < j < |ps| && i != j // indices are unique
            ==> ps[i].header_1.proposer_index != ps[j].header_1.proposer_index 
        requires forall i :: 0 <= i < |ps| ==> ps[i].header_1.slot == ps[i].header_2.slot
        requires forall i :: 0 <= i < |ps| 
                    ==> ps[i].header_1.proposer_index == ps[i].header_2.proposer_index 
        requires forall i :: 0 <= i < |ps| ==> ps[i].header_1 == ps[i].header_2
        requires forall i :: 0 <= i < |ps| ==> ps[i].header_1.proposer_index as int < |s.validators| 
        requires forall i :: 0 <= i < |ps| ==> !s.validators[ps[i].header_1.proposer_index].slashed 
        requires forall i :: 0 <= i < |ps| 
                    ==> s.validators[ps[i].header_1.proposer_index].activation_epoch 
                        <= get_current_epoch(s) 
                        < s.validators[ps[i].header_1.proposer_index].withdrawable_epoch
        requires |s.validators| == |s.balances|
        
        ensures updateProposerSlashings(s, ps).slot == s.slot
        //ensures get_current_epoch(updateProposerSlashings(s, ps)) == get_current_epoch(s)
        ensures updateProposerSlashings(s, ps).eth1_deposit_index == s.eth1_deposit_index
        ensures updateProposerSlashings(s, ps).latest_block_header == s.latest_block_header
        ensures |updateProposerSlashings(s, ps).validators| == |s.validators|
        ensures |updateProposerSlashings(s, ps).validators| == |updateProposerSlashings(s, ps).balances|
        ensures forall i :: 0 <= i < |s.validators| 
                    ==> updateProposerSlashings(s, ps).validators[i].activation_epoch 
                        == s.validators[i].activation_epoch
        ensures forall i :: 0 <= i < |s.validators| && i !in get_PS_validator_indices(ps) 
                    ==> updateProposerSlashings(s, ps).validators[i] 
                        == s.validators[i]
        ensures minimumActiveValidators(updateProposerSlashings(s, ps))

        decreases |ps|
    {
        if |ps| == 0 then s
        else
            // preconditions for updateProposerSlashings
            assert minimumActiveValidators(s);
            var ps1 := ps[..|ps|-1];
            assert forall i :: 0 <= i < |ps1| ==> ps1[i] == ps[i];
            assert forall i,j :: 0 <= i < j < |ps1| && i != j // ve indices are unique
                        ==> ps1[i].header_1.proposer_index != ps1[j].header_1.proposer_index; 
            
            assert forall i :: 0 <= i < |ps1| 
                        ==> ps1[i].header_1.slot == ps1[i].header_2.slot; 
            assert forall i :: 0 <= i < |ps1| 
                        ==> ps1[i].header_1.proposer_index == ps1[i].header_2.proposer_index ;
            assert forall i :: 0 <= i < |ps1| 
                        ==> ps1[i].header_1 == ps1[i].header_2;
            assert forall i :: 0 <= i < |ps1| 
                        ==> ps1[i].header_1.proposer_index as nat < |s.validators| ;
            assert forall i :: 0 <= i < |ps1| 
                        ==> !s.validators[ps1[i].header_1.proposer_index].slashed ;
            assert forall i :: 0 <= i < |ps1| 
                        ==> s.validators[ps1[i].header_1.proposer_index].activation_epoch 
                            <= get_current_epoch(s) 
                            < s.validators[ps1[i].header_1.proposer_index].withdrawable_epoch;

            //requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
            assert |s.validators| == |s.balances|;

            // preconditions for updateProposerSlashing
            //var s1 := updateProposerSlashings(s,ps[..|ps|-1]);
            var s1 := updateProposerSlashings(s,ps1);

            assert s1.slot == s.slot;
            
            assert s1.eth1_deposit_index == s.eth1_deposit_index;
            assert s1.latest_block_header == s.latest_block_header;

            assert minimumActiveValidators(s1);
            
            assert |s1.validators| == |s.validators|;
            assert |s1.validators| == |s1.balances|;

            assert forall i :: 0 <= i < |s.validators| 
                        ==> s1.validators[i].activation_epoch == s.validators[i].activation_epoch;
            assert forall i :: 0 <= i < |s.validators| && i !in get_PS_validator_indices(ps1) 
                        ==> s1.validators[i] == s.validators[i];

            var ps2 := ps[|ps|-1];

            assert minimumActiveValidators(s1);
            assert ps2.header_1.slot == ps2.header_2.slot;
            assert ps2.header_1.proposer_index == ps2.header_2.proposer_index ;
            assert ps2.header_1 == ps2.header_2;
            assert ps2.header_1.proposer_index as int < |s1.validators| == |s.validators|;
            
            assert ps2 !in ps1;
            PSHelperLemma1(s, s1, ps1, ps2, ps);
            assert s1.validators[ps2.header_1.proposer_index] 
                    == s.validators[ps2.header_1.proposer_index];
            assert !s1.validators[ps2.header_1.proposer_index].slashed;
            assert s1.validators[ps2.header_1.proposer_index].activation_epoch 
                    <= get_current_epoch(s1) == get_current_epoch(s) 
                    < s1.validators[ps2.header_1.proposer_index].withdrawable_epoch;
            assert |s1.validators| == |s1.balances|;

            //updateProposerSlashing(updateProposerSlashings(s,ps[..|ps|-1]), ps[|ps|-1])
            var s2 := updateProposerSlashing(s1, ps2);

            // check resulting post conditions of s2
            assert |s.validators| == |s2.validators| ;
            assert |s.balances| == |s2.balances| ;
        
            assert forall i :: 0 <= i < |s.validators| && i !in get_PS_validator_indices(ps1) 
                        ==> s1.validators[i] == s.validators[i];
            assert forall i :: 0 <= i < |s.validators| && i != ps2.header_1.proposer_index as int 
                        ==> s2.validators[i] == s1.validators[i];
            assert forall i :: 0 <= i < |s.validators| 
                        && i !in get_PS_validator_indices(ps1) 
                        && i != ps2.header_1.proposer_index as int 
                        ==> s2.validators[i] == s.validators[i];
            assert forall i :: 0 <= i < |s.validators| 
                        && i !in (get_PS_validator_indices(ps1) + [ps2.header_1.proposer_index as int]) 
                        ==> s2.validators[i] == s.validators[i];

            PSHelperLemma2(s, s2, ps1, ps2, ps);
            assert forall i :: 0 <= i < |s.validators| && i !in get_PS_validator_indices(ps) 
                        ==> s2.validators[i] == s.validators[i];
            assert forall i :: 0 <= i < |s.validators| 
                        ==> s2.validators[i].activation_epoch == s.validators[i].activation_epoch;
       
            assert s2.slot == s.slot;
            assert s2.eth1_deposit_index == s.eth1_deposit_index;
            assert s2.latest_block_header == s.latest_block_header;
            assert minimumActiveValidators(s2);

            s2
    }

    /**
     *  The functional equivalent of slashing validator[slash_index].
     *  
     *  @param  s               A beacon state.
     *  @param  slash_index     A validator index. 
     *  @returns                A new state obtained from slashing validator[slash_index].        
     */
    function updateAttesterSlashingComp(s: BeaconState, slash_index: ValidatorIndex) : BeaconState 
        requires slash_index as int < |s.validators| 
        //requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires minimumActiveValidators(s)
        requires |s.validators| == |s.balances|
        
        ensures |updateAttesterSlashingComp(s, slash_index).validators| == |s.validators| 
        ensures |updateAttesterSlashingComp(s, slash_index).validators| 
                == |updateAttesterSlashingComp(s, slash_index).balances| 
        ensures updateAttesterSlashingComp(s, slash_index).slot == s.slot
        ensures updateAttesterSlashingComp(s, slash_index).latest_block_header == s.latest_block_header
        ensures updateAttesterSlashingComp(s, slash_index).eth1_deposit_index == s.eth1_deposit_index
        // ensures 
        //     var s1 := updateAttesterSlashingComp(s, slash_index);
        //     |get_active_validator_indices(s1.validators, get_current_epoch(s1))| > 0
        ensures minimumActiveValidators(updateAttesterSlashingComp(s, slash_index))
    {
        if is_slashable_validator(s.validators[slash_index], get_current_epoch(s)) then
            //slashValidatorPreservesActiveValidators(s, slash_index, get_beacon_proposer_index(s));
            slash_validator(s, slash_index, get_beacon_proposer_index(s))
        else
            s
    }
    
    /**
     *  The functional equivalent of processing a sequence of slashings.
     *  
     *  @param  s       A beacon state.
     *  @param  indices A sequence of validator indices (as uint64) to be slashed. 
     *  @returns        A new state obtained from slashing validator[indices[i]]
     *                  for all 0 <= i < |indices|.        
     */
    function updateAttesterSlashing(s: BeaconState, indices: seq<uint64>) : BeaconState 
        //requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires minimumActiveValidators(s)
        requires |s.validators| == |s.balances|
        requires valid_state_indices(s,indices)
        //requires forall i :: 0 <= i < |indices| ==> indices[i] as int < |s.validators| 

        ensures |s.validators| == |updateAttesterSlashing(s, indices).validators| 
        ensures |updateAttesterSlashing(s, indices).validators| 
                == |updateAttesterSlashing(s, indices).balances| 
        ensures updateAttesterSlashing(s, indices).slot == s.slot
        ensures updateAttesterSlashing(s, indices).eth1_deposit_index == s.eth1_deposit_index
        ensures updateAttesterSlashing(s, indices).latest_block_header == s.latest_block_header
        //ensures 
        //    var s1 := updateAttesterSlashing(s, indices);
        //    |get_active_validator_indices(s1.validators, get_current_epoch(s1))| > 0
        ensures minimumActiveValidators(updateAttesterSlashing(s, indices))
        decreases indices
    {
        if |indices| == 0 then 
            s
        else 
            updateAttesterSlashingComp(
                updateAttesterSlashing(s, indices[..|indices|-1]), 
                indices[|indices|-1] as ValidatorIndex
            )
    }

    /**
     *  The functional equivalent of processing a sequence of attester slashings.
     *  
     *  @param  s       A beacon state.
     *  @param  a       A sequence of attester slashings. 
     *  @returns        A new state obtained from processing a.
     *                  
     *  @note           Three levels of functions are used instead of just two because the indices
     *                  for slashing need to be extracted from a before recursion can be used.
     *                  i.e. in  updateAttesterSlashings the indices are extracted, in 
     *                  updateAttesterSlashing a sequence of indices are processed, and then in 
     *                  updateAttesterSlashingComp an individual validator is slashed.
     *  @note           For consistency the top two level functions have the naming conventions 
     *                  used throughout.
     *  @note           This function does not currently show that only those validators in
     *                  the sorted intersection are slashed.
     */
    function updateAttesterSlashings(s: BeaconState, a: seq<AttesterSlashing>) : BeaconState 
        requires forall i :: 0 <= i < |a| ==> is_valid_indexed_attestation(a[i].attestation_1)
        requires forall i :: 0 <= i < |a| ==> is_valid_indexed_attestation(a[i].attestation_2)
        requires forall i :: 0 <= i < |a| 
                    ==> forall j :: 0 <= j < |a[i].attestation_1.attesting_indices|
                    ==> a[i].attestation_1.attesting_indices[j] as int < |s.validators|
        requires forall i :: 0 <= i < |a| 
                    ==> forall j :: 0 <= j < |a[i].attestation_2.attesting_indices| 
                    ==> a[i].attestation_2.attesting_indices[j] as int < |s.validators|
        //requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires minimumActiveValidators(s)
        requires |s.validators| == |s.balances|

        ensures |s.validators| == |updateAttesterSlashings(s, a).validators| 
        ensures |updateAttesterSlashings(s, a).validators| == |updateAttesterSlashings(s, a).balances| 
        ensures updateAttesterSlashings(s, a).slot == s.slot
        ensures updateAttesterSlashings(s, a).eth1_deposit_index == s.eth1_deposit_index
        ensures updateAttesterSlashings(s, a).latest_block_header == s.latest_block_header
        ensures minimumActiveValidators(updateAttesterSlashings(s, a))
    {
        if |a| == 0 then 
            s
        else  
            updateAttesterSlashing(updateAttesterSlashings(s, a[..|a|-1]), 
                                   sorted_intersection(a[|a|-1].attestation_1.attesting_indices, 
                                   a[|a|-1].attestation_2.attesting_indices)
                                  )
    }

    /**
     *  The functional equivalent of process_attestation.
     *  
     *  @param  s       A beacon state.
     *  @param  a       An pattestation. 
     *  @returns        A new state obtained from processing an attestation.        
     */
    function updateAttestation(s: BeaconState, a: Attestation) : BeaconState
        requires attestationIsWellFormed(s, a)
        requires |s.current_epoch_attestations| < MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
        requires |s.previous_epoch_attestations| < MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
        requires minimumActiveValidators(s)
        ensures minimumActiveValidators(updateAttestation(s, a))
        ensures 
            var s1 := updateAttestation(s, a);
            |s1.current_epoch_attestations| + |s1.previous_epoch_attestations| 
                == |s.current_epoch_attestations| + |s.previous_epoch_attestations| + 1
        ensures |s.current_epoch_attestations| 
                    <= |updateAttestation(s, a).current_epoch_attestations| 
                    <= |s.current_epoch_attestations| + 1
        ensures |s.previous_epoch_attestations| 
                    <=|updateAttestation(s, a).previous_epoch_attestations| 
                    <= |s.previous_epoch_attestations| + 1
        ensures 
            var s1 := updateAttestation(s, a);
            s1 == s.(current_epoch_attestations := s1.current_epoch_attestations) 
            || s1 == s.(previous_epoch_attestations := s1.previous_epoch_attestations)
        ensures updateAttestation(s, a).validators == s.validators
        ensures updateAttestation(s, a).balances == s.balances
        ensures updateAttestation(s, a).slot == s.slot
        ensures updateAttestation(s, a).latest_block_header == s.latest_block_header
        ensures updateAttestation(s, a).current_justified_checkpoint 
                == s.current_justified_checkpoint
        ensures updateAttestation(s, a).previous_justified_checkpoint 
                == s.previous_justified_checkpoint
        ensures updateAttestation(s, a).eth1_deposit_index == s.eth1_deposit_index
    {
        // data = attestation.data
        assert get_previous_epoch(s) <= a.data.target.epoch <=  get_current_epoch(s);
        assert a.data.target.epoch == compute_epoch_at_slot(a.data.slot);
        assert a.data.slot as nat + MIN_ATTESTATION_INCLUSION_DELAY as nat 
                <= s.slot as nat 
                <= a.data.slot as nat + SLOTS_PER_EPOCH as nat;
        assert a.data.index < get_committee_count_per_slot(s, a.data.target.epoch);

        var committee := get_beacon_committee(s, a.data.slot, a.data.index);
        assert |a.aggregation_bits| == |committee|;

        var pending := PendingAttestation(
            a.aggregation_bits, 
            a.data, 
            (s.slot - a.data.slot), 
            get_beacon_proposer_index(s) 
        );

        if a.data.target.epoch == get_current_epoch(s) then
            //  Add a to current attestations
            assert a.data.source == s.current_justified_checkpoint;
            s.(
                current_epoch_attestations := s.current_epoch_attestations + [pending]
            )
            // s.current_epoch_attestations.append(pending_attestation)
        
        else 
            assert a.data.source == s.previous_justified_checkpoint;
            s.(
                previous_epoch_attestations := s.previous_epoch_attestations + [pending]
            )
            // s.previous_epoch_attestations.append(pending_attestation)
            
        // # Verify signature
        // Not implemented as part of the simplificiation
        //assert is_valid_indexed_attestation(s', get_indexed_attestation(s', a));
    }

    /**
     *  The functional equivalent of processing a sequence of attestations.
     *  
     *  @param  s       A beacon state.
     *  @param  a       A sequence of attestations. 
     *  @returns        A new state obtained from processing a.        
     */
    function updateAttestations(s: BeaconState, a: seq<Attestation>) : BeaconState
        requires |s.validators| == |s.balances|
        requires |a| as nat <= MAX_ATTESTATIONS as nat
        requires forall i:: 0 <= i < |a| ==> attestationIsWellFormed(s, a[i])
        requires |s.current_epoch_attestations| as nat + |a| as nat 
                    <= MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
        requires |s.previous_epoch_attestations| as nat + |a| as nat 
                    <= MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
        requires minimumActiveValidators(s)
        
        ensures |updateAttestations(s,a).validators| == |updateAttestations(s,a).balances|
        ensures 
                var s1 := updateAttestations(s,a);
                |s1.current_epoch_attestations| + |s1.previous_epoch_attestations| 
                == |s.current_epoch_attestations| + |s.previous_epoch_attestations| + |a|
        ensures |updateAttestations(s,a).current_epoch_attestations| 
                    <= |s.current_epoch_attestations| + |a|;
        ensures |updateAttestations(s,a).previous_epoch_attestations| 
                    <= |s.previous_epoch_attestations| + |a|;
        ensures minimumActiveValidators(updateAttestations(s, a))
        ensures updateAttestations(s, a).validators == s.validators
        ensures updateAttestations(s, a).slot == s.slot
        ensures updateAttestations(s, a).latest_block_header == s.latest_block_header
        ensures updateAttestations(s, a).current_justified_checkpoint == s.current_justified_checkpoint
        ensures updateAttestations(s, a).previous_justified_checkpoint == s.previous_justified_checkpoint
        ensures updateAttestations(s, a).eth1_deposit_index == s.eth1_deposit_index
    {
        if |a| == 0 then s
        else
            var index := |a| - 1;
            var s1 := updateAttestations(s,a[..index]);

            //assert attestationIsWellFormed(s1, a[index]);
            AttestationHelperLemma(s, s1, a[index]);

            updateAttestation(s1, a[index])
    }

    /**
     *  Take into account a single deposit from a block.
     *
     *  @param  s       A beacon state.
     *  @param  d       A single deposit.
     *  @returns        The state obtained after taking account the deposit `d` from state `s` 
     */
    function updateDeposit(s: BeaconState, d: Deposit) : BeaconState 
        requires minimumActiveValidators(s)
        requires s.eth1_deposit_index as int +  1 < 0x10000000000000000 
        requires |s.validators| == |s.balances|
        requires |s.validators| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
        requires total_balances(s.balances) + d.data.amount as int < 0x10000000000000000
        
        ensures d.data.pubkey !in seqKeysInValidators(s.validators) 
                ==> updateDeposit(s,d).validators == s.validators + [get_validator_from_deposit(d)]
        ensures d.data.pubkey in seqKeysInValidators(s.validators)  
                ==> updateDeposit(s,d).validators == s.validators 
        ensures updateDeposit(s,d).eth1_deposit_index == s.eth1_deposit_index + 1
        ensures updateDeposit(s,d).slot == s.slot
        ensures updateDeposit(s,d).latest_block_header == s.latest_block_header
        ensures |updateDeposit(s,d).validators| == |updateDeposit(s,d).balances|        
        ensures |s.validators| <= |updateDeposit(s,d).validators| <= |s.validators| + 1 
        ensures |s.balances| <= |updateDeposit(s,d).balances| <= |s.balances| + 1 
        ensures forall i :: 0 <= i < |s.balances| 
                ==> s.balances[i] <= updateDeposit(s,d).balances[i]
        ensures total_balances(updateDeposit(s,d).balances) 
                == total_balances(s.balances) + d.data.amount as int 
                < 0x10000000000000000
        ensures forall i :: 0 <= i < |s.validators| 
                ==> s.validators[i] == updateDeposit(s,d).validators[i]
        ensures minimumActiveValidators(updateDeposit(s,d))
        
    {
        var pk := seqKeysInValidators(s.validators); 
        var k := d.data.pubkey;
        
        var s' := s.(
                eth1_deposit_index := (s.eth1_deposit_index as int + 1) as uint64,
                validators := if k in pk then 
                                    s.validators // unchanged validator members
                                else 
                                    validator_append(s.validators, get_validator_from_deposit(d)), 
                balances := if k in pk then 
                                individualBalanceBoundMaintained(s.balances,d);
                                updateExistingBalance(s, get_validator_index(pk, k), d.data.amount);
                                increase_balance(s,get_validator_index(pk, k),d.data.amount).balances
                            else 
                                distBalancesProp(s.balances,[d.data.amount]);
                                balance_append(s.balances, d.data.amount) 
            );
        assert forall i :: 0 <= i < |s.validators| 
                ==> s.validators[i] == s'.validators[i];
        assert minimumActiveValidators(s');
        s'
    }
    
    /**
     *  Take into account deposits in a block.
     *
     *  @param  s           A beacon state.
     *  @param  deposits    A list of deposits from a block body.
     *  @returns            The state obtained after taking account the deposits in `body` 
     *                      from state `s` 
     *
     *  @note               The processing of deposits does not use assume statements
     *                      to prevent the overflow of amounts. The strategy of assuming
     *                      that such overflow is not possible due to an upper limit on
     *                      the amount of eth is used here and could be applied in other
     *                      parts of the model where such assume statements are used.
     */
    function updateDeposits(s: BeaconState, deposits: seq<Deposit>) : BeaconState 
        requires minimumActiveValidators(s)
        requires s.eth1_deposit_index as int +  |deposits| < 0x10000000000000000 
        requires |s.validators| == |s.balances|
        requires |s.validators| + |deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        requires total_balances(s.balances) + total_deposits(deposits) < 0x10000000000000000 
        // i.e. assume that (total balances + total deposits) isless than total eth
        
        ensures updateDeposits(s, deposits).eth1_deposit_index 
                == s.eth1_deposit_index  + |deposits| as uint64 
        ensures |s.validators| 
                <= |updateDeposits(s,deposits).validators| 
                <= |s.validators| + |deposits| 
        ensures total_balances(updateDeposits(s,deposits).balances) 
                == total_balances(s.balances) + total_deposits(deposits)
        ensures get_current_epoch(updateDeposits(s, deposits)) 
                == get_current_epoch(s)
        ensures updateDeposits(s, deposits).slot == s.slot
        ensures updateDeposits(s, deposits).latest_block_header == s.latest_block_header
        ensures minimumActiveValidators(updateDeposits(s, deposits))
        
        decreases |deposits|
    {
        if |deposits| == 0 then s
        else 
            updateDeposit(updateDeposits(s,deposits[..|deposits|-1]),deposits[|deposits|-1])
    }

    /**
     *  The functional equivalent of process_voluntary_exit.
     *  
     *  @param  s       A beacon state.
     *  @param  ve      A voluntary exit. 
     *  @returns        A new state obtained from processing a voluntary exit.        
     */
    function updateVoluntaryExit(s: BeaconState, ve: VoluntaryExit) : BeaconState
        requires minimumActiveValidators(s)
        requires |s.validators| == |s.balances|
        requires ve.validator_index as int < |s.validators| 
        requires !s.validators[ve.validator_index].slashed
        requires s.validators[ve.validator_index].activation_epoch 
                <= get_current_epoch(s) 
                < s.validators[ve.validator_index].withdrawable_epoch
        requires s.validators[ve.validator_index].exitEpoch == FAR_FUTURE_EPOCH
        requires get_current_epoch(s) >= ve.epoch
        requires get_current_epoch(s) 
                >= s.validators[ve.validator_index].activation_epoch + SHARD_COMMITTEE_PERIOD 
         
        ensures updateVoluntaryExit(s, ve).slot == s.slot
        ensures updateVoluntaryExit(s, ve).latest_block_header == s.latest_block_header
        ensures |updateVoluntaryExit(s, ve).validators| == |s.validators| 
        ensures |updateVoluntaryExit(s, ve).validators| == |s.balances| 
        ensures forall i :: 0 <= i < |s.validators| && i != ve.validator_index as int 
                ==> updateVoluntaryExit(s, ve).validators[i] == s.validators[i]
        ensures updateVoluntaryExit(s, ve) == initiate_validator_exit(s, ve.validator_index)
        ensures get_current_epoch(updateVoluntaryExit(s, ve)) == get_current_epoch(s)
        ensures get_current_epoch(s) 
                >= updateVoluntaryExit(s, ve).validators[ve.validator_index].activation_epoch 
                    + SHARD_COMMITTEE_PERIOD 
        ensures forall i :: 0 <= i < |s.validators| 
                ==> updateVoluntaryExit(s, ve).validators[i].activation_epoch 
                    == s.validators[i].activation_epoch
        ensures minimumActiveValidators(updateVoluntaryExit(s, ve))
    {
        var s' := initiate_validator_exit(s, ve.validator_index);
        assert minimumActiveValidators(s');
        s'
    }
    
    /**
     *  The functional equivalent of processing a sequence of voluntary exits.
     *  
     *  @param  s       A beacon state.
     *  @param  ve      A sequence of voluntary exits. 
     *  @returns        A new state obtained from processing ve.        
     */
    function updateVoluntaryExits(s: BeaconState, ve: seq<VoluntaryExit>) : BeaconState
        requires minimumActiveValidators(s)
        requires forall i,j :: 0 <= i < j < |ve| && i != j 
                ==> ve[i].validator_index != ve[j].validator_index // ve indices are unique
        requires |s.validators| == |s.balances|
        requires forall i :: 0 <= i < |ve| ==> get_current_epoch(s) >= ve[i].epoch
        requires forall i :: 0 <= i < |ve| ==> ve[i].validator_index as int < |s.validators| 
        requires forall i :: 0 <= i < |ve| ==> !s.validators[ve[i].validator_index].slashed
        requires forall i :: 0 <= i < |ve| ==> s.validators[ve[i].validator_index].activation_epoch 
                                                <= get_current_epoch(s) 
                                                < s.validators[ve[i].validator_index].withdrawable_epoch
        requires forall i :: 0 <= i < |ve| 
                ==> s.validators[ve[i].validator_index].exitEpoch == FAR_FUTURE_EPOCH
        requires forall i :: 0 <= i < |ve| 
                ==> s.validators[ve[i].validator_index].activation_epoch as nat + SHARD_COMMITTEE_PERIOD as nat 
                    <= get_current_epoch(s) as nat < 0x10000000000000000 
   
        ensures |updateVoluntaryExits(s, ve).validators| == |s.validators|
        ensures |updateVoluntaryExits(s, ve).validators| == |updateVoluntaryExits(s, ve).balances|
        ensures updateVoluntaryExits(s, ve).slot == s.slot
        ensures updateVoluntaryExits(s, ve).latest_block_header == s.latest_block_header
        ensures get_current_epoch(updateVoluntaryExits(s, ve)) == get_current_epoch(s)
        ensures forall i :: 0 <= i < |s.validators| 
                ==> updateVoluntaryExits(s, ve).validators[i].activation_epoch == s.validators[i].activation_epoch
        ensures forall i :: 0 <= i < |s.validators| && i !in get_VolExit_validator_indices(ve) 
                ==> updateVoluntaryExits(s, ve).validators[i] == s.validators[i]
        ensures minimumActiveValidators(updateVoluntaryExits(s, ve))
        
        decreases |ve|
    {
        if |ve| == 0 then 
            s
        else
            var s1 := updateVoluntaryExits(s,ve[..|ve|-1]);

            assert ve[|ve|-1] !in ve[..|ve|-1] ;
            assert minimumActiveValidators(s1);
            assert |s1.validators| == |s1.balances| == |s.validators|;
            assert ve[|ve|-1].validator_index as int < |s.validators|; 
            
            VEHelperLemma1(s, s1,  ve[..|ve|-1], ve[|ve|-1], ve);
            assert s1.validators[ve[|ve|-1].validator_index] == s.validators[ve[|ve|-1].validator_index];
            assert !s1.validators[ve[|ve|-1].validator_index].slashed;
            assert s1.validators[ve[|ve|-1].validator_index].activation_epoch 
                    <= get_current_epoch(s) 
                    < s1.validators[ve[|ve|-1].validator_index].withdrawable_epoch;
            assert s1.validators[ve[|ve|-1].validator_index].exitEpoch == FAR_FUTURE_EPOCH;
            assert get_current_epoch(s) >= ve[|ve|-1].epoch;
            assert get_current_epoch(s) 
                    >= s1.validators[ve[|ve|-1].validator_index].activation_epoch + SHARD_COMMITTEE_PERIOD ;

            var s2 := updateVoluntaryExit(s1, ve[|ve|-1]);

            assert |s2.validators| == |s.validators|;
            assert |s2.validators| == |s2.balances|;
            assert s2.slot == s.slot;
            assert get_current_epoch(s2) == get_current_epoch(s);
            assert forall i :: 0 <= i < |s.validators| 
                ==> s2.validators[i].activation_epoch == s.validators[i].activation_epoch;
            
            VEHelperLemma2(s, s2,  ve[..|ve|-1], ve[|ve|-1], ve);
            assert forall i :: 0 <= i < |s.validators| && i !in get_VolExit_validator_indices(ve) 
                ==> s2.validators[i] == s.validators[i];
            assert minimumActiveValidators(s2);

            s2

    }
    
}