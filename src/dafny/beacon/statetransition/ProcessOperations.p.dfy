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
include "ProcessOperations.dfy"

/**
 *  Proofs for process operations
 */
module ProcessOperationsProofs {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NativeTypes
    import opened Eth2Types
    import opened Constants
    import opened BeaconChainTypes
    import opened Validators
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened BeaconHelpers
    import opened MathHelpers
    import ProcessOperations

    
    // Helper lemmas

    lemma helperIndicesLemma(indices: seq<ValidatorIndex>)
        requires |indices| > 0
        ensures forall i :: 0 < i < |indices| ==> indices[..i+1] == indices[..i] + [indices[i]]
    {
        // Thanks Dafny
    }

    lemma helperIndicesLemma2(indices: seq<ValidatorIndex>)
        requires |indices| > 0
        ensures indices == indices[..|indices|-1] + [indices[|indices|-1]]
    {
        // Thanks Dafny
    }

    lemma helperIndicesLemma3(indices: seq<uint64>, i: nat)
        requires 0 <= i < |indices|
        ensures indices[..i+1] == indices[..i] + [indices[i]]
    {
        // Thanks Dafny
    }

    lemma helperIndicesLemma4(s: BeaconState, indices: seq<uint64>, i: nat)
        requires 0 <= i <= |indices|
        requires valid_state_indices(s, indices)
        ensures valid_state_indices(s, indices[..i])
    {
        // Thanks Dafny
    }

    lemma helperIndicesLemma5(indices: seq<uint64>, i: nat)
        requires i <= |indices|
        ensures |indices[..i]| == i;
    {
        // Thanks Dafny
    }

    lemma helperIndicesLemma6(indices: seq<uint64>, i: nat)
        requires i == |indices|
        ensures indices[..i] == indices
    {
        // Thanks Dafny
    }

    lemma helperIndicesLemma7(indices: seq<uint64>, i: nat)
        requires i < |indices|
        ensures indices[..i+1] == indices[..i] + [indices[i]];
    {
        // Thanks Dafny
    }



///////////////////////////
    lemma mappingPSIndices(ps: seq<ProposerSlashing>)
        ensures forall i :: 0 <= i < |ps| ==> get_PS_validator_indices(ps)[i] == ps[i].header_1.proposer_index as int
    {
        //Thanks Dafny
    }

    lemma subsetMappingPSIndices(ps: seq<ProposerSlashing>, i : nat)
        requires 0 <= i < |ps|
        ensures get_PS_validator_indices(ps[..i]) == get_PS_validator_indices(ps)[..i]
    {
        if |ps| == 0 {}
        else {
            assert ps == ps[..i] + ps[i..];
            
            mappingPSIndices(ps[..i]);
            assert forall j :: 0 <= j < |ps[..i]| ==> get_PS_validator_indices(ps[..i])[j] == ps[j].header_1.proposer_index as int;

            mappingPSIndices(ps);
            assert forall j :: 0 <= j < |ps| ==> get_PS_validator_indices(ps)[j] == ps[j].header_1.proposer_index as int;
        }
    }

    lemma helperPSLemma(s: BeaconState, ps: ProposerSlashing)
        requires ps.header_1.slot == ps.header_2.slot
        requires ps.header_1.proposer_index == ps.header_2.proposer_index 
        requires ps.header_1 == ps.header_2
        requires ps.header_1.proposer_index as int < |s.validators| 

        // requires is_active_validator: (!v.slashed) && (v.activation_epoch <= epoch < v.withdrawable_epoch)
        requires !s.validators[ps.header_1.proposer_index].slashed
        requires s.validators[ps.header_1.proposer_index].activation_epoch <= get_current_epoch(s) < s.validators[ps.header_1.proposer_index].withdrawable_epoch
 
        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires |s.validators| == |s.balances|
        
        ensures forall i :: 0 <= i < |s.validators| && i != ps.header_1.proposer_index as int ==> updateProposerSlashing(s, ps).validators[i].exitEpoch == s.validators[i].exitEpoch
        ensures forall i :: 0 <= i < |s.validators| && i != ps.header_1.proposer_index as int ==> updateProposerSlashing(s, ps).validators[i].slashed == s.validators[i].slashed
        ensures forall i :: 0 <= i < |s.validators| && i != ps.header_1.proposer_index as int ==> updateProposerSlashing(s, ps).validators[i].withdrawable_epoch == s.validators[i].withdrawable_epoch
    {
        // Thanks Dafny
    }

    lemma helperPSLemma2(s: BeaconState, ps: seq<ProposerSlashing>)
        requires  |get_PS_validator_indices(ps)| > 0
        requires forall i :: i in get_PS_validator_indices(ps) ==> 0 <= i < |s.validators| 
        requires forall i :: i in get_PS_validator_indices(ps) ==> !s.validators[i].slashed
        requires forall i :: i in get_PS_validator_indices(ps) ==> s.validators[i].activation_epoch <= get_current_epoch(s) < s.validators[i].withdrawable_epoch
        

        ensures forall i :: i in get_PS_validator_indices(ps[..|ps|-1]) ==> 0 <= i < |s.validators|
        ensures forall i :: i in get_PS_validator_indices(ps[..|ps|-1]) ==> !s.validators[i].slashed
        ensures forall i :: i in get_PS_validator_indices(ps[..|ps|-1]) ==> s.validators[i].activation_epoch <= get_current_epoch(s) < s.validators[i].withdrawable_epoch
    {
        mappingPSIndices(ps);
        assert forall i :: 0 <= i < |ps| ==> get_PS_validator_indices(ps)[i] == ps[i].header_1.proposer_index as int;

        subsetMappingPSIndices(ps, |ps|-1);
        assert get_PS_validator_indices(ps[..|ps|-1]) == get_PS_validator_indices(ps)[..|ps|-1];
        
        assert forall i :: i in get_PS_validator_indices(ps) ==> 0 <= i < |s.validators|; // from requires
        assert forall i :: 0 <= i < |ps| ==> get_PS_validator_indices(ps)[i] == ps[i].header_1.proposer_index as int;
        assert forall i :: 0 <= i < |ps| ==> ps[i].header_1.proposer_index as int in get_PS_validator_indices(ps) ;
        
    }


    lemma updateProposerSlashingLemma(s: BeaconState, ps : ProposerSlashing)
        requires ps.header_1.slot == ps.header_2.slot
        requires ps.header_1.proposer_index == ps.header_2.proposer_index 
        requires ps.header_1 == ps.header_2
        requires ps.header_1.proposer_index as int < |s.validators| 
        //requires is_slashable_validator(s.validators[ps.header_1.proposer_index], get_current_epoch(s));
        //(!v.slashed) && (v.activation_epoch <= epoch < v.withdrawable_epoch)
        requires !s.validators[ps.header_1.proposer_index].slashed
        requires s.validators[ps.header_1.proposer_index].activation_epoch <= get_current_epoch(s) < s.validators[ps.header_1.proposer_index].withdrawable_epoch
        
        requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires |s.validators| == |s.balances|
        
        ensures |get_active_validator_indices(updateProposerSlashing(s, ps).validators, get_current_epoch(s))| > 0
    {
        var index := ps.header_1.proposer_index; // validator to be slashed
        var slashable_validator := s.validators[index];
        var epoch : Epoch := get_current_epoch(s);

        assert updateProposerSlashing(s, ps) == slash_validator(s, ps.header_1.proposer_index, get_beacon_proposer_index(s));
        slashValidatorPreservesActivateValidators(s, ps.header_1.proposer_index, get_beacon_proposer_index(s));
        assert |get_active_validator_indices(updateProposerSlashing(s, ps).validators, get_current_epoch(s))| > 0;

    }

    lemma helperPSLemma3(s: BeaconState, ps : seq<ProposerSlashing>)
        requires forall i :: 0 <= i < |ps| ==> ps[i].header_1.proposer_index as int < |s.validators| 
        requires forall i :: 0 <= i < |ps| ==> !s.validators[ps[i].header_1.proposer_index].slashed 
        requires forall i :: 0 <= i < |ps| ==> s.validators[ps[i].header_1.proposer_index].activation_epoch <= get_current_epoch(s) < s.validators[ps[i].header_1.proposer_index].withdrawable_epoch

        ensures forall i :: i in get_PS_validator_indices(ps) ==> 0 <= i < |s.validators|
        ensures forall i :: i in get_PS_validator_indices(ps) ==> !s.validators[i].slashed
        ensures forall i :: i in get_PS_validator_indices(ps) ==> s.validators[i].activation_epoch <= get_current_epoch(s) < s.validators[i].withdrawable_epoch
    {
        // Thanks Dafny
    }

    lemma helperPSLemma4(ps : seq<ProposerSlashing>)
        requires |ps| > 0
        requires forall i,j :: 0 <= i < j < |ps| && i != j ==> ps[i].header_1.proposer_index!= ps[j].header_1.proposer_index // ve indices are unique
        ensures ps[|ps|-1].header_1.proposer_index as int !in get_PS_validator_indices(ps[..|ps|-1])
    {
        mappingPSIndices(ps[..|ps|-1]);
        assert forall i :: 0 <= i < |ps[..|ps|-1]| ==> get_PS_validator_indices(ps[..|ps|-1])[i] == ps[i].header_1.proposer_index as int;
    }

    lemma helperPSLemma5(s: BeaconState, ps : seq<ProposerSlashing>)
        requires |ps| > 0
        requires forall i,j :: 0 <= i < j < |ps| && i != j ==> ps[i].header_1.proposer_index!= ps[j].header_1.proposer_index // ve indices are unique
        requires forall i :: 0 <= i < |ps| ==> ps[i].header_1.slot == ps[i].header_2.slot
        requires forall i :: 0 <= i < |ps| ==> ps[i].header_1.proposer_index == ps[i].header_2.proposer_index 
        requires forall i :: 0 <= i < |ps| ==> ps[i].header_1 == ps[i].header_2
        requires forall i :: 0 <= i < |ps| ==> ps[i].header_1.proposer_index as int < |s.validators| 
        requires forall i :: 0 <= i < |ps| ==> !s.validators[ps[i].header_1.proposer_index].slashed 
        requires forall i :: 0 <= i < |ps| ==> s.validators[ps[i].header_1.proposer_index].activation_epoch <= get_current_epoch(s) < s.validators[ps[i].header_1.proposer_index].withdrawable_epoch

        ensures forall i,j :: 0 <= i < j < |ps[..|ps|-1]| && i != j ==> ps[i].header_1.proposer_index!= ps[j].header_1.proposer_index
        ensures forall i :: 0 <= i < |ps[..|ps|-1]| ==> ps[i].header_1.slot == ps[i].header_2.slot;
        ensures forall i :: 0 <= i < |ps[..|ps|-1]| ==> ps[i].header_1.proposer_index == ps[i].header_2.proposer_index ;
        ensures forall i :: 0 <= i < |ps[..|ps|-1]| ==> ps[i].header_1 == ps[i].header_2;
        ensures forall i :: 0 <= i < |ps[..|ps|-1]| ==> ps[i].header_1.proposer_index as int < |s.validators| ;
        ensures forall i :: 0 <= i < |ps[..|ps|-1]| ==> !s.validators[ps[i].header_1.proposer_index].slashed ;
        ensures forall i :: 0 <= i < |ps[..|ps|-1]| ==> s.validators[ps[i].header_1.proposer_index].activation_epoch <= get_current_epoch(s) < s.validators[ps[i].header_1.proposer_index].withdrawable_epoch;
           
    {
    }

    lemma helperPSLemma6(ps : seq<ProposerSlashing>)
        requires |ps| > 0
        ensures get_PS_validator_indices(ps[..|ps|-1]) + [ps[|ps|-1].header_1.proposer_index as int] == get_PS_validator_indices(ps)
        ensures forall i : int :: i !in get_PS_validator_indices(ps[..|ps|-1]) && i != ps[|ps|-1].header_1.proposer_index as int ==>
                i !in get_PS_validator_indices(ps)
    {
        mappingPSIndices(ps);
        subsetMappingPSIndices(ps, |ps|-1);
    }


    ///////////////

    lemma AttestationHelperLemma(s: BeaconState, s1: BeaconState, a: Attestation)
        requires attestationIsWellFormed(s, a);
        requires s1.validators == s.validators
        requires s1.slot == s.slot
        requires s1.current_justified_checkpoint == s.current_justified_checkpoint
        requires s1.previous_justified_checkpoint == s.previous_justified_checkpoint
        ensures attestationIsWellFormed(s1, a);
    { // Thanks Dafny
    }

    //////////////////

    lemma VolExitLemma1(s: BeaconState, voluntary_exit: VoluntaryExit)
        requires |s.validators| == |s.balances|
        requires voluntary_exit.validator_index as int < |s.validators| 
        requires minimumActiveValidators(s)
        
        requires !s.validators[voluntary_exit.validator_index].slashed
        requires s.validators[voluntary_exit.validator_index].activation_epoch <= get_current_epoch(s) < s.validators[voluntary_exit.validator_index].withdrawable_epoch

        requires s.validators[voluntary_exit.validator_index].exitEpoch == FAR_FUTURE_EPOCH
        requires get_current_epoch(s) >= voluntary_exit.epoch
        requires get_current_epoch(s) >= s.validators[voluntary_exit.validator_index].activation_epoch + SHARD_COMMITTEE_PERIOD 

        ensures minimumActiveValidators(updateVoluntaryExit(s, voluntary_exit))
    {
        // var s1 := updateVoluntaryExit(s, voluntary_exit);
        // assert get_current_epoch(s) == get_current_epoch(s1);
        // assert exists v :: 0 <= v < |s.validators| && s.validators[v].activation_epoch <= get_current_epoch(s) < s.validators[v].exitEpoch;
        // assert forall v :: 0 <= v < |s.validators| ==> s.validators[v].activation_epoch <= get_current_epoch(s) < s.validators[v].exitEpoch
        //                                             ==> s1.validators[v].activation_epoch <= get_current_epoch(s1) < s1.validators[v].exitEpoch;
        // assert exists v :: 0 <= v < |s1.validators| && s1.validators[v].activation_epoch <= get_current_epoch(s1) < s1.validators[v].exitEpoch;
        // assert exists v :: 0 <= v < |s1.validators| && is_active_validator(s1.validators[v], get_current_epoch(s1));
        // assert |get_active_validator_indices(s1.validators, get_current_epoch(s1))| > 0 ==> 
        //     (exists v :: 0 <= v < |s1.validators| && is_active_validator(s1.validators[v], get_current_epoch(s1)));
        // assert  minimumActiveValidators(s1);
    }


    lemma helperVoluntaryExitLemma3(s: BeaconState, ve: seq<VoluntaryExit>)
        requires forall i :: 0 <= i < |ve| ==> ve[i].validator_index as int < |s.validators| 
        //requires forall i :: 0 <= i < |ve| ==> is_active_validator(s.validators[ve[i].validator_index], get_current_epoch(s))
        requires forall i :: 0 <= i < |ve| ==> !s.validators[ve[i].validator_index].slashed
        requires forall i :: 0 <= i < |ve| ==> s.validators[ve[i].validator_index].activation_epoch <= get_current_epoch(s) < s.validators[ve[i].validator_index].withdrawable_epoch

        requires forall i :: 0 <= i < |ve| ==> s.validators[ve[i].validator_index].exitEpoch == FAR_FUTURE_EPOCH
        requires forall i :: 0 <= i < |ve| ==> get_current_epoch(s) >= s.validators[ve[i].validator_index].activation_epoch + SHARD_COMMITTEE_PERIOD 

        ensures forall i :: i in get_VolExit_validator_indices(ve) ==> 0 <= i < |s.validators| 
        
        //ensures forall i :: i in get_VolExit_validator_indices(ve) ==> is_active_validator(s.validators[i], get_current_epoch(s))
        ensures forall i :: i in get_VolExit_validator_indices(ve) ==> !s.validators[i].slashed
        ensures forall i :: i in get_VolExit_validator_indices(ve) ==> s.validators[i].activation_epoch <= get_current_epoch(s) < s.validators[i].withdrawable_epoch

        ensures forall i :: i in get_VolExit_validator_indices(ve) ==> s.validators[i].exitEpoch == FAR_FUTURE_EPOCH
        ensures forall i :: i in get_VolExit_validator_indices(ve) ==> get_current_epoch(s) >= s.validators[i].activation_epoch + SHARD_COMMITTEE_PERIOD 
    {
        // Thanks Dafny
    }

    lemma helperVoluntaryExitLemma2(s: BeaconState, ve: seq<VoluntaryExit>)
        requires  |get_VolExit_validator_indices(ve)| > 0
        requires forall i :: i in get_VolExit_validator_indices(ve) ==> 0 <= i < |s.validators| 
        requires forall i :: i in get_VolExit_validator_indices(ve) ==> !s.validators[i].slashed
        requires forall i :: i in get_VolExit_validator_indices(ve) ==> s.validators[i].activation_epoch <= get_current_epoch(s) < s.validators[i].withdrawable_epoch
        requires forall i :: i in get_VolExit_validator_indices(ve) ==> s.validators[i].exitEpoch == FAR_FUTURE_EPOCH
        requires forall i :: i in get_VolExit_validator_indices(ve) ==> get_current_epoch(s) >= s.validators[i].activation_epoch + SHARD_COMMITTEE_PERIOD 
    

        ensures forall i :: i in get_VolExit_validator_indices(ve[..|ve|-1]) ==> 0 <= i < |s.validators|
        ensures forall i :: i in get_VolExit_validator_indices(ve[..|ve|-1]) ==> !s.validators[i].slashed
        ensures forall i :: i in get_VolExit_validator_indices(ve[..|ve|-1]) ==> s.validators[i].activation_epoch <= get_current_epoch(s) < s.validators[i].withdrawable_epoch
        ensures forall i :: i in get_VolExit_validator_indices(ve[..|ve|-1]) ==> s.validators[i].exitEpoch == FAR_FUTURE_EPOCH
        ensures forall i :: i in get_VolExit_validator_indices(ve[..|ve|-1]) ==> get_current_epoch(s) >= s.validators[i].activation_epoch + SHARD_COMMITTEE_PERIOD
    {
        mappingVolExitIndices(ve);
        assert forall i :: 0 <= i < |ve| ==> get_VolExit_validator_indices(ve)[i] == ve[i].validator_index as int;

        subsetMappingVolExitIndices(ve, |ve|-1);
        assert get_VolExit_validator_indices(ve[..|ve|-1]) == get_VolExit_validator_indices(ve)[..|ve|-1];
        
        assert forall i :: i in get_VolExit_validator_indices(ve) ==> 0 <= i < |s.validators|; // from requires
        assert forall i :: 0 <= i < |ve| ==> get_VolExit_validator_indices(ve)[i] == ve[i].validator_index as int;
        assert forall i :: 0 <= i < |ve| ==> ve[i].validator_index as int in get_VolExit_validator_indices(ve) ;
        
    }

    lemma helperVoluntaryExitLemma(s: BeaconState, exit: VoluntaryExit)
        requires |s.validators| == |s.balances|
        requires exit.validator_index as int < |s.validators| 
        // requires is_active_validator(s.validators[voluntary_exit.validator_index], get_current_epoch(s))
        // (!v.slashed) && (v.activation_epoch <= epoch < v.withdrawable_epoch)
        requires !s.validators[exit.validator_index].slashed
        requires s.validators[exit.validator_index].activation_epoch <= get_current_epoch(s) < s.validators[exit.validator_index].withdrawable_epoch

        requires s.validators[exit.validator_index].exitEpoch == FAR_FUTURE_EPOCH
        requires get_current_epoch(s) >= exit.epoch
        requires get_current_epoch(s) >= s.validators[exit.validator_index].activation_epoch + SHARD_COMMITTEE_PERIOD 
        
        ensures forall i :: 0 <= i < |s.validators| && i != exit.validator_index as int ==> updateVoluntaryExit(s, exit).validators[i].exitEpoch == s.validators[i].exitEpoch
        ensures forall i :: 0 <= i < |s.validators| && i != exit.validator_index as int ==> updateVoluntaryExit(s, exit).validators[i].slashed == s.validators[i].slashed
        ensures forall i :: 0 <= i < |s.validators| && i != exit.validator_index as int ==> updateVoluntaryExit(s, exit).validators[i].withdrawable_epoch == s.validators[i].withdrawable_epoch
    {
        // Thanks Dafny
    }

    lemma mappingVolExitIndices(ve: seq<VoluntaryExit>)
        ensures forall i :: 0 <= i < |ve| ==> get_VolExit_validator_indices(ve)[i] == ve[i].validator_index as int
    {
        //Thanks Dafny
    }

    lemma subsetMappingVolExitIndices(ve: seq<VoluntaryExit>, i : nat)
        requires 0 <= i < |ve|
        ensures get_VolExit_validator_indices(ve[..i]) == get_VolExit_validator_indices(ve)[..i]
    {
        if |ve| == 0 {}
        else {
            assert ve == ve[..i] + ve[i..];
            
            mappingVolExitIndices(ve[..i]);
            assert forall j :: 0 <= j < |ve[..i]| ==> get_VolExit_validator_indices(ve[..i])[j] == ve[j].validator_index as int;

            mappingVolExitIndices(ve);
            assert forall j :: 0 <= j < |ve| ==> get_VolExit_validator_indices(ve)[j] == ve[j].validator_index as int;
        }
    }

    //lemma PSpreconditionLemma()
    lemma helperVolExitLemma4(ve : seq<VoluntaryExit>)
        requires |ve| > 0
        requires forall i,j :: 0 <= i < j < |ve| && i != j ==> ve[i].validator_index!= ve[j].validator_index // ve indices are unique
        ensures ve[|ve|-1].validator_index as int !in get_VolExit_validator_indices(ve[..|ve|-1])
    {
        mappingVolExitIndices(ve[..|ve|-1]);
        assert forall i :: 0 <= i < |ve[..|ve|-1]| ==> get_VolExit_validator_indices(ve[..|ve|-1])[i] == ve[i].validator_index as int;
    }

    

}