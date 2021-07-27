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
include "../../utils/SeqHelpers.dfy"
include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../validators/Validators.dfy"
include "../validators/ValidatorHelpers.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../Helpers.dfy"
include "../Helpers.s.dfy"

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
    import opened ValidatorHelpers
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened BeaconHelpers
    import opened BeaconHelperSpec
    import opened MathHelpers
    import opened SeqHelpers
 
    
    // Helper lemmas

    // lemma helperIndicesLemma(indices: seq<ValidatorIndex>)
    //     requires |indices| > 0
    //     ensures forall i :: 0 < i < |indices| ==> indices[..i+1] == indices[..i] + [indices[i]]
    // {
    //     // Thanks Dafny
    // }

    // lemma helperIndicesLemma2(indices: seq<ValidatorIndex>)
    //     requires |indices| > 0
    //     ensures indices == indices[..|indices|-1] + [indices[|indices|-1]]
    // {
    //     // Thanks Dafny
    // }

    // lemma helperIndicesLemma3(indices: seq<uint64>, i: nat)
    //     requires 0 <= i < |indices|
    //     ensures indices[..i+1] == indices[..i] + [indices[i]]
    // {
    //     // Thanks Dafny
    // }

    // lemma helperIndicesLemma4(s: BeaconState, indices: seq<uint64>, i: nat)
    //     requires 0 <= i <= |indices|
    //     requires valid_state_indices(s, indices)
    //     ensures valid_state_indices(s, indices[..i])
    // {
    //     // Thanks Dafny
    // }

    // lemma helperIndicesLemma5(indices: seq<uint64>, i: nat)
    //     requires i <= |indices|
    //     ensures |indices[..i]| == i;
    // {
    //     // Thanks Dafny
    // }

    // lemma helperIndicesLemma6(indices: seq<uint64>, i: nat)
    //     requires i == |indices|
    //     ensures indices[..i] == indices
    // {
    //     // Thanks Dafny
    // }

    // lemma helperIndicesLemma7(indices: seq<uint64>, i: nat)
    //     requires i < |indices|
    //     ensures indices[..i+1] == indices[..i] + [indices[i]];
    // {
    //     // Thanks Dafny
    // }

/////////////////////

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

    lemma PSHelperLemma1(s: BeaconState, s1: BeaconState, ps1: seq<ProposerSlashing>, ps2: ProposerSlashing, ps: seq<ProposerSlashing>)
        requires |ps1| == |ps|-1
        requires ps1 == ps[..|ps|-1]
        requires ps2 == ps[|ps|-1]

        //requires ps1 + [ps2] == ps
        requires forall i,j :: 0 <= i < j < |ps| && i != j ==> ps[i].header_1.proposer_index!= ps[j].header_1.proposer_index 
        requires forall i :: 0 <= i < |ps1| ==> ps1[i].header_1.proposer_index as int < |s.validators| 
        requires ps2.header_1.proposer_index as int < |s.validators| 
        requires |s1.validators| == |s.validators|

        requires forall i :: 0 <= i < |s.validators| && i !in get_PS_validator_indices(ps1) ==> s1.validators[i] == s.validators[i]
        requires ps2 !in ps1

        ensures s1.validators[ps2.header_1.proposer_index] == s.validators[ps2.header_1.proposer_index]
    {
        seqInitLast<ProposerSlashing>(ps, |ps|-1);
        assert ps[..|ps|-1] + [ps[|ps|-1]] == ps[..|ps|];
        assert ps[..|ps|] == ps;
        assert ps1 + [ps2] == ps;
        
        mappingPSIndices(ps1);
        assert forall i :: 0 <= i < |ps1| ==> get_PS_validator_indices(ps1)[i] == ps1[i].header_1.proposer_index as int;
        assert forall i :: 0 <= i < |ps[..|ps|-1]|  ==> ps[i].header_1.proposer_index != ps[|ps|-1].header_1.proposer_index ;
        assert ps2.header_1.proposer_index as int !in get_PS_validator_indices(ps1);
    }

    lemma PSHelperLemma2(s: BeaconState, s2: BeaconState, ps1: seq<ProposerSlashing>, ps2: ProposerSlashing, ps: seq<ProposerSlashing>)
        requires |ps1| == |ps|-1
        requires ps1 == ps[..|ps|-1]
        requires ps2 == ps[|ps|-1]

        requires forall i,j :: 0 <= i < j < |ps| && i != j ==> ps[i].header_1.proposer_index!= ps[j].header_1.proposer_index 
        requires forall i :: 0 <= i < |ps1| ==> ps1[i].header_1.proposer_index as int < |s.validators| 
        requires ps2.header_1.proposer_index as int < |s.validators| 
        requires |s2.validators| == |s.validators|

        requires forall i :: 0 <= i < |s.validators| && i !in (get_PS_validator_indices(ps1) + [ps2.header_1.proposer_index as int]) 
                ==> s2.validators[i] == s.validators[i]
        
        ensures forall i :: 0 <= i < |s.validators| && i !in get_PS_validator_indices(ps) ==> s2.validators[i] == s.validators[i]
    {
        seqInitLast<ProposerSlashing>(ps, |ps|-1);
        assert ps[..|ps|-1] + [ps[|ps|-1]] == ps[..|ps|];
        assert ps[..|ps|] == ps;
        assert ps1 + [ps2] == ps; 

        subsetMappingPSIndices(ps,|ps|-1);
        assert ps1 == ps[..|ps|-1];
        assert get_PS_validator_indices(ps[..|ps|-1]) == get_PS_validator_indices(ps1) == get_PS_validator_indices(ps)[..|ps|-1];

        ////////
        mappingPSIndices(ps);
        assert forall i :: 0 <= i < |ps| ==> get_PS_validator_indices(ps)[i] == ps[i].header_1.proposer_index as int;
        assert get_PS_validator_indices(ps)[|ps|-1] == ps[|ps|-1].header_1.proposer_index as int == ps2.header_1.proposer_index as int;

        assert get_PS_validator_indices(ps)[..|ps|-1] + [get_PS_validator_indices(ps)[|ps|-1]] == get_PS_validator_indices(ps);
    
        assert get_PS_validator_indices(ps1) + [ps2.header_1.proposer_index as int] == get_PS_validator_indices(ps);

    }

    lemma PSHelperLemma3(ps : seq<ProposerSlashing>)
        requires |ps| > 0
        requires forall i,j :: 0 <= i < j < |ps| && i != j ==> ps[i].header_1.proposer_index!= ps[j].header_1.proposer_index // ve indices are unique
        ensures ps[|ps|-1].header_1.proposer_index as int !in get_PS_validator_indices(ps[..|ps|-1])
    {
        mappingPSIndices(ps[..|ps|-1]);
        assert forall i :: 0 <= i < |ps[..|ps|-1]| ==> get_PS_validator_indices(ps[..|ps|-1])[i] == ps[i].header_1.proposer_index as int;
    }




    lemma VEHelperLemma1(s: BeaconState, s1: BeaconState, ve1: seq<VoluntaryExit>, ve2: VoluntaryExit, ve: seq<VoluntaryExit>)
        requires |ve1| == |ve|-1
        requires ve1 == ve[..|ve|-1]
        requires ve2 == ve[|ve|-1]

        //requires ve1 + [ve2] == ve
        requires forall i,j :: 0 <= i < j < |ve| && i != j ==> ve[i].validator_index!= ve[j].validator_index 
        requires forall i :: 0 <= i < |ve1| ==> ve1[i].validator_index as int < |s.validators| 
        requires ve2.validator_index as int < |s.validators| 
        requires |s1.validators| == |s.validators|

        requires forall i :: 0 <= i < |s.validators| && i !in get_VolExit_validator_indices(ve1) ==> s1.validators[i] == s.validators[i]
        requires ve2 !in ve1

        ensures s1.validators[ve2.validator_index] == s.validators[ve2.validator_index]
    {
        seqInitLast<VoluntaryExit>(ve, |ve|-1);
        assert ve[..|ve|-1] + [ve[|ve|-1]] == ve[..|ve|];
        assert ve[..|ve|] == ve;
        assert ve1 + [ve2] == ve;
        
        mappingVolExitIndices(ve1);
        assert forall i :: 0 <= i < |ve1| ==> get_VolExit_validator_indices(ve1)[i] == ve1[i].validator_index as int;
        assert forall i :: 0 <= i < |ve[..|ve|-1]|  ==> ve[i].validator_index != ve[|ve|-1].validator_index ;
        assert ve2.validator_index as int !in get_VolExit_validator_indices(ve1);
    }

    lemma VEHelperLemma2(s: BeaconState, s1: BeaconState, ve1: seq<VoluntaryExit>, ve2: VoluntaryExit, ve: seq<VoluntaryExit>)
        requires |ve1| == |ve|-1
        requires ve1 == ve[..|ve|-1]
        requires ve2 == ve[|ve|-1]

        //requires ve1 + [ve2] == ve
        requires forall i,j :: 0 <= i < j < |ve| && i != j ==> ve[i].validator_index!= ve[j].validator_index 
        requires forall i :: 0 <= i < |ve1| ==> ve1[i].validator_index as int < |s.validators| 
        requires ve2.validator_index as int < |s.validators| 
        requires |s1.validators| == |s.validators|

        requires forall i :: 0 <= i < |s.validators| && i !in (get_VolExit_validator_indices(ve1) + [ve2.validator_index as int]) 
                ==> s1.validators[i] == s.validators[i]
        
        ensures forall i :: 0 <= i < |s.validators| && i !in get_VolExit_validator_indices(ve) ==> s1.validators[i] == s.validators[i]
    {
        seqInitLast<VoluntaryExit>(ve, |ve|-1);
        assert ve[..|ve|-1] + [ve[|ve|-1]] == ve[..|ve|];
        assert ve[..|ve|] == ve;
        assert ve1 + [ve2] == ve;
        
        subsetMappingVolExitIndices(ve,|ve|-1);
        assert ve1 == ve[..|ve|-1];
        assert get_VolExit_validator_indices(ve[..|ve|-1]) == get_VolExit_validator_indices(ve1) == get_VolExit_validator_indices(ve)[..|ve|-1];

        ////////
        mappingVolExitIndices(ve);
        assert forall i :: 0 <= i < |ve| ==> get_VolExit_validator_indices(ve)[i] == ve[i].validator_index as int;
        assert get_VolExit_validator_indices(ve)[|ve|-1] == ve[|ve|-1].validator_index as int == ve2.validator_index as int;

        assert get_VolExit_validator_indices(ve)[..|ve|-1] + [get_VolExit_validator_indices(ve)[|ve|-1]] == get_VolExit_validator_indices(ve);
    
        assert get_VolExit_validator_indices(ve1) + [ve2.validator_index as int] == get_VolExit_validator_indices(ve);

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
    lemma VEHelperLemma3(ve : seq<VoluntaryExit>)
        requires |ve| > 0
        requires forall i,j :: 0 <= i < j < |ve| && i != j ==> ve[i].validator_index!= ve[j].validator_index // ve indices are unique
        ensures ve[|ve|-1].validator_index as int !in get_VolExit_validator_indices(ve[..|ve|-1])
    {
        mappingVolExitIndices(ve[..|ve|-1]);
        assert forall i :: 0 <= i < |ve[..|ve|-1]| ==> get_VolExit_validator_indices(ve[..|ve|-1])[i] == ve[i].validator_index as int;
    }

    
    

}