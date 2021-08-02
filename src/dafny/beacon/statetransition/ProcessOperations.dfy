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

 //  @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /timeLimit:400 /noCheating:0

include "../../utils/NativeTypes.dfy"
include "../../utils/SeqHelpers.dfy"
include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../validators/Validators.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../Helpers.dfy"
include "../Helpers.s.dfy"
include "../Helpers.p.dfy"
include "ProcessOperations.s.dfy"
include "ProcessOperations.p.dfy"

/**
 *  Process operations and related components for the Beacon Chain.
 */
module ProcessOperations {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NativeTypes
    import opened Constants
    import opened BeaconChainTypes
    import opened Validators
    import opened AttestationsTypes
    import opened BeaconHelperSpec
    import opened SeqHelpers
    import opened BeaconHelpers
    import opened BeaconHelperProofs
    import opened ProcessOperationsSpec
    import opened ProcessOperationsProofs
    
    
    /** 
     *  Process the operations defined by a block body.
     *  
     *  @param  s   A state.
     *  @param  bb  A block body.
     *  @returns    The state obtained after applying the operations of `bb` to `s`.
     *
     *  @note       This implementation currently takes several minutes to verify.
     *              An option to optimise would be to more explicity assert component
     *              pre and post conditions to speed up verification.
     */
    method process_operations(s: BeaconState, bb: BeaconBlockBody)  returns (s' : BeaconState) 
        requires  |s.validators| == |s.balances|
        //|get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires minimumActiveValidators(s) 
        requires isValidBeaconBlockBody(s, bb)
        
        ensures s' == updateOperations(s,bb)
        ensures |s'.validators| == |s'.balances|
        ensures s'.slot == s.slot
        ensures s'.latest_block_header == s.latest_block_header
    {
        s':= s;
        var slashed_any := false;

        // process the proposer slashings
        var i := 0;
        assert isValidProposerSlashings(s, bb);
        assert s' == updateProposerSlashings(s, bb.proposer_slashings[..i]);
        assert |s'.validators| == |s'.balances|;
        assert s'.slot == s.slot;
        assert s'.latest_block_header == s.latest_block_header;
        assert forall j :: i <= j < |bb.proposer_slashings| 
            ==> s'.validators[bb.proposer_slashings[j].header_1.proposer_index] 
                == s.validators[bb.proposer_slashings[j].header_1.proposer_index];

        while i < |bb.proposer_slashings| 
            decreases |bb.proposer_slashings| - i

            invariant 0 <= i <= |bb.proposer_slashings| 
            invariant |s'.validators| ==  |s.validators| 
            invariant s' == updateProposerSlashings(s, bb.proposer_slashings[..i])
            invariant s'.slot == s.slot
            invariant s'.latest_block_header == s.latest_block_header
            
        {
            assert 1 <= |bb.proposer_slashings|; 
            seqInitLast<ProposerSlashing>(bb.proposer_slashings, i);
            assert bb.proposer_slashings[..i+1] 
                    == bb.proposer_slashings[..i] + [bb.proposer_slashings[i]];
            PSHelperLemma3(bb.proposer_slashings[..i+1]);
            s' := process_proposer_slashing(s', bb.proposer_slashings[i]);
            i := i + 1;
        }
        fullSeq<ProposerSlashing>(bb.proposer_slashings, i);
        assert bb.proposer_slashings[..i] == bb.proposer_slashings;
        // store intermediate state to assist with final post condition check
        ghost var s1 := updateProposerSlashings(s, bb.proposer_slashings);
        assert s' == s1;

        // process attester slashings
        i := 0;
        assert isValidAttesterSlashings(s1, bb);
        assert s' == updateAttesterSlashings(s1, bb.attester_slashings[..i]);
        assert |s'.validators| == |s'.balances|;
        assert s'.slot == s.slot;
        assert s'.latest_block_header == s.latest_block_header;

        while i < |bb.attester_slashings| 
            decreases |bb.attester_slashings| - i

            invariant 0 <= i <= |bb.attester_slashings| 
            invariant |s'.validators| ==  |s.validators| 
            invariant s' == updateAttesterSlashings(s1, bb.attester_slashings[..i])
            invariant s'.slot == s.slot
            invariant s'.latest_block_header == s.latest_block_header
        {
            assert 1 <= |bb.attester_slashings|; 
            seqInitLast<AttesterSlashing>(bb.attester_slashings, i);
            assert bb.attester_slashings[..i+1] 
                    == bb.attester_slashings[..i] + [bb.attester_slashings[i]];
            assert is_valid_indexed_attestation(bb.attester_slashings[i].attestation_1);
            assert is_valid_indexed_attestation(bb.attester_slashings[i].attestation_2);
            assert |sorted_intersection(bb.attester_slashings[i].attestation_1.attesting_indices, 
                                        bb.attester_slashings[i].attestation_2.attesting_indices)| > 0;
            s', slashed_any := process_attester_slashing(s', bb.attester_slashings[i]);
            i := i + 1;
        }
        fullSeq<AttesterSlashing>(bb.attester_slashings, i);
        assert bb.attester_slashings[..i] == bb.attester_slashings;
        ghost var s2 := updateAttesterSlashings(s1, bb.attester_slashings);
        assert s' == s2;

        // process attestations
        i := 0;
        assert isValidAttestations(s2, bb);
        assert s' == updateAttestations(s2, bb.attestations[..i]);
        assert |s'.validators| == |s'.balances|;
        assert s'.slot == s.slot;
        assert s'.latest_block_header == s.latest_block_header;

        while i < |bb.attestations| 
            decreases |bb.attestations| - i

            invariant 0 <= i <= |bb.attestations|
            invariant s' == updateAttestations(s2, bb.attestations[..i])
            invariant |s'.validators| ==  |s.validators| 
            invariant s'.slot == s.slot
            invariant s'.latest_block_header == s.latest_block_header
        {
            assert 1 <= |bb.attestations|; 
            seqInitLast<Attestation>(bb.attestations, i);
            assert bb.attestations[..i+1] == bb.attestations[..i] + [bb.attestations[i]];
            s':= process_attestation(s', bb.attestations[i]); 
            i := i+1;
        }
        fullSeq<Attestation>(bb.attestations, i);
        assert bb.attestations[..i] == bb.attestations;
        ghost var s3 := updateAttestations(s2, bb.attestations);
        assert s3 == s';

        //  process deposits in the beacon block body.
        i := 0;
        assert s'.eth1_deposit_index == s.eth1_deposit_index;
        assert isValidDeposits(s3, bb);
        assert s' == updateDeposits(s3, bb.deposits[..i]);
        assert |s'.validators| == |s'.balances|;
        assert s'.slot == s.slot;
        assert s'.latest_block_header == s.latest_block_header;
        assert s' == updateDeposits(s3, bb.deposits[..i]);
        assert total_balances(s'.balances) + total_deposits(bb.deposits[..i]) 
                < 0x10000000000000000;
        
        while i < |bb.deposits| 
            decreases |bb.deposits| - i

            invariant 0 <= i <= |bb.deposits|
            invariant s'.eth1_deposit_index == s.eth1_deposit_index + i as uint64
            invariant total_balances(s3.balances) + total_deposits(bb.deposits[..i]) 
                        < 0x10000000000000000 
            invariant |s'.validators| == |s'.balances| 
            invariant s' == updateDeposits(s3, bb.deposits[..i])
            invariant s'.slot == s.slot
            invariant s'.latest_block_header == s.latest_block_header
        {
            assert 1 <= |bb.deposits|; 
            seqInitLast<Deposit>(bb.deposits, i);
            assert bb.deposits[..i+1] == bb.deposits[..i] + [bb.deposits[i]];
            subsetDepositSumProp(bb.deposits, i+1);
            s':= process_deposit(s', bb.deposits[i]); 
            i := i+1;
        }
        assert i == |bb.deposits|;
        fullSeq<Deposit>(bb.deposits, i);
        assert bb.deposits[..i] == bb.deposits;
        ghost var s4 := updateDeposits(s3, bb.deposits);
        assert s4 == s';

        // process voluntary exits
        i := 0;
        assert isValidVoluntaryExits(s4, bb);
        assert s' == updateVoluntaryExits(s4, bb.voluntary_exits[..i]);
        assert s'.slot == s.slot;
        assert s'.latest_block_header == s.latest_block_header;
        assert |s'.validators| == |s'.balances|;
        assert s'.eth1_deposit_index == s.eth1_deposit_index + |bb.deposits| as uint64;
        
        while i < |bb.voluntary_exits| 
            decreases |bb.voluntary_exits| - i

            invariant 0 <= i <= |bb.voluntary_exits|
            invariant s' == updateVoluntaryExits(s4, bb.voluntary_exits[..i])
            invariant s'.slot == s.slot
            invariant s'.latest_block_header == s.latest_block_header
        {
            VEHelperLemma3(bb.voluntary_exits[..i+1]);
            assert 1 <= |bb.voluntary_exits|; 
            seqInitLast<VoluntaryExit>(bb.voluntary_exits, i);
            assert bb.voluntary_exits[..i+1] == bb.voluntary_exits[..i] + [bb.voluntary_exits[i]];
            s' := process_voluntary_exit(s', bb.voluntary_exits[i]);
            i := i + 1;
        }
        assert i == |bb.voluntary_exits|;
        fullSeq<VoluntaryExit>(bb.voluntary_exits, i);
        assert bb.voluntary_exits[..i] == bb.voluntary_exits;
        ghost var s5 := updateVoluntaryExits(s4, bb.voluntary_exits);
        assert s5 == s';
        assert s' == updateOperations(s,bb);
    }

    /**
     *  Process a proposer slashing.
     *
     *  @param  s   A state.
     *  @param  ps  A proposer slashing.  
     *  @returns    The state obtained applying `ps` to `s`.
     */
    method process_proposer_slashing(s: BeaconState, ps : ProposerSlashing)  returns (s' : BeaconState)  
        requires ps.header_1.slot == ps.header_2.slot
        requires ps.header_1.proposer_index == ps.header_2.proposer_index 
        requires ps.header_1 == ps.header_2
        requires ps.header_1.proposer_index as int < |s.validators| 
        requires !s.validators[ps.header_1.proposer_index].slashed
        requires s.validators[ps.header_1.proposer_index].activation_epoch 
                    <= get_current_epoch(s) 
                    < s.validators[ps.header_1.proposer_index].withdrawable_epoch
        //requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires minimumActiveValidators(s)
        requires |s.validators| == |s.balances|
        
        ensures s' == updateProposerSlashing(s,ps)
    {
        // # Verify header slots match
        assert ps.header_1.slot == ps.header_2.slot;

        // # Verify header proposer indices match
        assert ps.header_1.proposer_index == ps.header_2.proposer_index;

        // # Verify the headers are different
        assert ps.header_1 == ps.header_2;

        // # Verify the proposer is slashable
        var proposer := s.validators[ps.header_1.proposer_index];
        assert is_slashable_validator(proposer, get_current_epoch(s));

        // # Verify signatures is not implemented
        assert ps.header_1.proposer_index as int < |s.validators| ;
        assert get_beacon_proposer_index(s) as int < |s.validators|;
        assert |s.validators| == |s.balances|;
        assert |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0;

        // The whistleblower_index parameter of slash_validator is None in the spec.
        // As 'None' isn't possible in Dafny, set the parameter to get_beacon_proposer_index(s)
        // as it would be set to that for 'None' within slash_validator.
        s' := slash_validator(s, ps.header_1.proposer_index, get_beacon_proposer_index(s));
    }

    /**
     *  Process an attester slashing.
     *
     *  @param  s   A state.
     *  @param  a   An attester slashing.  
     *  @returns    The state obtained applying `a` to `s`.
     */
    method process_attester_slashing(s: BeaconState, a: AttesterSlashing) 
            returns (s' : BeaconState, flag: bool) 
        requires forall i :: 0 <= i < |a.attestation_1.attesting_indices| 
                    ==> a.attestation_1.attesting_indices[i] as int < |s.validators|
        requires forall i :: 0 <= i < |a.attestation_2.attesting_indices|
                    ==> a.attestation_2.attesting_indices[i] as int < |s.validators|
        //requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        requires minimumActiveValidators(s)
        requires |s.validators| == |s.balances|
        requires is_slashable_attestation_data(a.attestation_1.data, a.attestation_2.data)
        requires is_valid_indexed_attestation(a.attestation_1)
        requires is_valid_indexed_attestation(a.attestation_2)
        requires |sorted_intersection(a.attestation_1.attesting_indices, 
                                      a.attestation_2.attesting_indices)| 
                    > 0

        ensures s' == updateAttesterSlashing(s, 
                                            sorted_intersection(a.attestation_1.attesting_indices, 
                                                                a.attestation_2.attesting_indices)
                                            )
        //ensures flag is not implemented in this simplified model
    {
        //Double vote
        //(data_1 != data_2 && data_1.target.epoch == data_2.target.epoch) ||
        // Surround vote
        //(data_1.source.epoch < data_2.source.epoch && data_2.target.epoch < data_1.target.epoch)
        assert is_slashable_attestation_data(a.attestation_1.data, a.attestation_2.data);
        // Verify indices are sorted and unique, and at least 1
        assert is_valid_indexed_attestation(a.attestation_1);
        // assert is_valid_indexed_attestation(state, attestation_2)
        assert is_valid_indexed_attestation(a.attestation_2);

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
            invariant get_active_validator_indices(s.validators, get_current_epoch(s)) 
                        == get_active_validator_indices(s'.validators, get_current_epoch(s));
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
            if (is_slashable_validator(origState.validators[ts[i]], get_current_epoch(origState))) {
                assert (!origState.validators[ts[i]].slashed) 
                    && (origState.validators[ts[i]].activation_epoch 
                            <= get_current_epoch(origState) 
                            < origState.validators[ts[i]].withdrawable_epoch
                        );
                slashValidatorPreservesActiveValidators(origState, 
                                                        ts[i], 
                                                        get_beacon_proposer_index(origState)
                                                    );
                s' := slash_validator(origState, ts[i], get_beacon_proposer_index(origState));
                //assert minimumActiveValidators(s');
                flag := true;
            }
            else {
                  s' := s';
            }
            assert 1 <= |ts|; 
            seqInitLast<uint64>(ts, i);
            assert ts[..i+1] == ts[..i] + [ts[i]];
            assert origState == updateAttesterSlashing(s, ts[..i]);
            assert s' == updateAttesterSlashingComp(origState, ts[i]);
            assert s' == updateAttesterSlashingComp(updateAttesterSlashing(s, ts[..i]), ts[i]);
            assert valid_state_indices(s, ts);
            assert 0 < i+1 <= |ts|;
            assert valid_state_indices(s, ts[..(i+1)]);
            assert |ts[..(i+1)]| != 0;
            assert updateAttesterSlashing(s, ts[..(i+1)]) 
                    == updateAttesterSlashingComp(updateAttesterSlashing(s, ts[..i]), ts[i]);
            assert s' == updateAttesterSlashing(s, ts[..(i+1)]);
            i := i+1;
            assert valid_state_indices(s, ts[..i]);
            assert s' == updateAttesterSlashing(s, ts[..i]);
        }
        assert i == |ts|;
        fullSeq<uint64>(ts, i);
        assert ts[..i] == ts;
        assert s' == updateAttesterSlashing(s, ts[..i]);
        assert s' == updateAttesterSlashing(s, ts);
        assert ts == sorted_intersection(a.attestation_1.attesting_indices, 
                                         a.attestation_2.attesting_indices);
        //assert slashed_any;
    }

    /**
     *
     *  Example.
     *  epoch   0             1                 k               k + 1       
     *          |............|....         .....|.................|.....................
     *  state                                                      s
     *  slot    0                                                  s.slot 
     *                                            <-SLOTS_PER_EPOCH->
     *  slot         s.slot - SLOTS_PER_EPOCH = x1                x2 = s.slot - 1
     *  slot(a)                                   *****************     
     *                          =======a======>tgt1
     *                                            =======a======>tgt2
     *     
     * 
     *  epoch(s) = k + 1, and previous epoch is k.
     *  source and target are checkpoints.
     *  Target must have an epoch which is k (tgt1, case1) or k + 1 (tgt2, case2).
     *  a.data.slot (slot(a))is the slot in which ther validator makes the attestation.
     *  x1 <= slot(a) <= x2.
     *  Two cases arise: 
     *      1. compute_epoch_at_slot(a.data.slot) is previous_epoch k 
     *          in this case the target's epoch must be  previous-epoch k
     *      2. compute_epoch_at_slot(a.data.slot) is current_epoch k + 1 
     *          in this case the target's epoch must be  current-epoch k + 1
     *
     *  MIN_ATTESTATION_INCLUSION_DELAY is 1.
     *
     *  Question: what is the invariant for the attestations in a state?
     *
     *  Process an attestation.
     *
     *  @param  s   A state.
     *  @param  a   An attestation.  
     *  @returns    The state obtained applying `a` to `s`.
     */
    method process_attestation(s: BeaconState, a: Attestation) returns (s' : BeaconState)
        requires attestationIsWellFormed(s, a)
        requires |s.current_epoch_attestations| < MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
        requires |s.previous_epoch_attestations| < MAX_ATTESTATIONS as nat * SLOTS_PER_EPOCH as nat 
        requires minimumActiveValidators(s)

        ensures s' == updateAttestation(s,a)
        ensures s'.eth1_deposit_index == s.eth1_deposit_index;
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

        var pending_attestation := PendingAttestation(
            a.aggregation_bits, 
            a.data, 
            (s.slot - a.data.slot), 
            get_beacon_proposer_index(s) 
        );

        if a.data.target.epoch == get_current_epoch(s) {
            //  Add a to current attestations
            assert a.data.source == s.current_justified_checkpoint;
            s' := s.(
                current_epoch_attestations := s.current_epoch_attestations + [pending_attestation]
            );
            // s.current_epoch_attestations.append(pending_attestation)
        }
        else {
            assert a.data.source == s.previous_justified_checkpoint;
            s' := s.(
                previous_epoch_attestations := s.previous_epoch_attestations + [pending_attestation]
            );
        }
        // # Verify signature
        // Not implemented as part of the simplificiation
        //assert is_valid_indexed_attestation(s', get_indexed_attestation(s', a));
    }

    /**
     *  Process a deposit operation.
     *
     *  @param  s   A state.
     *  @param  d   A deposit.  
     *  @returns    The state obtained depositing of `d` to `s`.
    */
    method process_deposit(s: BeaconState, d : Deposit)  returns (s' : BeaconState)  
        requires minimumActiveValidators(s)
        requires |s.validators| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
        requires s.eth1_deposit_index as int + 1 < 0x10000000000000000 
        requires |s.validators| == |s.balances|
        requires total_balances(s.balances) + d.data.amount as int < 0x10000000000000000

        ensures s'.eth1_deposit_index == s.eth1_deposit_index + 1
        ensures s' == updateDeposit(s,d) 
    {
        // Note that it is assumed that all new validator deposits are verified.
        // i.e. the step # Verify the deposit signature (proof of possession), which is not checked 
        // by the deposit contract, is not performed.
        var pk := seqKeysInValidators(s.validators);
        s' := s.(
                eth1_deposit_index := (s.eth1_deposit_index as int + 1) as uint64,
                validators := if d.data.pubkey in pk then 
                                    s.validators // unchanged validator members
                                else 
                                    (s.validators + [get_validator_from_deposit(d)]),
                balances := if d.data.pubkey in pk then 
                                    individualBalanceBoundMaintained(s.balances,d);
                                    increase_balance(s,
                                                    get_validator_index(pk, d.data.pubkey),
                                                    d.data.amount).balances
                                else 
                                    s.balances + [d.data.amount]
        );
    }

    /**
     *  Process a voluntary exit.
     *
     *  @param  s               A state.
     *  @param  voluntary_exit  A voluntary exit.  
     *  @returns                The state obtained applying `voluntary_exit` to `s`.
     */
    method process_voluntary_exit(s: BeaconState, voluntary_exit: VoluntaryExit) returns (s' : BeaconState) 
        requires minimumActiveValidators(s)
        requires |s.validators| == |s.balances|
        requires voluntary_exit.validator_index as int < |s.validators|
        requires !s.validators[voluntary_exit.validator_index].slashed
        requires s.validators[voluntary_exit.validator_index].activation_epoch 
                    <= get_current_epoch(s) 
                    < s.validators[voluntary_exit.validator_index].withdrawable_epoch
        requires s.validators[voluntary_exit.validator_index].exitEpoch == FAR_FUTURE_EPOCH
        requires get_current_epoch(s) >= voluntary_exit.epoch
        requires get_current_epoch(s) 
                    >= s.validators[voluntary_exit.validator_index].activation_epoch + SHARD_COMMITTEE_PERIOD 
        
        ensures s' == updateVoluntaryExit(s, voluntary_exit)
    {
        var validator := s.validators[voluntary_exit.validator_index];

        // Note if any of the spec asserts fail then the state is unchanged 
        // and the voluntary exit is not implemented.

        // # Verify the validator is active
        assert is_active_validator(validator, get_current_epoch(s));

        // # Verify exit has not been initiated
        assert validator.exitEpoch == FAR_FUTURE_EPOCH;

        // # Exits must specify an epoch when they become valid; they are not valid before then
        assert get_current_epoch(s) >= voluntary_exit.epoch;

        // # Verify the validator has been active long enough
        assert get_current_epoch(s) >= validator.activation_epoch + SHARD_COMMITTEE_PERIOD;

        // # Verify signature
        // Not implemented as part of the simplificiation.
        
        // # Initiate exit
        s' := initiate_validator_exit(s, voluntary_exit.validator_index);
    }

}