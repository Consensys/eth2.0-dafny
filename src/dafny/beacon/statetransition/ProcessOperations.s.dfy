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
    import opened MathHelpers
    import opened SSZ

/**
     *  Collect pubkey in a list of validators.
     *
     *  @param  xv  A list of validators,
     *  @returns    The sequence\list of keys helpd byt the validators in `xv`.
     */
    function method seqKeysInValidators(xv : seq<Validator>) : seq<BLSPubkey>
        ensures |seqKeysInValidators(xv)| == |xv|
        decreases xv
    {
        if |xv| == 0 then  
            []
        else 
            [ xv[0].pubkey ] + seqKeysInValidators(xv[1..])
    }

    /**
     *  Collect pubkey in a list of deposits.
     *
     *  @param  xd  A list of validators,
     *  @returns    The sequence\list of keys held by the depositors in `xd`.
     */
    function method seqKeysInDeposits(xd : seq<Deposit>) : seq<BLSPubkey>
        ensures |seqKeysInDeposits(xd)| == |xd|
        decreases xd
    {
        if |xd| == 0 then  
            []
        else 
            [ xd[0].data.pubkey ] + seqKeysInDeposits(xd[1..])
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

        /**
     * Extract a validator from a single deposit.
     *
     *  @param  d       A single deposit.
     *  @returns        A validator created from the deposit information
     *
     *  @note           The `effective_balance` is not an active field in the current model but the code
     *                  to set this field is included as a comment for future reference.
     */
    function method get_validator_from_deposit(d: Deposit): Validator
        ensures get_validator_from_deposit(d).effective_balance <= MAX_EFFECTIVE_BALANCE as Gwei
    {
        var amount := d.data.amount; 
        var effective_balance := min((amount as nat- amount as nat % EFFECTIVE_BALANCE_INCREMENT as nat) as nat, MAX_EFFECTIVE_BALANCE as nat);

        Validator(d.data.pubkey, effective_balance as Gwei, false, FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH)
    }

    /**
     *  Append a new validator
     */
    function method validator_append(sv: ListOfValidators, v: Validator): ListOfValidators
        requires |sv| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
    {
        sv + [v]
    }
    /**
     *  Append a new balance entry
     */
    function method balance_append(sb: ListOfBalances, b: Gwei): ListOfBalances
        requires |sb| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
    {
        sb + [b]
    }

     /**
     *  Get the index of a validator. 
     *
     *  @notes  Helper function as no alternative indexing functionality available.
     *
     */
    function method get_validator_index(pk: seq<BLSPubkey>, pubkey: BLSPubkey) : ValidatorIndex
        requires |pk| < VALIDATOR_REGISTRY_LIMIT as int
        requires pubkey in pk
        ensures get_validator_index(pk,pubkey) as int < |pk|
        ensures pk[get_validator_index(pk,pubkey)] == pubkey
        decreases pk
    {
        if pk[0] == pubkey then 0 as ValidatorIndex
        else 1 + get_validator_index(pk[1..], pubkey)
        // alternative reverse form
        //if pk[|pk|-1] == pubkey then (|pk|-1) as ValidatorIndex
        //else get_validator_index(pk[..|pk|-1], pubkey)

    }

    /** */
    function updateRandao(s: BeaconState, b: BeaconBlockBody) : BeaconState
        requires |s.validators| == |s.balances|
        ensures |updateRandao(s,b).validators| == |updateRandao(s,b).balances|
        ensures updateRandao(s,b) == s.(randao_mixes := updateRandao(s,b).randao_mixes)
        ensures updateRandao(s,b).latest_block_header == s.latest_block_header
    {
        var epoch := get_current_epoch(s);

        // Verify RANDAO reveal not implemented
        //var proposer := s.validators[get_beacon_proposer_index(s)];
        // signing_root = compute_signing_root(epoch, get_domain(state, DOMAIN_RANDAO))
        // assert bls.Verify(proposer.pubkey, signing_root, body.randao_reveal)

        // # Mix in RANDAO reveal (use simplified mix value)
        var mix := DEFAULT_BYTES32; //var mix := xor(get_randao_mix(s, epoch), hash(b.randao_reveal));
        s.(randao_mixes := s.randao_mixes[(epoch % EPOCHS_PER_HISTORICAL_VECTOR) as nat := mix])
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

    // function total_deposits(deposits: seq<Deposit>): nat
    // {
    //     if |deposits| == 0 then 0
    //     //else deposits[0].data.amount as nat + total_deposits(deposits[1..])
    //     else total_deposits(deposits[..|deposits|-1]) + deposits[|deposits|-1].data.amount as nat
    // }

    // function total_balances(bal: seq<Gwei>): nat
    // {
    //     if |bal| == 0 then 0
    //     else bal[0] as nat + total_balances(bal[1..])
    // }

        /**
     * Extract a validator from a single deposit.
     *
     *  @param  d       A single deposit.
     *  @returns        A validator created from the deposit information
     *
     *  @note           The `effective_balance` is not an active field in the current model but the code
     *                  to set this field is included as a comment for future reference.
     */
    // function method get_validator_from_deposit(d: Deposit): Validator
    //     ensures get_validator_from_deposit(d).effective_balance <= MAX_EFFECTIVE_BALANCE as Gwei
    // {
    //     var amount := d.data.amount; 
    //     var effective_balance := min((amount as int- amount as int % EFFECTIVE_BALANCE_INCREMENT) as nat, MAX_EFFECTIVE_BALANCE as nat);

    //     Validator(d.data.pubkey, effective_balance as Gwei)
    // }

    /**
     *  Append a new validator
     */
    // function method validator_append(sv: ListOfValidators, v: Validator): ListOfValidators
    //     requires |sv| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
    // {
    //     sv + [v]
    // }
    /**
     *  Append a new balance entry
     */
    // function method balance_append(sb: ListOfBalances, b: Gwei): ListOfBalances
    //     requires |sb| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
    // {
    //     sb + [b]
    // }

     /**
     *  Get the index of a validator. 
     *
     *  @notes  Helper function as no alternative indexing functionality available.
     *
     */
    // function method get_validator_index(pk: seq<BLSPubkey>, pubkey: BLSPubkey) : ValidatorIndex
    //     requires |pk| < VALIDATOR_REGISTRY_LIMIT as int
    //     requires pubkey in pk
    //     ensures get_validator_index(pk,pubkey) as int < |pk|
    //     ensures pk[get_validator_index(pk,pubkey)] == pubkey
    //     decreases pk
    // {
    //     if pk[0] == pubkey then 0 as ValidatorIndex
    //     else 1 + get_validator_index(pk[1..], pubkey)
    //     // alternative reverse form
    //     //if pk[|pk|-1] == pubkey then (|pk|-1) as ValidatorIndex
    //     //else get_validator_index(pk[..|pk|-1], pubkey)

    // }

    // Beacon State Mutators

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

    ///////////////////////
    predicate attestationIsWellFormed(s: BeaconState, a: PendingAttestation)
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

    function updateAttestation(s: BeaconState, a: PendingAttestation) : BeaconState
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

    function updateAttestations(s: BeaconState, a: ListOfAttestations) : BeaconState
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

    lemma AttestationHelperLemma(s: BeaconState, s1: BeaconState, a: PendingAttestation)
        requires attestationIsWellFormed(s, a);
        requires s1.validators == s.validators
        requires s1.slot == s.slot
        requires s1.current_justified_checkpoint == s.current_justified_checkpoint
        requires s1.previous_justified_checkpoint == s.previous_justified_checkpoint
        ensures attestationIsWellFormed(s1, a);
    {
        
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

 
    function get_VolExit_validator_indices(ve: seq<VoluntaryExit>): seq<int>
        ensures |get_VolExit_validator_indices(ve)| == |ve|
    {
        if |ve| == 0 then []
        else [ve[0].validator_index as int] + get_VolExit_validator_indices(ve[1..])
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

///////////////////////////

    function get_PS_validator_indices(ps: seq<ProposerSlashing>): seq<int>
        ensures |get_PS_validator_indices(ps)| == |ps|
    {
        if |ps| == 0 then []
        else [ps[0].header_1.proposer_index as int] + get_PS_validator_indices(ps[1..])
    }

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

    // lemma helperPSLemma7(s: BeaconState, ps : seq<ProposerSlashing>)
    //     //requires |ps| > 0
    //     requires forall i,j :: 0 <= i < j < |ps| && i != j ==> ps[i].header_1.proposer_index!= ps[j].header_1.proposer_index // ve indices are unique
        
    //     requires forall i :: 0 <= i < |ps| ==> ps[i].header_1.slot == ps[i].header_2.slot
    //     requires forall i :: 0 <= i < |ps| ==> ps[i].header_1.proposer_index == ps[i].header_2.proposer_index 
    //     requires forall i :: 0 <= i < |ps| ==> ps[i].header_1 == ps[i].header_2
    //     requires forall i :: 0 <= i < |ps| ==> ps[i].header_1.proposer_index as int < |s.validators| 
    //     requires forall i :: 0 <= i < |ps| ==> !s.validators[ps[i].header_1.proposer_index].slashed 
    //     requires forall i :: 0 <= i < |ps| ==> s.validators[ps[i].header_1.proposer_index].activation_epoch <= get_current_epoch(s) < s.validators[ps[i].header_1.proposer_index].withdrawable_epoch

    //     ensures forall i :: 0 <= i < |s.validators| && i !in get_PS_validator_indices(ps) ==> updateProposerSlashings(s, ps).validators[i] == s.validators[i]
        
    
    /////////////////////////////////////////////////////////////////////////////////////


    // Helper functions: Sorted intersection of two sequences of unique sorted ValidatorIndex
    // function method indices_intersection(a : seq<ValidatorIndex>, b: seq<ValidatorIndex>): seq<ValidatorIndex>
    //     requires forall i,j :: 0 <= i < j < |a| ==> a[i] < a[j]
    //     requires forall i,j :: 0 <= i < j < |b| ==> b[i] < b[j]
    
    //     ensures forall i :: 0 <= i < |indices_intersection(a,b)| ==> 
    //             indices_intersection(a,b)[i] in a && indices_intersection(a,b)[i] in b
    //     ensures forall i, j :: 0 <= i < j < |indices_intersection(a,b)| ==> 
    //             indices_intersection(a,b)[i] != indices_intersection(a,b)[j]
    // {
    //     if |a| == 0 then []
    //     else 
    //         if a[0] in b then 
    //             [a[0]]
    //         else [] + indices_intersection(a[1..], b)
    // }

    function method sorted_intersection(a : seq<ValidatorIndex>, b: seq<ValidatorIndex>): seq<uint64>
        requires forall i,j :: 0 <= i < j < |a| ==> a[i] < a[j]
        requires forall i,j :: 0 <= i < j < |b| ==> b[i] < b[j]
        ensures forall i,j :: 0 <= i < j < |sorted_intersection(a,b)| ==> sorted_intersection(a,b)[i] < sorted_intersection(a,b)[j]
        ensures forall i :: 0 <= i < |sorted_intersection(a,b)| ==> sorted_intersection(a,b)[i] as ValidatorIndex in a &&
                                                                    sorted_intersection(a,b)[i] as ValidatorIndex in b
        ensures sorted_intersection(a,b) == sorted_intersection_fn(a,b)
    {
        if |a| == 0 then []
        else (if a[0] in b then [a[0] as uint64] else []) + sorted_intersection(a[1..], b)
    }

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

    


    function sorted_intersection_fn(a : seq<ValidatorIndex>, b: seq<ValidatorIndex>): seq<uint64>
        requires forall i,j :: 0 <= i < j < |a| ==> a[i] < a[j]
        requires forall i,j :: 0 <= i < j < |b| ==> b[i] < b[j]
        ensures forall i,j :: 0 <= i < j < |sorted_intersection_fn(a,b)| ==> sorted_intersection_fn(a,b)[i] < sorted_intersection_fn(a,b)[j]
        ensures forall i :: 0 <= i < |sorted_intersection_fn(a,b)| ==> sorted_intersection_fn(a,b)[i] as ValidatorIndex in a &&
                                                                    sorted_intersection_fn(a,b)[i] as ValidatorIndex in b
    {
        if |a| == 0 then []
        else (if a[0] in b then [a[0] as uint64] else []) + sorted_intersection_fn(a[1..], b)
    }

    //lemma sorted_intersection_bound(s: BeaconState, a : seq<ValidatorIndex>, b: seq<ValidatorIndex>)


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

    predicate valid_state_indices(s: BeaconState, indices: seq<uint64>)
    {
        forall i :: 0 <= i < |indices| ==> indices[i] as int < |s.validators|
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


     
    // function updateAttesterSlashing(s: BeaconState, indices: seq<ValidatorIndex>) : BeaconState 
    //     requires forall i :: 0 <= i < |indices| ==> indices[i] as int < |s.validators| 
    //     requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
    //     requires |s.validators| == |s.balances|

    //     ensures |s.validators| == |updateAttesterSlashing(s, indices).validators| 
    //     ensures updateAttesterSlashing(s, indices).slot == s.slot

    //     ensures |updateAttesterSlashing(s, indices).validators| == |updateAttesterSlashing(s, indices).balances|   
    //     ensures updateAttesterSlashing(s, indices).eth1_deposit_index == s.eth1_deposit_index
    //     ensures |get_active_validator_indices(updateAttesterSlashing(s, indices).validators, get_current_epoch(updateAttesterSlashing(s, indices)))| > 0
  
    //     decreases indices
    // {
    //     if |indices| == 0 then 
    //         s
    //     else 
    //         if is_slashable_validator(s.validators[indices[0]], get_current_epoch(s)) then
    //             slashValidatorPreservesActivateValidators(s, indices[0], get_beacon_proposer_index(s));
    //             updateAttesterSlashing(slash_validator(s, indices[0], get_beacon_proposer_index(s)), indices[1..])
    //         else
    //             updateAttesterSlashing(s, indices[1..])
    // }
    
    
    
    // function updateAttesterSlashing2(s: BeaconState, a: AttesterSlashing) : BeaconState 
    //     requires is_slashable_attestation_data(a.attestation_1.data, a.attestation_2.data)
    //     requires is_valid_indexed_attestation(s, a.attestation_1)
    //     requires is_valid_indexed_attestation(s, a.attestation_2)
    //     requires forall i :: 0 <= i < |a.attestation_1.attesting_indices| ==> a.attestation_1.attesting_indices[i] as int < |s.validators|
    //     requires forall i :: 0 <= i < |a.attestation_2.attesting_indices| ==> a.attestation_2.attesting_indices[i] as int < |s.validators|
    //     requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
    //     requires |s.validators| == |s.balances|

    //     ensures |s.validators| == |updateAttesterSlashing(s,a).validators| 
    //     //ensures updateAttesterSlashing(s, a).slot == s.slot
    //     //ensures get_current_epoch(s) == get_current_epoch(updateProposerSlashing(s, ps))
    // {
    //     var indices := sorted_intersection(a.attestation_1.attesting_indices, a.attestation_2.attesting_indices);
    //     slashAttesterIndices(s, indices)
    // }

    // function slashAttesterIndices(s: BeaconState, indices: seq<ValidatorIndex>): BeaconState
    //     requires forall i :: 0 <= i < |indices| ==> indices[i] as int < |s.validators| 
    //     requires |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
    //     requires |s.validators| == |s.balances|
    //     ensures |s.validators| == |slashAttesterIndices(s, indices).validators| 
    //     ensures slashAttesterIndices(s, indices).slot == s.slot
    //     decreases indices
    // {
    //     if |indices| == 0 then 
    //         s
    //     else 
    //         if is_slashable_validator(s.validators[indices[0]], get_current_epoch(s)) then
    //             slashValidatorPreservesActivateValidators(s, indices[0], get_beacon_proposer_index(s));
    //             slashAttesterIndices(slash_validator(s, indices[0], get_beacon_proposer_index(s)), indices[1..])
    //         else
    //             slashAttesterIndices(s, indices[1..])
    // }

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

 
    
    function method get_exit_epochs(sv: ListOfValidators) : seq<Epoch>
        ensures forall i :: 0 <= i < |get_exit_epochs(sv)| ==> get_exit_epochs(sv)[i] < FAR_FUTURE_EPOCH
    {
        if |sv| == 0 
            then []
        else 
            if sv[0].exitEpoch != FAR_FUTURE_EPOCH 
                then [sv[0].exitEpoch] + get_exit_epochs(sv[1..])
                else get_exit_epochs(sv[1..])
    }

    function method get_queue_churn(sv: ListOfValidators, exit_queue_epoch: Epoch) : seq<Validator>
    {
        if |sv| == 0 
            then []
        else 
            if sv[0].exitEpoch == exit_queue_epoch 
                then [sv[0]] + get_queue_churn(sv[1..], exit_queue_epoch)
                else get_queue_churn(sv[1..], exit_queue_epoch)
    }

    // // Check if ``validator`` is active.
    // predicate method is_active_validator(validator: Validator, epoch: Epoch)
    // {
    //     validator.activation_epoch <= epoch < validator.exitEpoch
    // }

    // // Return the sequence of active validator indices at ``epoch``.
    // // function get_active_validator_indices(s: BeaconState, epoch: Epoch) : seq<ValidatorIndex>
    // // NOTE: as BeaconState isn't modified and only validators field is accessed, the function is better suited to 
    // //      using an input parameter of just the list of validators (rather than the entire state)
    // function method get_active_validator_indices(sv: ListOfValidators, epoch: Epoch) : seq<ValidatorIndex>
    //     ensures |get_active_validator_indices(sv,epoch)| <= |sv|
    // {
    //     //[ValidatorIndex(i) for i, v in enumerate(state.validators) if is_active_validator(v, epoch)]
    //     if |sv| == 0 then []
    //     else 
    //         if is_active_validator(sv[|sv|-1], epoch) then get_active_validator_indices(sv[..|sv|-1], epoch) + [(|sv|-1) as ValidatorIndex]
    //         else get_active_validator_indices(sv[..|sv|-1], epoch)
    // }

    //Return the validator churn limit for the current epoch.
    function method get_validator_churn_limit(s: BeaconState) : uint64
        //ensures MIN_PER_EPOCH_CHURN_LIMIT <= get_validator_churn_limit(s) <= 
        //    (|get_active_validator_indices(s.validators, get_current_epoch(s))| as uint64/CHURN_LIMIT_QUOTIENT)  // i.e. at least 4
    {
        var active_validator_indices := get_active_validator_indices(s.validators, get_current_epoch(s));
        max(MIN_PER_EPOCH_CHURN_LIMIT as nat, (|active_validator_indices| as uint64/CHURN_LIMIT_QUOTIENT) as nat) as uint64
    }


    
    function method max_epoch(se: seq<Epoch>): Epoch
        requires |se| > 0
        ensures forall i :: 0 <= i < |se| ==> max_epoch(se) >= se[i]
        decreases se
    {
        if |se| == 1 then se[0]
        else
            if se[0] > max_epoch(se[1..]) then se[0]
            else max_epoch(se[1..])
    }
    
    // Return the epoch during which validator activations and exits initiated in ``epoch`` take effect.
    function method compute_activation_exit_epoch(epoch: Epoch) : Epoch
        requires epoch as int + 1 + MAX_SEED_LOOKAHEAD as int < 0x10000000000000000 
        ensures compute_activation_exit_epoch(epoch) > epoch
    {
        epoch + 1 as Epoch + MAX_SEED_LOOKAHEAD as Epoch
    }

    // //Return the randao mix at a recent ``epoch``.
    // function method get_randao_mix(state: BeaconState, epoch: Epoch): Bytes32
    // {
    //     state.randao_mixes[epoch % EPOCHS_PER_HISTORICAL_VECTOR as uint64]
    // }


    // // Return the seed at ``epoch``.
    // function method get_seed(state: BeaconState, epoch: Epoch, domain_type: DomainType): Bytes32
    //     requires epoch as int + EPOCHS_PER_HISTORICAL_VECTOR - MIN_SEED_LOOKAHEAD  - 1 < 0x10000000000000000
    // {
    //     var mix := get_randao_mix(state, (epoch as int + EPOCHS_PER_HISTORICAL_VECTOR - MIN_SEED_LOOKAHEAD - 1) as uint64);  // Avoid underflow
    //     var sb := serialise(domain_type) + serialise(Uint64(epoch as nat)) + serialise(mix);
    //     hash(sb)
    // }
    

    //Return from ``indices`` a random index sampled by effective balance.
    function method compute_proposer_index(state: BeaconState, indices: seq<ValidatorIndex>, seed: Bytes32) : ValidatorIndex
        requires |indices| > 0
    {
        // assert len(indices) > 0

        var MAX_RANDOM_BYTE := TWO_UP_8 - 1;
        var i : uint64 := 0;
        var total := |indices|;
        //while true {
        //     candidate_index = indices[compute_shuffled_index(i % total, total, seed)]
        //     random_byte = hash(seed + uint_to_bytes(uint64(i // 32)))[i % 32]
        //     effective_balance = state.validators[candidate_index].effective_balance
        //     if effective_balance * MAX_RANDOM_BYTE >= MAX_EFFECTIVE_BALANCE * random_byte:
        //         return candidate_index
        //    i := i + 1;
        //}
        
        
        0 as ValidatorIndex // temporary return value
    }

    // Return the shuffled index corresponding to ``seed`` (and ``index_count``).
    // Swap or not (https://link.springer.com/content/pdf/10.1007%2F978-3-642-32009-5_1.pdf)
    // See the 'generalized domain' algorithm on page 3
    function method compute_shuffled_index(index: uint64, index_count: uint64, seed: Bytes32): ValidatorIndex
        requires index < index_count
    {
        // for current_round in range(SHUFFLE_ROUND_COUNT):
        //     pivot = bytes_to_uint64(hash(seed + uint_to_bytes(uint8(current_round)))[0:8]) % index_count
        //     flip = (pivot + index_count - index) % index_count
        //     position = max(index, flip)
        //     source = hash(
        //         seed
        //         + uint_to_bytes(uint8(current_round))
        //         + uint_to_bytes(uint32(position // 256))
        //     )
        //     byte = uint8(source[(position % 256) // 8])
        //     bit = (byte >> (position % 8)) % 2
        //     index = flip if bit else index

        // return index

        0 as ValidatorIndex // temporary return value

    }

    //Return the beacon proposer index at the current slot.
    function method get_beacon_proposer_index(state: BeaconState): ValidatorIndex
        requires |get_active_validator_indices(state.validators, get_current_epoch(state))| > 0
        //ensures is_active_validator(state.validators[get_beacon_proposer_index(state)], get_current_epoch(state))
    {
        var epoch := get_current_epoch(state);
        var seed := hash(serialise(get_seed(state, epoch, DOMAIN_BEACON_PROPOSER)) + serialise(Uint64(state.slot as nat)));
        var indices := get_active_validator_indices(state.validators, epoch);

        compute_proposer_index(state, indices, seed)
    }

    // is_slashable_attestation_data
    // Check if ``data_1`` and ``data_2`` are slashable according to Casper FFG rules.
    predicate method is_slashable_attestation_data(data_1: AttestationData, data_2: AttestationData)
    {
        // Double vote
        (data_1 != data_2 && data_1.target.epoch == data_2.target.epoch) ||
        // Surround vote
        (data_1.source.epoch < data_2.source.epoch && data_2.target.epoch < data_1.target.epoch)
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

    predicate method is_valid_indexed_attestation(s: BeaconState, indexed_attestation: IndexedAttestation)
    {
        // Verify indices are sorted and unique
        var indices := indexed_attestation.attesting_indices;
        //if len(indices) == 0 or not indices == sorted(set(indices)):
        if (|indices| == 0 || !is_attesting_indices_sorted_and_unique(indices))
            then false
        else 
            true

        // Verify aggregate signature, not implemented at this time

        // pubkeys = [state.validators[i].pubkey for i in indices]
        // domain = get_domain(state, DOMAIN_BEACON_ATTESTER, indexed_attestation.data.target.epoch)
        // signing_root = compute_signing_root(indexed_attestation.data, domain)
        // return bls.FastAggregateVerify(pubkeys, signing_root, indexed_attestation.signature)
    }

    predicate method is_attesting_indices_sorted_and_unique(indices: AttestingIndices)
        requires |indices| > 0
    {
        forall i,j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]
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