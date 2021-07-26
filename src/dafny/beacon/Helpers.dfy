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

include "../utils/Eth2Types.dfy"
include "../utils/MathHelpers.dfy"
include "../utils/NativeTypes.dfy"

include "../ssz/Constants.dfy"
include "../ssz/Serialise.dfy"

include "BeaconChainTypes.dfy"
include "Helpers.s.dfy"
include "Helpers.p.dfy"
include "attestations/AttestationsTypes.dfy"
include "validators/Validators.dfy"



/**
 * Misc helpers.
 */
module BeaconHelpers {

    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened MathHelpers
    import opened NativeTypes

    import opened Constants
    import opened SSZ

    import opened BeaconChainTypes
    import opened BeaconHelperSpec
    import opened BeaconHelperProofs
    import opened AttestationsTypes
    import opened Validators
    
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

    
    /**
     *  Check that a bitlist has all bits set to 1.
     *  @param      xs  
     *  @returns    
     */
    function method all(xs: seq<bool>) : bool
    {
        forall i :: 0 < i < |xs| ==> xs[i]
    }
    
    /**
     *  The epoch of a slot.
     *
     *  @param  slot    A slot.
     *  @returns        The epoch of the slot.
     */
    function method compute_epoch_at_slot(slot: Slot) : Epoch
        ensures compute_epoch_at_slot(slot) as int * SLOTS_PER_EPOCH as int < 0x10000000000000000
        ensures compute_epoch_at_slot(slot) * SLOTS_PER_EPOCH <= slot 
    {
        divLess(slot as nat, SLOTS_PER_EPOCH as nat);
        div2(slot as nat, SLOTS_PER_EPOCH as nat);
        assert(slot / SLOTS_PER_EPOCH <= slot);
        (slot / SLOTS_PER_EPOCH) as Epoch
    }

    
    /**
     *  Slot number at start of an epoch.
     *  
     *  @param  epoch   An epoch.
     *  @returns        The slot number at the start of `epoch`.
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#compute_start_slot_at_epoch}
     */
    function method compute_start_slot_at_epoch(epoch: Epoch) : Slot
        requires epoch as int * SLOTS_PER_EPOCH as int < 0x10000000000000000    // report
    {
        epoch * SLOTS_PER_EPOCH as Slot
    }

    /**
     *  @param  state   A beacon state.
     *  @returns        The epoch of the state's slot.
     */
    function method get_current_epoch(state: BeaconState) : Epoch 
        ensures get_current_epoch(state) as int * SLOTS_PER_EPOCH as int < 0x10000000000000000
        ensures get_current_epoch(state) * SLOTS_PER_EPOCH <= state.slot
        ensures state.slot % SLOTS_PER_EPOCH != 0 ==> 
            get_current_epoch(state) * SLOTS_PER_EPOCH < state.slot
        /** A useful proof that states that the slot that corresponds
            to the current epoch is within the range of the history 
            a block roots stored in the state.block_roots. */
        ensures state.slot - get_current_epoch(state) * SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT
    {
        compute_epoch_at_slot(state.slot)
    }

    /**
     *  @param  state   A beacon state.
     *  @returns        Epoch before state's epoch and 0 is state's epoch is 0.
     */
    function method get_previous_epoch(state: BeaconState) : Epoch 
        ensures get_previous_epoch(state) <= get_current_epoch(state)
        ensures get_previous_epoch(state) as int * SLOTS_PER_EPOCH as int < 0x10000000000000000
        ensures get_previous_epoch(state) * SLOTS_PER_EPOCH <= state.slot
        ensures get_current_epoch(state) == 0 ==>  get_current_epoch(state) == get_previous_epoch(state)
        ensures get_current_epoch(state) > 0 ==> get_current_epoch(state) - 1 == get_previous_epoch(state) 
        /** A useful proof that states that the slot that corresponds
            to the previous epoch is within the range of the history 
            a block roots stored in the state.block_roots. */
        ensures state.slot - get_previous_epoch(state) * SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT
        ensures get_current_epoch(state) > 0 ==> get_previous_epoch(state) * SLOTS_PER_EPOCH < state.slot
    {
        var e := get_current_epoch(state);
        //  max(0, e - 1)
        if e > 0 then e - 1 else e 
    }

    /**
     *  The block root at the start of an epoch.
     *
     *  @param  state   A beacon state.
     *  @param  epoch   A recent epoch (must be tracked in state.block_roots).
     *  @returns        The block root at the beginning of epoch. 
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#get_block_root}
     *  
     *  Given an epoch, start slot is epoch * SLOTS_PER_EPOCH.
     *  Only the last SLOTS_PER_HISTORICAL_ROOT block roots are stored in the state.
     *  To be able to retrieve the block root, the slot of epoch must be recent
     *  i.e state.slot - epoch * SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT.
     */
    function method get_block_root(state: BeaconState, epoch: Epoch) : Root  
        requires epoch as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
        requires epoch *  SLOTS_PER_EPOCH   < state.slot  
        requires state.slot  - epoch  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
    { 
        var slot_of_epoch := compute_start_slot_at_epoch(epoch);  
        assert(slot_of_epoch == epoch * SLOTS_PER_EPOCH);
        assert(slot_of_epoch < state.slot);
        get_block_root_at_slot(state, slot_of_epoch)
    }
    
    /**
     *  The block root at the start of a given (recent) slot.
     *
     *  @param  state   A beacon state.
     *  @param  slot    A recent slot (must be tracked in state.block_roots).
     *  @returns        The block root at (a recent) slot. 
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#get_block_root_at_slot}
     *  
     */
    function method get_block_root_at_slot(state: BeaconState, slot: Slot) : Root
        requires slot < state.slot 
        requires state.slot - slot <=  SLOTS_PER_HISTORICAL_ROOT
    {
        state.block_roots[slot % SLOTS_PER_HISTORICAL_ROOT]
    }

    /**
     *  Count instances of d in a list of eth1_data.
     */
     function method count_eth1_data_votes(l: ListOfEth1Data, d: Eth1Data) : nat
    {
        if |l| == 0 then 0
        else 
            if (l[0] == d) then 1 + count_eth1_data_votes(l[1..], d)
            else count_eth1_data_votes(l[1..], d)
     }

    /**
     *  Check if ``validator`` is slashable.
     */
    predicate method is_slashable_validator(v: Validator, epoch: Epoch)
    {
        (!v.slashed) && (v.activation_epoch <= epoch < v.withdrawable_epoch)
    }

    /**
     *  Check if ``validator`` is eligible to be placed into the activation queue.
     */
    predicate method is_eligible_for_activation_queue(v: Validator)
    {
        v.activation_eligibility_epoch == FAR_FUTURE_EPOCH
        && v.effective_balance == MAX_EFFECTIVE_BALANCE
    }

    /**
     *   Check if ``validator`` is eligible for activation.
     */
    predicate method is_eligible_for_activation(s: BeaconState, v: Validator)
    {
        // Placement in queue is finalized
        v.activation_eligibility_epoch <= s.finalised_checkpoint.epoch
        // Has not yet been activated
        && v.activation_epoch == FAR_FUTURE_EPOCH
    }

    function method get_activation_queue(s: BeaconState, i: nat): seq<ValidatorIndex>
        decreases |s.validators| - i
    {
        if i < |s.validators| then
            if is_eligible_for_activation(s, s.validators[i]) then
                [i as ValidatorIndex] + get_activation_queue(s, i+1)
            else 
                get_activation_queue(s, i+1)
        else
            []
    }

    

    


    // Check if ``validator`` is active.
    predicate method is_active_validator(validator: Validator, epoch: Epoch)
    {
        validator.activation_epoch <= epoch < validator.exitEpoch
    }

    // Return the sequence of active validator indices at ``epoch``.
    // function get_active_validator_indices(s: BeaconState, epoch: Epoch) : seq<ValidatorIndex>
    // NOTE: as BeaconState isn't modified and only validators field is accessed, the function is better suited to 
    //      using an input parameter of just the list of validators (rather than the entire state)
    function method get_active_validator_indices(sv: ListOfValidators, epoch: Epoch) : seq<ValidatorIndex>
        ensures |get_active_validator_indices(sv,epoch)| <= |sv|
        ensures forall i :: 0 <= i < |get_active_validator_indices(sv, epoch)| ==> get_active_validator_indices(sv, epoch)[i] as nat < |sv|
        ensures forall i :: 0 <= i < |get_active_validator_indices(sv, epoch)| ==> 
                sv[get_active_validator_indices(sv, epoch)[i] ].activation_epoch <= epoch < sv[get_active_validator_indices(sv, epoch)[i]].exitEpoch
        ensures (exists i :: 0 <= i < |sv| && sv[i].activation_epoch <= epoch < sv[i].exitEpoch)
                ==> |get_active_validator_indices(sv, epoch)| > 0
                

    {
        //[ValidatorIndex(i) for i, v in enumerate(state.validators) if is_active_validator(v, epoch)]
        if |sv| == 0 then []
        else 
            if is_active_validator(sv[|sv|-1], epoch) then get_active_validator_indices(sv[..|sv|-1], epoch) + [(|sv|-1) as ValidatorIndex]
            else get_active_validator_indices(sv[..|sv|-1], epoch)
    }

    //get_committee_count_per_slot

    // def get_committee_count_per_slot(state: BeaconState, epoch: Epoch) -> uint64:
    // """
    // Return the number of committees in each slot for the given ``epoch``.
    // """
    // return max(uint64(1), min(
    //     MAX_COMMITTEES_PER_SLOT,
    //     uint64(len(get_active_validator_indices(state, epoch))) // SLOTS_PER_EPOCH // TARGET_COMMITTEE_SIZE,
    // ))

    function method get_committee_count_per_slot(s: BeaconState, epoch: Epoch) : uint64
        ensures 1 <= get_committee_count_per_slot(s,epoch) <= MAX_COMMITTEES_PER_SLOT == TWO_UP_6;
        //ensures |get_active_validator_indices(s.validators, epoch)| as uint64 < 2 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE ==> get_committee_count_per_slot(s,epoch) == 1
        //ensures 2 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE <= |get_active_validator_indices(s.validators, epoch)| as uint64 < 3 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE==> get_committee_count_per_slot(s,epoch) == 2
        //ensures 3 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE <= |get_active_validator_indices(s.validators, epoch)| as uint64 < 4 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE==> get_committee_count_per_slot(s,epoch) == 3

        //ensures 64 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE <= |get_active_validator_indices(s.validators, epoch)| as uint64 ==> get_committee_count_per_slot(s,epoch) == 64
        // TARGET_COMMITTEE_SIZE == TWO_UP_7;
    {
        max(1, min(
            MAX_COMMITTEES_PER_SLOT as nat,  
            |get_active_validator_indices(s.validators, epoch)| / SLOTS_PER_EPOCH as nat / TARGET_COMMITTEE_SIZE as nat) 
        ) as uint64
    }

    //compute_shuffled_index

    // // Return the shuffled index corresponding to ``seed`` (and ``index_count``).
    // // Swap or not (https://link.springer.com/content/pdf/10.1007%2F978-3-642-32009-5_1.pdf)
    // // See the 'generalized domain' algorithm on page 3
    // function method compute_shuffled_index(index: uint64, index_count: uint64, seed: Bytes32): ValidatorIndex
    //     requires index < index_count
    // {
    //     // for current_round in range(SHUFFLE_ROUND_COUNT):
    //     //     pivot = bytes_to_uint64(hash(seed + uint_to_bytes(uint8(current_round)))[0:8]) % index_count
    //     //     flip = (pivot + index_count - index) % index_count
    //     //     position = max(index, flip)
    //     //     source = hash(
    //     //         seed
    //     //         + uint_to_bytes(uint8(current_round))
    //     //         + uint_to_bytes(uint32(position // 256))
    //     //     )
    //     //     byte = uint8(source[(position % 256) // 8])
    //     //     bit = (byte >> (position % 8)) % 2
    //     //     index = flip if bit else index

    //     // return index

    //     0 as ValidatorIndex // temporary return value

    // }
// def compute_shuffled_index(index: uint64, index_count: uint64, seed: Bytes32) -> uint64:
    // """
    // Return the shuffled index corresponding to ``seed`` (and ``index_count``).
    // """
    // assert index < index_count

    // # Swap or not (https://link.springer.com/content/pdf/10.1007%2F978-3-642-32009-5_1.pdf)
    // # See the 'generalized domain' algorithm on page 3
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

    function method compute_shuffled_index(index: uint64, index_count: uint64, seed: Bytes32) : uint64
        requires index < index_count
    {
        index // temporary return value
    }

    //compute_committee

    // def compute_committee(indices: Sequence[ValidatorIndex],
    //                   seed: Bytes32,
    //                   index: uint64,
    //                   count: uint64) -> Sequence[ValidatorIndex]:
    // """
    // Return the committee corresponding to ``indices``, ``seed``, ``index``, and committee ``count``.
    // """
    // start = (len(indices) * index) // count
    // end = (len(indices) * uint64(index + 1)) // count
    // return [indices[compute_shuffled_index(uint64(i), uint64(len(indices)), seed)] for i in range(start, end)]
    
    // DEEP DIVE notes:
    // function method compute_committee(indices: seq<ValidatorIndex>, seed: Bytes32, index: uint64, count: uint64) : seq<ValidatorIndex>
    //     requires count > 0
    //     requires index < count
    //     requires 0 < |indices| < 0x10000000000000000
    //     requires |indices|  * index as nat / count as nat  < 0x10000000000000000
    //     requires |indices| * (index as nat +1) / count as nat < 0x10000000000000000
         
    //     ensures 0 < |compute_committee(indices, seed, index, count)| == (|indices| * (index as nat +1)) / count as nat - (|indices| * index as nat) / count as nat <= MAX_VALIDATORS_PER_COMMITTEE as nat
    //     ensures forall e :: e in compute_committee(indices, seed, index, count) ==> e in indices
    // {
    //     var start := (|indices| * index as nat) / count as nat;
    //     var end := (|indices| * (index as nat +1)) / count as nat;
    //     var range := uint64Range(start as uint64, end as uint64);

    //     compute_committee_helper(indices, seed, range)

    // }
    
    function method compute_committee(indices: seq<ValidatorIndex>, seed: Bytes32, index: uint64, count: uint64) : seq<ValidatorIndex>
        requires count > 0
        requires index < count
        requires 0 < |indices| < 0x10000000000000000
        requires |indices|  * index as nat / count as nat  < 0x10000000000000000
        requires |indices| * (index as nat +1) / count as nat < 0x10000000000000000
        requires |indices| * (index as nat +1) / count as nat <= |indices| 
        requires |indices| * (index as nat +1) / count as nat > |indices| * index as nat / count as nat
        requires 0 < (|indices| * (index as nat + 1)) / (count as nat) - (|indices| * index as nat ) / count as nat <= MAX_VALIDATORS_PER_COMMITTEE as nat
        ensures 0 < |compute_committee(indices, seed, index, count)| == (|indices| * (index as nat +1)) / count as nat - (|indices| * index as nat) / count as nat <= MAX_VALIDATORS_PER_COMMITTEE as nat
        ensures forall e :: e in compute_committee(indices, seed, index, count) ==> e in indices
    {
        var start := (|indices| * index as nat) / count as nat;
        var end := (|indices| * (index as nat +1)) / count as nat;
        commonDivRule(|indices| as nat * (index as nat +1), |indices| as nat * index as nat, count as nat);
        
        assert end > start;
        assert end < 0x10000000000000000;
        assert start < 0x10000000000000000;

        //var range := uint64Range(start as uint64, end as uint64);
        var range := range(start, end);

        assert |indices| < 0x10000000000000000;
        assert forall i :: 0 <= i < |range| ==> range[i] as nat < end;
        assert end <= |indices|;
        assert forall i :: 0 <= i < |range| ==> range[i] as nat < |indices|;

        assert end - start == (|indices| * (index as nat +1)) / count as nat - (|indices| * index as nat) / count as nat ;
        assert end - start > 0;
        //assert (end - start) * count as nat == (|indices| * (index as nat +1)) - (|indices| * index as nat) ;
        //assert end - start == |indices| as nat / count as nat;

        compute_committee_helper(indices, seed, range)

    }

    function method compute_committee_helper(indices: seq<ValidatorIndex>, seed: Bytes32, range: seq<nat>) : seq<ValidatorIndex>
        requires |indices| < 0x10000000000000000
        requires forall i :: 0 <= i < |range| ==> range[i] as int < |indices|
        ensures |compute_committee_helper(indices, seed, range)| as nat == |range|
        ensures forall e :: e in compute_committee_helper(indices, seed, range) ==> e in indices
    {
        if |range| == 0 then []
        else [indices[compute_shuffled_index(range[0] as uint64, |indices| as uint64, seed)]] + compute_committee_helper(indices, seed, range[1..])
    }


    
    // //Return the randao mix at a recent ``epoch``.
    // function method get_randao_mix(state: BeaconState, epoch: Epoch): Bytes32
    // {
    //     state.randao_mixes[epoch % EPOCHS_PER_HISTORICAL_VECTOR as uint64]
    // }

     //Return the randao mix at a recent ``epoch``.
    function method get_randao_mix(state: BeaconState, epoch: Epoch): Bytes32
    {
        state.randao_mixes[epoch % EPOCHS_PER_HISTORICAL_VECTOR as uint64]
    }

    // // Return the seed at ``epoch``.
    // function method get_seed(state: BeaconState, epoch: Epoch, domain_type: DomainType): Bytes32
    //     requires epoch as int + EPOCHS_PER_HISTORICAL_VECTOR - MIN_SEED_LOOKAHEAD  - 1 < 0x10000000000000000
    // {
    //     var mix := get_randao_mix(state, (epoch as int + EPOCHS_PER_HISTORICAL_VECTOR - MIN_SEED_LOOKAHEAD - 1) as uint64);  // Avoid underflow
    //     var sb := serialise(domain_type) + serialise(Uint64(epoch as nat)) + serialise(mix);
    //     hash(sb)
    // }
    // Return the seed at ``epoch``.
    function method get_seed(state: BeaconState, epoch: Epoch, domain_type: DomainType): Bytes32
        requires epoch as nat + EPOCHS_PER_HISTORICAL_VECTOR as nat - MIN_SEED_LOOKAHEAD as nat  - 1 < 0x10000000000000000
    {
        var mix := get_randao_mix(state, (epoch as nat + EPOCHS_PER_HISTORICAL_VECTOR as nat - MIN_SEED_LOOKAHEAD as nat - 1) as uint64);  // Avoid underflow
        var sb := serialise(domain_type) + serialise(Uint64(epoch as nat)) + serialise(mix);
        hash(sb)
    }

    //get_beacon_committee

    // def get_beacon_committee(state: BeaconState, slot: Slot, index: CommitteeIndex) -> Sequence[ValidatorIndex]:
    // """
    // Return the beacon committee at ``slot`` for ``index``.
    // """
    // epoch = compute_epoch_at_slot(slot)
    // committees_per_slot = get_committee_count_per_slot(state, epoch)
    // return compute_committee(
    //     indices=get_active_validator_indices(state, epoch),
    //     seed=get_seed(state, epoch, DOMAIN_BEACON_ATTESTER),
    //     index=(slot % SLOTS_PER_EPOCH) * committees_per_slot + index,
    //     count=committees_per_slot * SLOTS_PER_EPOCH,
    // )

    // DEEP DIVE notes: starting code
    // function method get_beacon_committee(s: BeaconState, slot: Slot, index: CommitteeIndex) : seq<ValidatorIndex>
    //     requires index < TWO_UP_6 // this comes from the assert on attestations in process_attestations
    //     requires index < get_committee_count_per_slot(s, compute_epoch_at_slot(slot)) // at most 64 committees per slot 
        
    //     ensures 0 < |get_beacon_committee(s,slot,index)| <= MAX_VALIDATORS_PER_COMMITTEE as nat
    //     ensures forall e :: e in get_beacon_committee(s,slot,index) ==> e as nat < |s.validators|
    // {
    //     var epoch := compute_epoch_at_slot(slot);
    //     var committees_per_slot := get_committee_count_per_slot(s, epoch);
    
    //     compute_committee(
    //         get_active_validator_indices(s.validators, epoch),
    //         get_seed(s, epoch, DOMAIN_BEACON_ATTESTER),
    //         (slot % SLOTS_PER_EPOCH) * committees_per_slot + index,
    //         committees_per_slot * SLOTS_PER_EPOCH
    //     )
    // } 


    function method get_beacon_committee(s: BeaconState, slot: Slot, index: CommitteeIndex) : seq<ValidatorIndex>
        requires TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires index < TWO_UP_6 // this comes from the assert on attestations in process_attestations
        requires index < get_committee_count_per_slot(s, compute_epoch_at_slot(slot)) // at most 64 committees per slot 
        
        ensures 0 < |get_beacon_committee(s,slot,index)| <= MAX_VALIDATORS_PER_COMMITTEE as nat
        ensures forall e :: e in get_beacon_committee(s,slot,index) ==> e as nat < |s.validators|
    {
        var epoch := compute_epoch_at_slot(slot);
        //assert epoch as nat < 0x10000000000000000;

        var committees_per_slot := get_committee_count_per_slot(s, epoch);
        assert 1 <= committees_per_slot <= TWO_UP_6 as uint64;

        assert |get_active_validator_indices(s.validators, epoch)| <= |s.validators|;
        assert forall i :: 0 <= i < |get_active_validator_indices(s.validators, epoch)| ==> 
            get_active_validator_indices(s.validators, epoch)[i] as nat < |s.validators|;
        
        assert 0 <= slot % SLOTS_PER_EPOCH < TWO_UP_5;
        assert 0 <= (slot % SLOTS_PER_EPOCH) * committees_per_slot + index < TWO_UP_11; // i.e. max 31 * 64 + 63
        assert 32 <= committees_per_slot * SLOTS_PER_EPOCH <= TWO_UP_11;

        assert (committees_per_slot * SLOTS_PER_EPOCH) >= ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index);
        assert (committees_per_slot * SLOTS_PER_EPOCH) >= ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index + 1);
        assert |get_active_validator_indices(s.validators, epoch)| < 0x10000000000000000;
        divHelper(|get_active_validator_indices(s.validators, epoch)| as nat, ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index) as nat, (committees_per_slot * SLOTS_PER_EPOCH) as nat);
        divHelper(|get_active_validator_indices(s.validators, epoch)| as nat, ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index + 1) as nat, (committees_per_slot * SLOTS_PER_EPOCH) as nat);
        assert |get_active_validator_indices(s.validators, epoch)| as nat * ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index) as nat / (committees_per_slot * SLOTS_PER_EPOCH) as nat < 0x10000000000000000;
        assert |get_active_validator_indices(s.validators, epoch)| as nat * ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index + 1) as nat / (committees_per_slot * SLOTS_PER_EPOCH) as nat < 0x10000000000000000;
        
        
        divHelper2(|get_active_validator_indices(s.validators, epoch)| as nat, ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index + 1) as nat, (committees_per_slot * SLOTS_PER_EPOCH) as nat);
        assert |get_active_validator_indices(s.validators, epoch)| as nat * ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index + 1) as nat / (committees_per_slot * SLOTS_PER_EPOCH) as nat <= |get_active_validator_indices(s.validators, epoch)| as nat;
    
        //[]

        assert (slot % SLOTS_PER_EPOCH) * committees_per_slot + index < committees_per_slot * SLOTS_PER_EPOCH;
        assert TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat;
        //assert 0 <= slot % SLOTS_PER_EPOCH < SLOTS_PER_EPOCH;
        getBeaconCommitteeLemma(|get_active_validator_indices(s.validators, epoch)|, committees_per_slot as nat, (slot % SLOTS_PER_EPOCH) as nat, index as nat);
        proveActiveValidatorsSatisfyBounds(|get_active_validator_indices(s.validators, epoch)|, committees_per_slot as nat, (slot % SLOTS_PER_EPOCH) as nat, index as nat);
        //assert len_indices as nat * ((slot * CPS + cIndex) as nat + 1) / (CPS as nat * SLOTS_PER_EPOCH as nat) > len_indices as nat * (slot * CPS + cIndex) as nat / (CPS as nat * SLOTS_PER_EPOCH as nat);

        compute_committee(
            get_active_validator_indices(s.validators, epoch),
            get_seed(s, epoch, DOMAIN_BEACON_ATTESTER),
            (slot % SLOTS_PER_EPOCH) * committees_per_slot + index,
            committees_per_slot * SLOTS_PER_EPOCH
        )
    } 

    
       

}