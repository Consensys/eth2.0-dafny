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

//  @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /timeLimit:100 /noCheating:0


include "../utils/Eth2Types.dfy"
include "../utils/MathHelpers.dfy"
include "../utils/NativeTypes.dfy"
include "../utils/SetHelpers.dfy"
include "../utils/Helpers.dfy"

include "../ssz/Constants.dfy"
include "../ssz/Serialise.dfy"

include "BeaconChainTypes.dfy"
include "Helpers.s.dfy"
include "ActiveValidatorBounds.p.dfy"
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
    import opened SetHelpers
    import opened Helpers


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


    function method get_total_slashings(slashings: seq<Gwei>): Gwei
    {
        if |slashings| == 0 then 0 as Gwei
        else 
            assume slashings[0] as nat + get_total_slashings(slashings[1..]) as nat < 0x10000000000000000;
            slashings[0] + get_total_slashings(slashings[1..])
    }

// Helpers - Rewards and penalties

    function method integer_square_root(n:uint64) : uint64
        requires n < 0xFFFFFFFFFFFFFFFF;
        ensures power2(integer_square_root(n) as nat) <= n as nat;
        //ensures !(exists x' {:trigger power(x' as nat,2)} :: x'>x && power(x' as nat,2) <= n as nat)
    
    function method get_base_reward(s: BeaconState, index: ValidatorIndex) : Gwei
        requires index as int < |s.validators|
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires s.validators[index].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000
    {
        var total_balance : Gwei := get_total_active_balance_full(s);
        var effective_balance : Gwei := s.validators[index].effective_balance;

        (EFFECTIVE_BALANCE_INCREMENT as int * BASE_REWARD_FACTOR as int / integer_square_root(total_balance) as int) as Gwei 
    }

    function method get_proposer_reward(state: BeaconState, attesting_index: ValidatorIndex): Gwei
        requires attesting_index as int < |state.validators|
        requires get_total_active_balance_full(state) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(state)) > 1
        requires state.validators[attesting_index].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(state)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000
    {
        (get_base_reward(state, attesting_index) / PROPOSER_REWARD_QUOTIENT) as Gwei  
    }
    
    function method get_finality_delay(state: BeaconState): uint64
        requires get_previous_epoch(state) >= state.finalised_checkpoint.epoch
    {
        get_previous_epoch(state) - state.finalised_checkpoint.epoch
    }
     
    predicate method is_in_inactivity_leak(state: BeaconState)
        requires get_previous_epoch(state) >= state.finalised_checkpoint.epoch
    {
        get_finality_delay(state) > MIN_EPOCHS_TO_INACTIVITY_PENALTY
    }
    
    function method get_eligible_validator_indices(state: BeaconState): seq<ValidatorIndex>
        ensures forall i :: 0 <= i < |get_eligible_validator_indices(state)|  
            ==> get_eligible_validator_indices(state)[i] as nat < |state.validators|
    {
        var previous_epoch := get_previous_epoch(state);
        get_eligible_validator_indices_helper(state.validators, previous_epoch)
        //     return [
        //         ValidatorIndex(index) for index, v in enumerate(state.validators)
        //         if is_active_validator(v, previous_epoch) or (v.slashed and previous_epoch + 1 < v.withdrawable_epoch)
        //     ]
    }

    function method get_eligible_validator_indices_helper(v: ListOfValidators, previous_epoch: Epoch): seq<ValidatorIndex>
        ensures forall i :: 0 <= i < |get_eligible_validator_indices_helper(v, previous_epoch)|  
            ==> get_eligible_validator_indices_helper(v, previous_epoch)[i] as nat < |v|
    {
        if |v| == 0 then []
        else 
            if is_active_validator(v[|v|-1], previous_epoch) || (v[|v|-1].slashed && (previous_epoch as int + 1 < v[|v|-1].withdrawable_epoch as int)) then
                get_eligible_validator_indices_helper(v[..|v|-1], previous_epoch) + [(|v|-1) as ValidatorIndex]
            else 
                get_eligible_validator_indices_helper(v[..|v|-1], previous_epoch)
    }

    //datatype RewardsAndPenalties = rewardsAndPenalties(rewards: seq<Gwei>, penalties: seq<Gwei>)

    /** Helper with shared logic for use by get source, target, and head deltas functions */

    //Components of attestation deltas

    // Return attester micro-rewards/penalties for source-vote for each validator.
    function method get_source_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s)

        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        ensures |get_source_deltas(s).0| == |get_source_deltas(s).1| == |s.validators|
    {
        var matching_source_attestations := get_matching_source_attestations(s, get_previous_epoch(s));

        get_attestation_component_deltas(s, matching_source_attestations)
    }

    // Return attester micro-rewards/penalties for target-vote for each validator.
    function method get_target_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        requires get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat
        //requires s.slot - get_previous_epoch(s) *  SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT  // equivalent to above requires

        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s)
        requires 1 <= get_previous_epoch(s) <= get_current_epoch(s)

        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        ensures |get_target_deltas(s).0| == |get_target_deltas(s).1| == |s.validators|
    {
        var matching_target_attestations := get_matching_target_attestations(s, get_previous_epoch(s));

        get_attestation_component_deltas(s, matching_target_attestations)
    }


    // def get_head_deltas(state: BeaconState) -> Tuple[Sequence[Gwei], Sequence[Gwei]]:
    // """
    // Return attester micro-rewards/penalties for head-vote for each validator.
    // """
    // matching_head_attestations = get_matching_head_attestations(state, get_previous_epoch(state))
    // return get_attestation_component_deltas(state, matching_head_attestations)
    function method get_head_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        requires get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat
        //requires s.slot - get_previous_epoch(s) *  SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT  // equivalent to above requires
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s)
        requires 1 <= get_previous_epoch(s) <= get_current_epoch(s)

        requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        ensures |get_head_deltas(s).0| == |get_head_deltas(s).1| == |s.validators|
    {
        var matching_head_attestations := get_matching_head_attestations(s, get_previous_epoch(s));
        get_attestation_component_deltas(s, matching_head_attestations)
    }

    // def get_inclusion_delay_deltas(state: BeaconState) -> Tuple[Sequence[Gwei], Sequence[Gwei]]:
    // """
    // Return proposer and inclusion delay micro-rewards/penalties for each validator.
    // """
    // rewards = [Gwei(0) for _ in range(len(state.validators))]
    // matching_source_attestations = get_matching_source_attestations(state, get_previous_epoch(state))

    // for index in get_unslashed_attesting_indices(state, matching_source_attestations):
    //     attestation = min([
    //         a for a in matching_source_attestations
    //         if index in get_attesting_indices(state, a.data, a.aggregation_bits)
    //     ], key=lambda a: a.inclusion_delay)
    //     rewards[attestation.proposer_index] += get_proposer_reward(state, index)
    //     max_attester_reward = Gwei(get_base_reward(state, index) - get_proposer_reward(state, index))
    //     rewards[index] += Gwei(max_attester_reward // attestation.inclusion_delay)

    // # No penalties associated with inclusion delay
    // penalties = [Gwei(0) for _ in range(len(state.validators))]
    // return rewards, penalties

    function method get_inclusion_delay_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1

        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
        
        ensures |get_inclusion_delay_deltas(s).0| == |get_inclusion_delay_deltas(s).1| == |s.validators|
    {
        var rewards : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var penalties : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);

        var matching_source_attestations := get_matching_source_attestations(s, get_previous_epoch(s));
        var unslashed_attesting_indices := get_unslashed_attesting_indices(s, matching_source_attestations);

        // resolve the following assume at a later date i.e. look at the bound for effectBalance as part of the proof required
        assume forall i :: i in unslashed_attesting_indices ==> s.validators[i].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000;
  
        get_inclusion_delay_deltas_helper(s, unslashed_attesting_indices, matching_source_attestations, rewards, penalties)

    }

    function method get_inclusion_delay_deltas_helper(s: BeaconState, unslashed_attesting_indices: set<ValidatorIndex>, matching_source_attestations: seq<PendingAttestation>, rewards: seq<Gwei>, penalties: seq<Gwei>) : (seq<Gwei>,seq<Gwei>)
        requires |rewards| == |penalties| == |s.validators|
        requires forall i :: i in unslashed_attesting_indices ==> i as int < |s.validators|
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires forall i :: i in unslashed_attesting_indices ==> 
                s.validators[i as nat].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000

        ensures |get_inclusion_delay_deltas_helper(s, unslashed_attesting_indices, matching_source_attestations, rewards, penalties).0| == |rewards| == |s.validators|
        ensures |get_inclusion_delay_deltas_helper(s, unslashed_attesting_indices, matching_source_attestations, rewards, penalties).1| == |penalties| == |s.validators|
    
    {
        if unslashed_attesting_indices == {} then (rewards, penalties)
        else
            var index := PickIndex(unslashed_attesting_indices);
            var attestation := get_min_attestation(matching_source_attestations, index);
            assume attestation.proposer_index as nat < |rewards|;
            assume (rewards[attestation.proposer_index as nat] as nat + get_proposer_reward(s, index) as nat) < 0x10000000000000000; 
            var rewards' := rewards[attestation.proposer_index as nat := (rewards[attestation.proposer_index as nat] as nat + get_proposer_reward(s, index) as nat) as Gwei];
            var penalties' := penalties;
            
            assume get_base_reward(s, index) > get_proposer_reward(s, index);
            // or set to 0
            var max_attester_reward := get_base_reward(s, index) - get_proposer_reward(s, index);
            assume attestation.inclusion_delay > 0;
            assume (rewards'[index as nat] as nat + max_attester_reward as nat / attestation.inclusion_delay as nat) < 0x10000000000000000;

            assert |rewards'| == |rewards|;
            assert |penalties'| == |penalties|;
            get_inclusion_delay_deltas_helper(s, unslashed_attesting_indices - {index}, matching_source_attestations, rewards'[index as nat := (rewards'[index as nat] as nat
                                            + max_attester_reward as nat / attestation.inclusion_delay as nat) as Gwei], penalties)

    }

    function method get_min_attestation(sa : seq<PendingAttestation>, index: ValidatorIndex) : PendingAttestation
        

    // def get_inactivity_penalty_deltas(state: BeaconState) -> Tuple[Sequence[Gwei], Sequence[Gwei]]:
    // """
    
    // """
    // penalties = [Gwei(0) for _ in range(len(state.validators))]
    // if is_in_inactivity_leak(state):
    //     matching_target_attestations = get_matching_target_attestations(state, get_previous_epoch(state))
    //     matching_target_attesting_indices = get_unslashed_attesting_indices(state, matching_target_attestations)
    //     for index in get_eligible_validator_indices(state):
    //         # If validator is performing optimally this cancels all rewards for a neutral balance
    //         base_reward = get_base_reward(state, index)
    //         penalties[index] += Gwei(BASE_REWARDS_PER_EPOCH * base_reward - get_proposer_reward(state, index))
    //         if index not in matching_target_attesting_indices:
    //             effective_balance = state.validators[index].effective_balance
    //             penalties[index] += Gwei(effective_balance * get_finality_delay(state) // INACTIVITY_PENALTY_QUOTIENT)

    // # No rewards associated with inactivity penalties
    // rewards = [Gwei(0) for _ in range(len(state.validators))]
    // return rewards, penalties

    // Return inactivity reward/penalty deltas for each validator.
    function method get_inactivity_penalty_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        requires get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat
        requires s.slot - get_previous_epoch(s) *  SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT 
        requires 1 <= get_previous_epoch(s) <= get_current_epoch(s)
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1

        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
        
        ensures |get_inactivity_penalty_deltas(s).0| == |get_inactivity_penalty_deltas(s).1| == |s.validators|
    {
        var rewards : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var penalties : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);

        if (is_in_inactivity_leak(s)) then
            var matching_target_attestations := get_matching_target_attestations(s, get_previous_epoch(s));
            var matching_target_attesting_indices := get_unslashed_attesting_indices(s, matching_target_attestations);
            var eligible_validator_indices := get_eligible_validator_indices(s);
            assert forall i :: 0 <= i < |eligible_validator_indices| ==> eligible_validator_indices[i] as nat < |s.validators|;
        
            assume forall i :: 0 <= i < |eligible_validator_indices| ==> s.validators[eligible_validator_indices[i] as nat].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000;
   
            get_inactivity_penalty_deltas_helper(s, eligible_validator_indices, matching_target_attesting_indices, rewards, penalties)
        else    
            (rewards,penalties)
        
    }

    function method get_inactivity_penalty_deltas_helper(s: BeaconState, 
                                                    eligible_indices: seq<ValidatorIndex>, 
                                                    target_indices: set<ValidatorIndex>,
                                                    rewards: seq<Gwei>,
                                                    penalties: seq<Gwei>)  
                                                : (seq<Gwei>,seq<Gwei>)
        requires |rewards| == |penalties| == |s.validators|
        requires forall i :: 0 <= i < |eligible_indices| ==> eligible_indices[i] as nat < |s.validators|
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires forall i :: 0 <= i < |eligible_indices| ==> s.validators[eligible_indices[i] as nat].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch

         ensures |get_inactivity_penalty_deltas_helper(s, eligible_indices, target_indices, rewards, penalties).0| == |rewards| == |s.validators|
        ensures |get_inactivity_penalty_deltas_helper(s, eligible_indices, target_indices, rewards, penalties).1| == |penalties| == |s.validators|
    {
        if |eligible_indices| == 0 then (rewards, penalties)
        else
            var base_reward := get_base_reward(s,eligible_indices[0]);
            var first_part_of_penalty := (BASE_REWARDS_PER_EPOCH * base_reward - get_proposer_reward(s, eligible_indices[0])) as Gwei;

            var rewards' := rewards;
            assert |rewards'| == |rewards|;
            

            if eligible_indices[0] !in target_indices then
                var effective_balance := s.validators[eligible_indices[0] as nat].effective_balance;
                assume INACTIVITY_PENALTY_QUOTIENT as nat > 0;
                assume (effective_balance as nat * get_finality_delay(s) as nat / INACTIVITY_PENALTY_QUOTIENT as nat) < 0x10000000000000000;
                var second_part_of_penalty := (effective_balance as nat * get_finality_delay(s) as nat / INACTIVITY_PENALTY_QUOTIENT as nat) as Gwei;
                
                assume (penalties[eligible_indices[0] as nat] as nat + first_part_of_penalty as nat + second_part_of_penalty as nat) < 0x10000000000000000;
                var penalties' := penalties[eligible_indices[0] as nat := (penalties[eligible_indices[0] as nat] as nat + first_part_of_penalty as nat + second_part_of_penalty as nat) as Gwei];
                assert |penalties'| == |penalties|;

                get_inactivity_penalty_deltas_helper(s, eligible_indices[1..], target_indices, rewards', penalties')
            else
                assume penalties[eligible_indices[0] as nat] as nat + first_part_of_penalty as nat < 0x10000000000000000;
                var penalties' := penalties[eligible_indices[0] as nat := (penalties[eligible_indices[0] as nat] as nat + first_part_of_penalty as nat) as Gwei];
                assert |penalties'| == |penalties|;
                get_inactivity_penalty_deltas_helper(s, eligible_indices[1..], target_indices, rewards', penalties')
            
    }


    
    // Helper with shared logic for use by get source, target, and head deltas functions
    function method get_attestation_component_deltas(s: BeaconState, attestations: seq<PendingAttestation>) : (seq<Gwei>,seq<Gwei>)
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s) 

        requires forall a :: a in attestations ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in attestations ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 

        ensures |get_attestation_component_deltas(s, attestations).0| == |get_attestation_component_deltas(s, attestations).1| == |s.validators|
        
    {
        var rewards : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var penalties : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var total_balance := get_total_active_balance_full(s);
        var unslashed_attesting_indices := get_unslashed_attesting_indices(s, attestations);
        var attesting_balance := get_total_balance(s, unslashed_attesting_indices);
        var indices := get_eligible_validator_indices(s);

        assert forall i :: 0 <= i < |indices| ==> indices[i] as nat < |s.validators|;

        // resolve the following assume at a later date i.e. look at the bound for effectBalance as part of the proof required
        assume forall i :: 0 <= i < |indices| ==> s.validators[indices[i]].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000;
  
        
        get_attestation_component_deltas_helper(s, indices, total_balance, unslashed_attesting_indices, attesting_balance, rewards, penalties)
        
    }

    function method get_attestation_component_deltas_helper(s: BeaconState, 
                                                    indices: seq<ValidatorIndex>, 
                                                    total_balance: Gwei,
                                                    unslashed_attesting_indices: set<ValidatorIndex>,
                                                    attesting_balance: Gwei,
                                                    rewards: seq<Gwei>,
                                                    penalties: seq<Gwei>)  
                                                : (seq<Gwei>,seq<Gwei>)
        requires |rewards| == |penalties| == |s.validators|
        requires EFFECTIVE_BALANCE_INCREMENT <= total_balance 
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        requires forall i :: 0 <= i < |indices| ==> indices[i] as nat < |s.validators|
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires forall i :: 0 <= i < |indices| ==> s.validators[indices[i]].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000
     
        ensures |get_attestation_component_deltas_helper(s, indices, total_balance, unslashed_attesting_indices, attesting_balance, rewards, penalties).0| == |rewards| == |s.validators|
        ensures |get_attestation_component_deltas_helper(s, indices, total_balance, unslashed_attesting_indices, attesting_balance, rewards, penalties).1| == |penalties| == |s.validators|
    {
        if |indices| == 0 then (rewards, penalties)
        else
            var index := indices[0];
            assert index as nat < |s.validators|;
            assert integer_square_root(get_total_active_balance_full(s)) > 1;
            assert s.validators[index].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000;

            if index in unslashed_attesting_indices then
                var increment := EFFECTIVE_BALANCE_INCREMENT;
                var rewards_numerator :=  get_base_reward(s, index) as nat * (attesting_balance as nat / increment as nat); // this is moved above the else branch to faciliate the related assume statement

                assert (total_balance as nat / increment as nat) >= 1;
                // resolve the following assume at a later date i.e. look at the bounds for each component
                assume rewards_numerator > 0;
                assume rewards[index as nat] as nat + get_base_reward(s, index) as nat < 0x10000000000000000;
                assume rewards[index as nat] as nat + rewards_numerator / (total_balance as nat / increment as nat) < 0x10000000000000000;
                
                if is_in_inactivity_leak(s) then   
                    //(rewards[indices[0] := rewards[indices[0]] + get_base_reward(s, indices[0])], penalties)
                    get_attestation_component_deltas_helper(s, indices[1..], total_balance, unslashed_attesting_indices, attesting_balance, rewards[index as nat := (rewards[index as nat] as nat + get_base_reward(s, index) as nat) as Gwei], penalties)
                else
                    //  var rewards_numerator :=  get_base_reward(s, index) * (attesting_balance / increment); 
                    //(rewards[indices[0] := rewards[indices[0]] + rewards_numerator / (total_balance / increment)], penalties)
                    get_attestation_component_deltas_helper(s, indices[1..], total_balance, unslashed_attesting_indices, attesting_balance, rewards[index as nat := (rewards[index as nat] as nat + rewards_numerator / (total_balance as nat / increment as nat)) as Gwei], penalties)
            else
                // resolve the following assume at a later date i.e. look at the bounds for each component
                assume penalties[index as nat] as nat + get_base_reward(s, index) as nat < 0x10000000000000000;

                //(rewards, penalties[indices[0] := penalties[indices[0]] + get_base_reward(s, indices[0])])
                get_attestation_component_deltas_helper(s, indices[1..], total_balance, unslashed_attesting_indices, attesting_balance, rewards, penalties[index as nat := (penalties[index as nat] as nat + get_base_reward(s, index) as nat) as Gwei])

    }
    
    
    // def get_attestation_deltas(state: BeaconState) -> Tuple[Sequence[Gwei], Sequence[Gwei]]:
    // """
    // Return attestation reward/penalty deltas for each validator.
    // """
    // source_rewards, source_penalties = get_source_deltas(state)
    // target_rewards, target_penalties = get_target_deltas(state)
    // head_rewards, head_penalties = get_head_deltas(state)
    // inclusion_delay_rewards, _ = get_inclusion_delay_deltas(state)
    // _, inactivity_penalties = get_inactivity_penalty_deltas(state)

    // rewards = [
    //     source_rewards[i] + target_rewards[i] + head_rewards[i] + inclusion_delay_rewards[i]
    //     for i in range(len(state.validators))
    // ]

    // penalties = [
    //     source_penalties[i] + target_penalties[i] + head_penalties[i] + inactivity_penalties[i]
    //     for i in range(len(state.validators))
    // ]

    // return rewards, penalties
    function method get_attestation_deltas(s: BeaconState) : (seq<Gwei>, seq<Gwei>)
        //requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        //requires integer_square_root(get_total_active_balance_full(s)) > 1
        //requires get_total_active_balance_full(s) > 1
        //requires EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s)

        //requires get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat
        requires 1 <= get_previous_epoch(s) //<= get_current_epoch(s)
        // i.e. this means it isn't applicable to the GENESIS_EPOCH

        requires forall a :: a in s.previous_epoch_attestations ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in s.previous_epoch_attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in s.previous_epoch_attestations ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 


        // requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        // requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        // requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        // requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        // requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        // requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        // requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        // requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        // requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        ensures |get_attestation_deltas(s).0| == |get_attestation_deltas(s).1| == |s.validators|
    {
        //assert forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> a in s.previous_epoch_attestations;
        // assert forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6;
        // assert forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat; 
        // assert forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat ;
    
        // assert forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6;
        // assert forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat ;
        // assert forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat; 
    
        // assert forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6;
        // assert forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat ;
        // assert forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat ;
    
        
        var rewards : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var penalties : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        
        assume get_previous_epoch(s) >= s.finalised_checkpoint.epoch;
        assert EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s);

        assume get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF;
        assume integer_square_root(get_total_active_balance_full(s)) > 1; // ie as EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s)
        assert get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat;
        
        var (sr, sp) := get_source_deltas(s);
        var (tr, tp) := get_target_deltas(s);
        var (hr, hp) := get_head_deltas(s);
        var (ddr, ddp) := get_inclusion_delay_deltas(s);
        var (pdr, pdp) := get_inactivity_penalty_deltas(s);

        assert |sr| == |tr| == |hr| == |ddr| == |pdr| == |s.validators|;
        assert |sp| == |tp| == |hp| == |ddp| == |pdp| == |s.validators|;

        (get_attestation_deltas_helper_sum_rewards(sr, tr, hr, ddr, pdr, rewards),
         get_attestation_deltas_helper_sum_penalties(sp, tp, hp, ddp, pdp, penalties))

    }

    function method get_attestation_deltas_helper_sum_rewards(sr: seq<Gwei>, tr: seq<Gwei>, hr: seq<Gwei>, ddr: seq<Gwei>, pdr: seq<Gwei>, rewards: seq<Gwei>) : seq<Gwei>
        requires |sr| == |tr| == |hr| == |ddr| == |pdr| <= |rewards|
        ensures |get_attestation_deltas_helper_sum_rewards(sr, tr, hr, ddr, pdr, rewards)| == |rewards|
    {
        if |sr| == 0 then rewards
        else    
            assume rewards[0] as nat + sr[0] as nat + tr[0] as nat + hr[0] as nat + ddr[0] as nat + pdr[0] as nat < 0x10000000000000000;
            get_attestation_deltas_helper_sum_rewards(sr[1..], tr[1..], hr[1..], ddr[1..], pdr[1..], rewards[0 := rewards[0] + sr[0] + tr[0] + hr[0] + ddr[0] + pdr[0]])
    }

    function method get_attestation_deltas_helper_sum_penalties(sp: seq<Gwei>, tp: seq<Gwei>, hp: seq<Gwei>, ddp: seq<Gwei>, pdp: seq<Gwei>, penalties: seq<Gwei>) : seq<Gwei>
        requires |sp| == |tp| == |hp| == |ddp| == |pdp| <= |penalties|
        ensures |get_attestation_deltas_helper_sum_penalties(sp, tp, hp, ddp, pdp, penalties)| == |penalties|
    {
        if |sp| == 0 then penalties
        else    
            assume penalties[0] as nat + sp[0] as nat + tp[0] as nat + hp[0] as nat + ddp[0] as nat + pdp[0] as nat  < 0x10000000000000000;
            get_attestation_deltas_helper_sum_penalties(sp[1..], tp[1..], hp[1..], ddp[1..], pdp[1..], penalties[0 := penalties[0] + sp[0] + tp[0] + hp[0] + ddp[0] + pdp[0]])
    }


    

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
        slashValidatorPreservesActiveValidators(s, slashed_index, whistleblower_index);
    }

    // ?? prove that the only way slashed is set to true is by calling slash_validator?? 
    
    lemma slashValidatorPreservesActiveValidators(s: BeaconState, slashed_index: ValidatorIndex, whistleblower_index: ValidatorIndex)
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


    // function method  get_total_balance(state: BeaconState, indices: set<ValidatorIndex>) : Gwei
    // """
    // Return the combined effective balance of the ``indices``.
    // ``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum to avoid divisions by zero.
    // Math safe up to ~10B ETH, afterwhich this overflows uint64.
    // """
    // {
        // return Gwei(max(EFFECTIVE_BALANCE_INCREMENT, sum([state.validators[index].effective_balance for index in indices])));
        //  for now we return the size of indices
        // |indices| as Gwei 
    // }


    function method get_total_balance_seq(s: BeaconState, indices: seq<ValidatorIndex>) : Gwei
        requires forall i :: 0 <= i < |indices| ==> indices[i] as nat < |s.validators|
        ensures EFFECTIVE_BALANCE_INCREMENT <= get_total_balance_seq(s, indices)

    {
        max(EFFECTIVE_BALANCE_INCREMENT as nat, get_total_balance_seq_helper(s, indices) as nat) as Gwei
    }

    function method get_total_balance_seq_helper(s: BeaconState, indices: seq<ValidatorIndex>) : Gwei
        requires forall i :: 0 <= i < |indices| ==> indices[i] as nat < |s.validators|
    {
        if |indices| == 0 then 0 as Gwei
        else
            assume s.validators[indices[0]].effective_balance as nat + get_total_balance_seq_helper(s, indices[1..]) as nat < 0x10000000000000000;
            s.validators[indices[0]].effective_balance + get_total_balance_seq_helper(s, indices[1..]) 
    }

    function method get_total_balance(s: BeaconState, indices: set<ValidatorIndex>) : Gwei
        requires forall i : ValidatorIndex :: i in indices ==> i as nat < |s.validators|

    {
        max(EFFECTIVE_BALANCE_INCREMENT as nat, get_total_balance_helper(s, indices) as nat) as Gwei
    }

    function method get_total_balance_helper(s: BeaconState, indices: set<ValidatorIndex>) : Gwei
        requires forall i : ValidatorIndex :: i in indices ==> i as nat < |s.validators|
    {
        if |indices| == 0 then 0 as Gwei
        else
            var y := PickIndex(indices);
            assume s.validators[y].effective_balance as nat + get_total_balance_helper(s, indices - {y}) as nat < 0x10000000000000000;
            s.validators[y].effective_balance + get_total_balance_helper(s, indices - {y}) 
    }

    function method PickIndex(s: set<ValidatorIndex>): ValidatorIndex
        requires s != {}
    {
        HasMinimum(s);
        var z :| z in s && forall y :: y in s ==> z as nat <= y as nat;
        z
    }

    lemma HasMinimum(s: set<ValidatorIndex>)
        requires s != {}
        ensures exists z :: z in s && forall y :: y in s ==> z <= y
        // Ref: https://stackoverflow.com/questions/51207795/the-hilbert-epsilon-operator
    {
        var z :| z in s;
        if s == {z} {
            // the mimimum of a singleton set is its only element
        } else if forall y :: y in s ==> z <= y {
            // we happened to pick the minimum of s
        } else {
            // s-{z} is a smaller, nonempty set and it has a minimum
            var s' := s - {z};
            HasMinimum(s');
            var z' :| z' in s' && forall y :: y in s' ==> z' <= y;
            // the minimum of s' is the same as the miminum of s
            forall y | y in s
            ensures z' <= y
            {
            if
            case y in s' =>
                assert z' <= y;  // because z' in minimum in s'
            case y == z =>
                var k :| k in s && k < z;  // because z is not minimum in s
                assert k in s';  // because k != z
            }
        }
    }

    function method get_total_active_balance(state: BeaconState) : Gwei
        // requires |state.validators| < 0x10000000000000000
    // """
    // Return the combined effective balance of the active validators.
    // Note: ``get_total_balance`` returns ``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum to avoid divisions by zero.
    // """
    {
        // get_total_balance(state, set(get_active_validator_indices(state, get_current_epoch(state))))
        assert(|state.validators| < 0x10000000000000000);
        |state.validators| as uint64
    }

    function method get_total_active_balance_full(s: BeaconState) : Gwei
        // requires |state.validators| < 0x10000000000000000
        ensures EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s) 
    // """
    // Return the combined effective balance of the active validators.
    // Note: ``get_total_balance`` returns ``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum to avoid divisions by zero.
    // """
    {
        get_total_balance_seq(s, get_active_validator_indices(s.validators, get_current_epoch(s)))
    }

/**
     *  The number of attestations for a pair of checkpoints.
     *  
     *  @param  xa  The known list of attestations (votes).
     *  @param  src A checkpoint.
     *  @param  tgt A checkpoint.
     *  @returns    The number of votes for src --> tgt in `xa`.
     */
    function method countAttestationsForLink(xa : seq<PendingAttestation>, src : CheckPoint, tgt: CheckPoint) : nat
        ensures countAttestationsForLink(xa, src, tgt) <= |xa|
        decreases xa
    {
        if |xa| == 0 then 
            0
        else 
            (if xa[0].data.source == src && xa[0].data.target == tgt then 
                1

            else 
                0
            ) + countAttestationsForLink(xa[1..], src, tgt)
    }

    
    
    /**
     *  The set of validators attesting to a target is larger than the set 
     *  of validators attesting to a link with that target. 
     *
     *  @param  xa      A seq of attestations.
     *  @param  src     The source checkpoint of the link.
     *  @param  tgt     The target checkpoint of the link.
     */
    lemma {:induction xa} attForTgtLargerThanLinks(xa : seq<PendingAttestation>, src : CheckPoint, tgt: CheckPoint)
        ensures collectValidatorsAttestatingForLink(xa, src, tgt) <= collectValidatorsIndicesAttestatingForTarget(xa, tgt) 
        ensures |collectValidatorsAttestatingForLink(xa, src, tgt)| <= |collectValidatorsIndicesAttestatingForTarget(xa, tgt)| 
    {
        assert(collectValidatorsAttestatingForLink(xa, src, tgt) <= collectValidatorsIndicesAttestatingForTarget(xa, tgt) );
        cardIsMonotonic(collectValidatorsAttestatingForLink(xa, src, tgt), collectValidatorsIndicesAttestatingForTarget(xa, tgt));
    }

    /**
     *  @param  state   A beacon state.
     *  @param  epoch   An epoch which is either the state's epoch ior the previous one.
     *  @returns        The current (resp. previous) list of attestations if epoch is 
     *                  state's epoch (resp. epoch before state's epoch). 
     *  @note           The function name is misleading as it seems to be a counter-part
     *                  or symmetric of `get_matching_target_attestations` but it is not.
     *                  Moreover it does not perform any matching as the name indicates,
     *                  and the matching/filtering is done in `get_matching_target_attestations`.
     *                  A better name may be `get_attestations_at_epoch`.
     *  @note           An even better solution would be to remove this function 
     *                  and directly `use state.current_epoch_attestations` or 
     *                  `state.previous_epoch_attestations` in the callers.
     */
    function method get_matching_source_attestations(state: BeaconState, epoch: Epoch) : seq<PendingAttestation>
        //  report? -> meaning of i in (a, b)? seems to be closed interval ...
        requires get_previous_epoch(state) <= epoch <= get_current_epoch(state)
        ensures |get_matching_source_attestations(state, epoch)| < 0x10000000000000000

        // this property will be assumed for the moment
        //ensures forall i :: 0 <= i < |get_matching_source_attestations(state, epoch)| 
        //    ==> get_matching_source_attestations(state, epoch)[i].data.index 
        //        < get_committee_count_per_slot(state, compute_epoch_at_slot(get_matching_source_attestations(state, epoch)[i].data.slot)) <= TWO_UP_6
    {
        // assert epoch in (get_previous_epoch(state), get_current_epoch(state))
        // return state.current_epoch_attestations if epoch == get_current_epoch(state) else state.previous_epoch_attestations
        if epoch == get_current_epoch(state) then
            state.current_epoch_attestations
        else 
            state.previous_epoch_attestations
    }  

    /**
     *  @param  state   A beacon state.
     *  @param  epoch   An epoch which is either the state's epoch or the previous one.
     *  @returns        Attestations at epoch with a target that is the block root
     *                  recorded for that epoch.         
     *
     *  @note           This function does not check the epoch of the source attestation.
     *                  As a result if the seq of attestations in   
     *                  `state.previous/current_epoch_attestations` contains the same 
     *                  block root at different epochs, all the attestations will be collect.
     *                  However the following note seems to suggest that this cannot happen.
     *
     *  @note           From the eth2.0 specs: When processing attestations, we already only *                  accept attestations that have the correct Casper FFG source checkpoint 
     *                  (specifically, the most recent justified checkpoint that the chain 
     *                  knows about). The goal of this function is to get all attestations 
     *                  that have a correct Casper FFG source. Hence, it can safely just 
     *                  return all the PendingAttestations for the desired epoch 
     *                  (current or previous).
     *  @note           The claim "it can safely just return all the PendingAttestations for 
     *                  the desired epoch (current or previous)." is valid only if all the 
     *                  attestations in `state.previous/current_epoch_attestations`
     *                  are well-formed. 
     *  @todo           We should add this constraint to the pre-conditions of this function.
     */
    function method get_matching_target_attestations(state: BeaconState, epoch: Epoch) : seq<PendingAttestation>
        requires epoch as nat *  SLOTS_PER_EPOCH as nat  <  state.slot as nat
        requires state.slot - epoch *  SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT 
        requires 1 <= get_previous_epoch(state) <= epoch <= get_current_epoch(state)
        // requires 

        ensures |get_matching_target_attestations(state, epoch)| < 0x10000000000000000
        ensures forall a :: a in get_matching_target_attestations(state, epoch) ==>
                    a.data.target.root == get_block_root(state, epoch)

        ensures var e := get_previous_epoch(state);
            epoch == e ==> 
                get_matching_target_attestations(state, e) == 
                filterAttestations(state.previous_epoch_attestations, get_block_root(state, e))
        ensures var e := get_current_epoch(state);
            epoch == e ==> 
                get_matching_target_attestations(state, e) == 
                filterAttestations(state.current_epoch_attestations, get_block_root(state, e))
        decreases epoch //  seems needed to prove last two post-conds
    {
        //  Get attestattions at epoch as recorded in state (previous epoch or current epoch).
        var ax := get_matching_source_attestations(state, epoch);
        //  Collect attestations for (i.e. with target equal to) block root at epoch
        filterAttestations(ax, get_block_root(state, epoch))
    }

    function method get_matching_head_attestations(state: BeaconState, epoch: Epoch) : seq<PendingAttestation>
        requires epoch as nat *  SLOTS_PER_EPOCH as nat  <  state.slot as nat
        requires state.slot - epoch *  SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT 
        requires 1 <= get_previous_epoch(state) <= epoch <= get_current_epoch(state)
        
        ensures |get_matching_head_attestations(state, epoch)| < 0x10000000000000000
        ensures forall a :: a in get_matching_head_attestations(state, epoch) ==>
                    a.data.slot < state.slot &&
                    state.slot - a.data.slot <= SLOTS_PER_HISTORICAL_ROOT &&
                    a.data.beacon_block_root == get_block_root_at_slot(state, a.data.slot)

    {
        var ax := get_matching_target_attestations(state, epoch);
        filterAttestationsyy(ax, state)
    }
    

    function method get_attesting_balance(state: BeaconState, attestations: seq<PendingAttestation>) : Gwei 
        requires |attestations| < 0x10000000000000000
    // """
    // Return the combined effective balance of the set of unslashed validators participating in ``attestations``.
    // Note: ``get_total_balance`` returns ``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum to avoid divisions by zero.
    // """
    {
        // get_total_balance(state, get_unslashed_attesting_indices(state, attestations))
        |attestations| as Gwei 
    }

    function method get_unslashed_attesting_indices(s: BeaconState, attestations: seq<PendingAttestation>): set<ValidatorIndex>
        //requires forall i :: 0 <= i < |attestations| ==> attestations[i].data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(attestations[i].data.slot)) <= TWO_UP_6
        requires forall a :: a in attestations ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in attestations ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 

        ensures forall i  :: i in get_unslashed_attesting_indices(s, attestations) ==> i as nat < |s.validators|
    {
        if |attestations| == 0 then {}
        else 
            // output = set()  # type: Set[ValidatorIndex]
            // for a in attestations:
            //      output = output.union(get_attesting_indices(state, a.data, a.aggregation_bits))
            //      return set(filter(lambda index: not state.validators[index].slashed, output))       
            var indices := get_attesting_indices(s, attestations[0].data, attestations[0].aggregation_bits);
            var unslashed_indices := unslashed_attesting_indices_helper(s,indices);
            unslashed_indices + get_unslashed_attesting_indices(s, attestations[1..])
    }
    
    function method unslashed_attesting_indices_helper(s: BeaconState, indices: set<ValidatorIndex>): set<ValidatorIndex>
        requires forall i  :: i in indices ==> i as nat < |s.validators|
        ensures forall i  :: i in unslashed_attesting_indices_helper(s, indices) ==> i as nat < |s.validators|
    {
       if indices == {} then {}
       else 
            var x := PickIndex(indices);
            if !s.validators[x].slashed then {x} + unslashed_attesting_indices_helper(s, indices - {x})
            else unslashed_attesting_indices_helper(s, indices - {x})
    }


    
    // def get_attesting_indices(state: BeaconState,
    //                       data: AttestationData,
    //                       bits: Bitlist[MAX_VALIDATORS_PER_COMMITTEE]) -> Set[ValidatorIndex]:
    // """
    // Return the set of attesting indices corresponding to ``data`` and ``bits``.
    // """
    // committee = get_beacon_committee(state, data.slot, data.index)
    // return set(index for i, index in enumerate(committee) if bits[i])
    function method get_attesting_indices(s: BeaconState, data: AttestationData, bits: AggregationBits) : set<ValidatorIndex>
        requires TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(data.slot)) <= TWO_UP_6
        requires 0 < |get_beacon_committee(s, data.slot, data.index)| == |bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat

        ensures forall i :: i in get_attesting_indices(s, data, bits) ==> i as nat < |s.validators|
    {
        var committee := get_beacon_committee(s, data.slot, data.index);
        assert |committee| <= |bits|;
        assert forall e :: e in committee ==> e as nat < |s.validators|;
        filterIndicesxx(committee, bits)

    }

    function method filterIndicesxx(sv : seq<ValidatorIndex>, bits: AggregationBits) : set<ValidatorIndex>
        requires |sv| <= |bits|
        ensures |filterIndicesxx(sv, bits)| <= |sv|
        ensures forall i :: 0 <= i < |sv| && bits[i] ==> sv[i] in filterIndicesxx(sv, bits)
        ensures |filterIndicesxx(sv, bits)| <= |sv|
        ensures forall i :: i in filterIndicesxx(sv, bits) ==> i in sv
        decreases sv
    {
        if |sv| == 0 then 
            {}
        else 
            (if bits[0] then {sv[0]} else {})
                + filterIndicesxx(sv[1..], bits[1..])
    }

    /**
     *  Collect attestations with a specific target.
     *
     *  @param  x   A list of attestations.
     *  @param  br  A root value (hash of a block or block root). 
     *  @returns    The subset of `xl` that corresponds to attestation with target `r`.
     */
    function method filterAttestations(xl : seq<PendingAttestation>, br : Root) : seq<PendingAttestation>
        ensures |filterAttestations(xl, br)| <= |xl|
        ensures forall a :: a in xl && a.data.target.root == br <==> a in filterAttestations(xl, br) 
        decreases xl
    {
        if |xl| == 0 then 
            []
        else 
            (if xl[0].data.target.root == br then [xl[0]] else [])
                + filterAttestations(xl[1..], br)
    }

    function method filterAttestationsyy(xl : seq<PendingAttestation>, s : BeaconState) : seq<PendingAttestation>
        ensures |filterAttestationsyy(xl, s)| <= |xl|
        ensures forall a :: a in xl && 
                            a.data.slot < s.slot &&
                            s.slot - a.data.slot <= SLOTS_PER_HISTORICAL_ROOT &&
                            a.data.beacon_block_root == get_block_root_at_slot(s, a.data.slot) <==> a in filterAttestationsyy(xl, s) 
        decreases xl
    {
        if |xl| == 0 then 
            []
        else 
            (if xl[0].data.slot < s.slot &&
                s.slot - xl[0].data.slot <= SLOTS_PER_HISTORICAL_ROOT &&
                xl[0].data.beacon_block_root == get_block_root_at_slot(s, xl[0].data.slot) then [xl[0]] else [])

                + filterAttestationsyy(xl[1..], s)

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

    lemma AttestationHelperLemma(s: BeaconState, s1: BeaconState, a: Attestation)
        requires attestationIsWellFormed(s, a);
        requires s1.validators == s.validators
        requires s1.slot == s.slot
        requires s1.current_justified_checkpoint == s.current_justified_checkpoint
        requires s1.previous_justified_checkpoint == s.previous_justified_checkpoint
        ensures attestationIsWellFormed(s1, a);
    { // Thanks Dafny
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



}