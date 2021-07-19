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
include "../utils/NativeTypes.dfy"
include "../ssz/Constants.dfy"
include "./BeaconChainTypes.dfy"
include "attestations/AttestationsTypes.dfy"
include "validators/Validators.dfy"
include "../ssz/Serialise.dfy"
include "../utils/MathHelpers.dfy"

/**
 * Misc helpers.
 */
module BeaconHelpers {

    import opened Eth2Types
    import opened NativeTypes
    import opened Constants
    import opened BeaconChainTypes
    import opened AttestationsTypes
    import opened Validators
    import opened SSZ
    import opened MathHelpers

    lemma NatDivision(a: nat, b: nat)
        requires b != 0
        ensures a / b == (a as real / b as real).Floor
    {
        // Ref: https://stackoverflow.com/questions/50627131/in-dafny-can-the-relationship-between-integer-natural-division-and-real-divisio
        assert a == (a / b) * b + (a % b);

        // Cast some values to `real`, because this is a programming language.
        // (In math, 7 and 7.0 are the same object and this wouldn't be needed...)
        assert a as real == (a / b) as real * b as real + (a % b) as real;

        assert (a % b) as real / b as real < b as real;
        assert a as real / b as real == (a / b) as real + (a % b) as real / b as real;
        assert (a % b) < b;
        assert (a % b) as real / b as real < 1 as real;
        
        // Aha! That reveals that the real quotient `a as real / b as real` is equal to the natural quotient `a / b` (a natural number) plus a fraction.
        // This looks enough like `Floor` that Dafny can take it from here.
    }

    /**
     *  A simple lemma to bound integer division when divisor >= 1.
     */
    lemma divLess(x : nat , k : nat) 
        requires k >= 1
        ensures 0 <= x / k <= x 
    {   //  Thanks Dafny
    }

    /**
     *  ( x  /  k ) * k is less than or equal to x.
     */
    lemma div2(x : nat, k : nat) 
        requires k >= 1 
        ensures ( x / k ) * k <= x
    {
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

    predicate minimumActiveValidators(s: BeaconState)
    {
        |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
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

    

    /** max(a,b) returns a if a > b, else b */
    function method max(a: nat, b: nat): nat
    {
        if a > b then a else b
    }   

    // /** min(a,b) returns a if a < b, else b */
    // function method min(a: nat, b: nat): nat
    // {
    //     if a < b then a else b
    // }   

    function method uint64Range(start: uint64, end: uint64): seq<uint64>
        requires end >= start
        ensures |uint64Range(start,end)| == (end - start) as int
        ensures forall i :: 0 <= i < |uint64Range(start,end)| ==> start <= uint64Range(start,end)[i] < end
        decreases end - start
    {
        if (end - start) == 0 then []
        else [start] + uint64Range(start+1, end)
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
        computeCommitteeLemma(|indices|, index as nat, count as nat);
        
        assert end > start;
        var range := uint64Range(start as uint64, end as uint64);

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

    function method compute_committee_helper(indices: seq<ValidatorIndex>, seed: Bytes32, range: seq<uint64>) : seq<ValidatorIndex>
        requires |indices| < 0x10000000000000000
        requires forall i :: 0 <= i < |range| ==> range[i] as int < |indices|
        ensures |compute_committee_helper(indices, seed, range)| as nat == |range|
        ensures forall e :: e in compute_committee_helper(indices, seed, range) ==> e in indices
    {
        if |range| == 0 then []
        else [indices[compute_shuffled_index(range[0], |indices| as uint64, seed)]] + compute_committee_helper(indices, seed, range[1..])
    }


    

    // lemma NatDivHelper(a: nat, b: nat, c: nat)
    //     requires b != 0
    //     ensures (a % b) as real / b as real - (c % b) as real / b as real == ((a % b) - (c % b)) as real / b as real
    // {
    //     // Thanks Dafny

    // }

    // lemma NatDivHelper2(a: nat, b: nat, c: nat)
    //     requires b != 0
    //     //requires a >= c
    //     ensures ((a % b) - (c % b)) % b == (a - c) % b
    //     // refer to ironfleet library
   

    // lemma NatDivHelper3(a: nat, b: nat)
    //     requires b > 0
    //     ensures (a * b) % b == 0
    //     // refer to ironfleet library

    lemma computeCommitteeLemma(len: nat, index: nat, count: nat)
        requires count > 0
        requires len * index / count  < 0x10000000000000000
        requires len * (index +1) / count < 0x10000000000000000
        ensures len * (index +1) / count >= len * index  / count
    {
        computeCommitteeLemma2(len * (index +1), len * index, count);

    }

    lemma computeCommitteeLemma2(a: nat, b: nat, count: nat)
        requires count > 0
        requires a >= b
        ensures a/count >= b/count
    {
        if a == b {
            // Thanks Dafny
        }
        else {
            assert a > b;
            var i : nat :| a == b + i;
            assert i > 0;
            NatDivision(a,count);
            assert a / count == (a as real / count as real).Floor;
            NatDivision(b,count);
            assert b / count == (b as real / count as real).Floor;
            assert a as real / count as real > b as real / count as real;
        }
    }

     //Return the randao mix at a recent ``epoch``.
    function method get_randao_mix(state: BeaconState, epoch: Epoch): Bytes32
    {
        state.randao_mixes[epoch % EPOCHS_PER_HISTORICAL_VECTOR as uint64]
    }

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
        confirmBoundBreach3(|get_active_validator_indices(s.validators, epoch)|, committees_per_slot as nat, (slot % SLOTS_PER_EPOCH) as nat, index as nat);
        proveActiveValidatorsSatisfyBounds(|get_active_validator_indices(s.validators, epoch)|, committees_per_slot as nat, (slot % SLOTS_PER_EPOCH) as nat, index as nat);
        //assert len_indices as nat * ((slot * CPS + cIndex) as nat + 1) / (CPS as nat * SLOTS_PER_EPOCH as nat) > len_indices as nat * (slot * CPS + cIndex) as nat / (CPS as nat * SLOTS_PER_EPOCH as nat);

        compute_committee(
            get_active_validator_indices(s.validators, epoch),
            get_seed(s, epoch, DOMAIN_BEACON_ATTESTER),
            (slot % SLOTS_PER_EPOCH) * committees_per_slot + index,
            committees_per_slot * SLOTS_PER_EPOCH
        )
    } 

    lemma proveAtLeastOneCommitteeFormedBreachsBound(len_indices: nat, CPS: nat)
        requires TWO_UP_11 as nat * TWO_UP_11 as nat < len_indices 
        requires CPS == max(1, min(MAX_COMMITTEES_PER_SLOT as nat, len_indices/ SLOTS_PER_EPOCH  as nat/ TARGET_COMMITTEE_SIZE as nat) as nat)
        //requires 0 <= slot < SLOTS_PER_EPOCH as nat// i.e. slot % SPE
        //requires 0 <= cIndex < CPS

        ensures 
            exists cIndex, slot  | 0 <= cIndex < CPS && 0 <= slot < SLOTS_PER_EPOCH as nat :: 
            ((len_indices * ((slot * CPS + cIndex) + 1) / (CPS * SLOTS_PER_EPOCH as nat)) - (len_indices * (slot * CPS + cIndex)  / (CPS * SLOTS_PER_EPOCH as nat)) > MAX_VALIDATORS_PER_COMMITTEE as nat)
    {
        assert CPS == 64;
        
        assert exists cIndex, slot  | 0 <= cIndex < CPS && 0 <= slot < SLOTS_PER_EPOCH as nat :: // exists slot | 0 <= slot < SLOTS_PER_EPOCH as nat :: //
               ((len_indices * ((slot * CPS + cIndex) + 1) / (CPS * SLOTS_PER_EPOCH as nat)) - (len_indices * (slot * CPS + cIndex)  / (CPS * SLOTS_PER_EPOCH as nat)) > MAX_VALIDATORS_PER_COMMITTEE as nat)
               by
               {
                    assert //var slot := 31  && var cIndex := 63 ==>
                    (len_indices * ((31 * CPS + 63) + 1) / (CPS * SLOTS_PER_EPOCH as nat)) - (len_indices * (31 * CPS + 63)  / (CPS * SLOTS_PER_EPOCH as nat)) > MAX_VALIDATORS_PER_COMMITTEE as nat;
               }
    }

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

    // len_indices is the number of active validators, 
    // CPS = committees per slot, 
    // cIndex is the Committee Index from get_beacon_committee
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

    



    lemma confirmBoundBreach3(len_indices: nat, CPS: nat, slot: nat, cIndex: nat)
        requires TWO_UP_5 as nat <= len_indices 
        requires CPS == max(1, min(MAX_COMMITTEES_PER_SLOT as nat, len_indices/ SLOTS_PER_EPOCH  as nat/ TARGET_COMMITTEE_SIZE as nat) as nat)
        requires 0 <= slot < SLOTS_PER_EPOCH as nat// i.e. slot % SPE
        requires 0 <= cIndex < CPS

        ensures len_indices * ((slot * CPS + cIndex) + 1) / (CPS * SLOTS_PER_EPOCH as nat) > len_indices * (slot * CPS + cIndex) / (CPS * SLOTS_PER_EPOCH as nat);
    {
        confirmBoundBreach5(len_indices * ((slot * CPS + cIndex) + 1), len_indices * (slot * CPS + cIndex) , (CPS * SLOTS_PER_EPOCH as nat));

        assert len_indices * ((slot * CPS + cIndex) + 1) - len_indices  * (slot * CPS + cIndex) >=  (CPS  * SLOTS_PER_EPOCH as nat) ==> 
                len_indices * ((slot * CPS + cIndex) + 1) / (CPS  * SLOTS_PER_EPOCH as nat) > len_indices * (slot * CPS + cIndex) / (CPS * SLOTS_PER_EPOCH as nat);

        calc {
            len_indices * ((slot * CPS + cIndex) + 1) - len_indices * (slot * CPS + cIndex);
            {confirmBoundBreach6(len_indices as nat, (slot * CPS + cIndex));} len_indices * (slot * CPS + cIndex) + len_indices - len_indices * (slot * CPS + cIndex);
            len_indices as nat;
        }
        assert len_indices == len_indices * ((slot * CPS + cIndex) + 1) - len_indices * (slot * CPS + cIndex);

        assert len_indices >= (CPS * SLOTS_PER_EPOCH as nat) <==> len_indices * ((slot * CPS + cIndex) + 1) - len_indices * (slot * CPS + cIndex) >=  (CPS * SLOTS_PER_EPOCH as nat);

        assert  TWO_UP_5 as nat <= len_indices 
            ==> len_indices >= (CPS * SLOTS_PER_EPOCH as nat) 
            ==> len_indices * ((slot * CPS + cIndex) + 1) / (CPS * SLOTS_PER_EPOCH as nat) > len_indices * (slot * CPS + cIndex) / (CPS * SLOTS_PER_EPOCH as nat);
    }

    lemma confirmBoundBreach6(a: nat, b: nat)
        ensures a * (b + 1) == a * b + a 
    {

    }

    lemma confirmBoundBreach5(a: nat, b: nat, c: nat)
        requires c > 0
        ensures a - b >= c ==> a/c > b/c 
    {

    }


    // lemma confirmBoundBreach4(len_indices: uint64, CPS: uint64, slot: uint64, cIndex: uint64)
    //     //requires len_indices < TWO_UP_13  
    //     requires CPS == max(1, min(
    //         MAX_COMMITTEES_PER_SLOT as nat,  
    //         len_indices as nat/ SLOTS_PER_EPOCH as nat / TARGET_COMMITTEE_SIZE as nat) 
    //     ) as uint64
    //     requires 0 <= slot < SLOTS_PER_EPOCH // i.e. slot % SPE
    //     requires 0 <= cIndex < CPS

    //     //ensures TWO_UP_5 as nat <= len_indices as nat < (64 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE)  as nat ==> len_indices as nat * ((slot * CPS + cIndex) as nat + 1) / (CPS as nat * SLOTS_PER_EPOCH as nat) >
    //     //       len_indices as nat * (slot * CPS + cIndex) as nat / (CPS as nat * SLOTS_PER_EPOCH as nat    
    // {
    //     assert len_indices < TWO_UP_13 <==> CPS == 1;
    //     assert len_indices < TWO_UP_5 ==> CPS == 1 && cIndex == 0; 

    //     //assert TWO_UP_5 as nat <= len_indices as nat < 0x10000000000000000 as nat ==> ((slot * CPS + cIndex) as nat + 1) - (slot * CPS + cIndex) as nat == 1;
    //     //assert len_indices < TWO_UP_5 && slot == 0 ==> len_indices as nat * ((slot * CPS + cIndex) as nat + 1) / (CPS as nat * SLOTS_PER_EPOCH as nat) -
    //     //       len_indices as nat * (slot * CPS + cIndex) as nat / (CPS as nat * SLOTS_PER_EPOCH as nat) == 0 ;
        
    //     //assert TWO_UP_4 <= len_indices < TWO_UP_5 && slot == 1 ==> len_indices as nat * ((slot * CPS + cIndex) as nat + 1) / (CPS as nat * SLOTS_PER_EPOCH as nat) >
    //     //       len_indices as nat * (slot * CPS + cIndex) as nat / (CPS as nat * SLOTS_PER_EPOCH as nat);

    //     //assert TWO_UP_5 as nat <= len_indices as nat <  TWO_UP_16  as nat ==> len_indices as nat * ((slot * CPS + cIndex) as nat + 1) / (CPS as nat * SLOTS_PER_EPOCH as nat) >
    //     //       len_indices as nat * (slot * CPS + cIndex) as nat / (CPS as nat * SLOTS_PER_EPOCH as nat);

    //     //assert TWO_UP_5 as nat <= len_indices as nat < (64 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE)  as nat ==> len_indices as nat * ((slot * CPS + cIndex) as nat + 1) / (CPS as nat * SLOTS_PER_EPOCH as nat) >
    //     //       len_indices as nat * (slot * CPS + cIndex) as nat / (CPS as nat * SLOTS_PER_EPOCH as nat);

    //     assert (64 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE) as nat <= len_indices as nat  < 0x10000000000000000 ==> CPS == 64 && len_indices as nat * ((slot * CPS + cIndex) as nat + 1) / (CPS as nat * SLOTS_PER_EPOCH as nat) >
    //           len_indices as nat * (slot * CPS + cIndex) as nat / (CPS as nat * SLOTS_PER_EPOCH as nat);

    //     //assert TWO_UP_5 as nat <= len_indices as nat < TWO_UP_20  as nat ==> len_indices as nat * ((slot * CPS + cIndex) as nat + 1) / (CPS as nat * SLOTS_PER_EPOCH as nat) >
    //     //       len_indices as nat * (slot * CPS + cIndex) as nat / (CPS as nat * SLOTS_PER_EPOCH as nat);

    // //    assert (len_indices as nat * ((slot * CPS + cIndex) as nat + 1) / (CPS as nat * SLOTS_PER_EPOCH as nat)) -
    // //             (len_indices as nat * (slot * CPS + cIndex) as nat / (CPS as nat * SLOTS_PER_EPOCH as nat)) == 0;
    // }

    //ensures |get_active_validator_indices(s.validators, epoch)| as uint64 < 2 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE ==> get_committee_count_per_slot(s,epoch) == 1
    //ensures 2 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE <= |get_active_validator_indices(s.validators, epoch)| as uint64 < 3 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE==> get_committee_count_per_slot(s,epoch) == 2
    //ensures 3 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE <= |get_active_validator_indices(s.validators, epoch)| as uint64 < 4 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE==> get_committee_count_per_slot(s,epoch) == 3

    //ensures 64 * SLOTS_PER_EPOCH * TARGET_COMMITTEE_SIZE <= |get_active_validator_indices(s.validators, epoch)| as uint64 ==> get_committee_count_per_slot(s,epoch) == 64
    // TARGET_COMMITTEE_SIZE == TWO_UP_7;

    lemma divHelper(a: nat, b: nat, c: nat)
        requires a < 0x10000000000000000
        requires c > 0
        requires b <= c
        ensures a * b / c < 0x10000000000000000
    {
        assert a * b <= a * c;
    }

    lemma divHelper2(a: nat, b: nat, c: nat)
        requires a < 0x10000000000000000
        requires c > 0
        requires b <= c
        ensures a * b / c <= a
    {
        // Thanks Dafny
    }


}