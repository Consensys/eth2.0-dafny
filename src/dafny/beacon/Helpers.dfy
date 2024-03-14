/*
 * Copyright 2021 ConsenSys Software Inc.
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

//  @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /timeLimit:100 /noCheating:1

include "../utils/Eth2Types.dfy"
include "../utils/MathHelpers.dfy"
include "../utils/NativeTypes.dfy"
include "../utils/SetHelpers.dfy"
include "../utils/SeqHelpers.dfy"
include "../utils/Helpers.dfy"
include "../ssz/Constants.dfy"

include "BeaconChainTypes.dfy"
include "Helpers.s.dfy"
include "Helpers.p.dfy"
include "ActiveValidatorBounds.p.dfy"
include "attestations/AttestationsTypes.dfy"
include "validators/Validators.dfy"

/**
 *  Misc helpers, ordered as per the Beacon chain spec, and additional functions to facilitate 
 *  the Dafny implementation.
 */

module BeaconHelpers {

    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened MathHelpers
    import opened NativeTypes
    import opened SetHelpers
    import opened SeqHelpers
    import opened Helpers
    import opened Constants

    import opened BeaconChainTypes
    import opened BeaconHelperSpec
    import opened BeaconHelperProofs
    import opened ActiveValidatorBounds
    import opened AttestationsTypes
    import opened Validators

    ///////////////////////////////////////////////////////////////////////////////////////////
    //  Helper functions - Math  
    //  @note   xor, uint_to_bytes and bytes_to_uint64 have equivalents in other files e.g. SSZ
    ///////////////////////////////////////////////////////////////////////////////////////////
    
    /**
     *  Integer square root.
     *
     *  @param  n       A uint64.
     *  @returns        The integer square root of n.
     *
     *  @note           In src/dafny/beacon/helpers/Math.dfy a method version exits
     *                  however a function method version is required for the spec.
     */
    function method {:axiom} integer_square_root(n:uint64) : uint64
        requires n <= 0xFFFFFFFFFFFFFFFF
        ensures power2(integer_square_root(n) as nat) <= n as nat;
        ensures n >= 4 ==> integer_square_root(n) as nat > 1;
    // {}

    
    ///////////////////////////////////////////////////////////////////////////////////////////
    //  Helper functions - Crypto  
    //  @note   BLS signatures not used in this simplified model of the spec.
    ///////////////////////////////////////////////////////////////////////////////////////////
    
    /**
     *  Compute Root/Hash/Bytes32 for different types.
     *  
     *  @note   The property of hash_tree_root below is enough for 
     *          proving some invariants. So we may use a module refinement
     *          to integrate the actual hash_tree_root from Merkle module
     *          at a later stage if needed.
     */
    function method {:axiom} hash_tree_root<T(==)>(t : T) : Bytes32 
        ensures hash_tree_root(t) != DEFAULT_BYTES32

    function method {:axiom} hash<T(==)>(t : T) : Bytes32 
        ensures hash(t) != DEFAULT_BYTES32


    ///////////////////////////////////////////////////////////////////////////////////////////
    //  Helper functions - Predicates 
    //  @note   is_valid_merkle_branch is assumed in this simplified model of the spec.
    ///////////////////////////////////////////////////////////////////////////////////////////
    
    /**
     *  Check if ``validator`` is active for a given epoch.
     *
     *  @param  validator   A validator.
     *  @param  epoch       An epoch.
     *  @return             True if v is active.
     */
    predicate method is_active_validator(validator: Validator, epoch: Epoch)
    {
        validator.activation_epoch <= epoch < validator.exitEpoch
    }

    /**
     *  Check if ``validator`` is eligible to be placed into the activation queue.
     *
     *  @param  v   A validator.
     *  @return     True if the v is is eligible to be placed into the activation queue.
     */
    predicate method is_eligible_for_activation_queue(v: Validator)
    {
        v.activation_eligibility_epoch == FAR_FUTURE_EPOCH
        && v.effective_balance == MAX_EFFECTIVE_BALANCE
    }

    /**
     *   Check if ``validator`` is eligible for activation.
     *
     *  @param  s   A beacon state.
     *  @param  v   A validator.
     *  @return     True if v is eligible for activation.
     */
    predicate method is_eligible_for_activation(s: BeaconState, v: Validator)
    {
        // Placement in queue is finalized
        v.activation_eligibility_epoch <= s.finalised_checkpoint.epoch
        // Has not yet been activated
        && v.activation_epoch == FAR_FUTURE_EPOCH
    }

    /**
     *  Check if ``validator`` is slashable.
     *
     *  @param  v      A validator.
     *  @param  epoch  An epoch.
     *  @return        True if v is slashable.
     */
    predicate method is_slashable_validator(v: Validator, epoch: Epoch)
    {
        (!v.slashed) && (v.activation_epoch <= epoch < v.withdrawable_epoch)
    }

    /** Check if ``data_1`` and ``data_2`` are slashable according to Casper FFG rules.
     *
     *  @param  data_1   Attestation data.
     *  @param  data_2   Attestation data.
     *  @return          True if ``data_1`` and ``data_2`` are slashable.
     */
    predicate method is_slashable_attestation_data(data_1: AttestationData, 
                                                   data_2: AttestationData)
    {
        // Double vote
        (data_1 != data_2 
            && data_1.target.epoch == data_2.target.epoch) 
        // Surround vote
        || (data_1.source.epoch < data_2.source.epoch 
            && data_2.target.epoch < data_1.target.epoch)
    }

    /**
     *  Check if ``indexed_attestation`` is valid.
     *
     *  @param  indexed_attestation     Indexed attestation.
     *  @return                         True if``indexed_attestation`` is not empty, has sorted 
     *                                  and unique indices.// & has a valid aggregate signature.
     */
    predicate method is_valid_indexed_attestation(indexed_attestation: IndexedAttestation)
    {
        // Verify indices are sorted and unique
        var indices := indexed_attestation.attesting_indices;
        if (|indices| == 0 || !is_attesting_indices_sorted_and_unique(indices))
            then false
        else 
            true

        // Verify aggregate signature, not implemented in this model.
    }

    /**
     *  Check if ``indices`` are sorted and unique.
     *
     *  @param  indexed_attestation     Indexed attestation.
     *  @return                         True if the indices are sorted and unique.
     *
     *  @note   This predicate method is not specified in the spec but acts as a 
     *          helper to is_valid_indexed_attestation.
     */
    predicate method is_attesting_indices_sorted_and_unique(indices: AttestingIndices)
        requires |indices| > 0
    {
        forall i,j :: 0 <= i < j < |indices| ==> indices[i] < indices[j]
    }


    ///////////////////////////////
    ////////////////////////////////////////////////////////////
    //  Helper functions - Misc 
    //  @note   compute_fork_data_root, compute_fork_digest, compute_domain and
    //          compute_signing_root are not required to implement this model.
    ///////////////////////////////////////////////////////////////////////////////////////////
    
    /**
     *  Return the shuffled index corresponding to ``seed`` (and ``index_count``).
     *
     *  @param      index           An index.
     *  @param      index_count     Upper bound on index (index < index_count).
     *  @param      seed            A seed value.
     *  @returns                    The shuffled index as calculated by the 'generalized domain' 
     *                              algorithm on page 3 of the linked paper.
     *  @link{https://link.springer.com/content/pdf/10.1007%2F978-3-642-32009-5_1.pdf}
     *
     *  @note       The shuffle functionality is not implemented as in the spec but instead the 
     *              original index is returned. 
     */
    function method compute_shuffled_index(index: uint64, 
                                           index_count: uint64, 
                                           seed: Bytes32
                                          ) : uint64
        requires index < index_count
    {
        index // temporary return value
    }

    /**
     *  Return from ``indices`` a random index sampled by effective balance.
     *
     *  @param      state       A beacon state.
     *  @param      indices     A sequence of active validators.
     *  @param      seed        A seed value.
     *  @returns                The proposer index.
     *
     *  @note       The random functionality is not implemented as in the spec but instead the 
     *              0 index is returned. 
     */
    function method compute_proposer_index(state: BeaconState, 
                                           indices: seq<ValidatorIndex>, 
                                           seed: Bytes32
                                          ) : ValidatorIndex
        requires |indices| > 0
        ensures compute_proposer_index(state, indices, seed) in indices
    {
        indices[0] as ValidatorIndex // temporary return value
    }

    /**
     *  Return the committee corresponding to ``indices``, ``seed``, ``index``, and 
     *  committee ``count``.
     *
     *  @param      indices     A sequence of active validator indices.
     *  @param      seed        A seed value.
     *  @param      index       (slot % SLOTS_PER_EPOCH) * committees_per_slot + CommitteeIndex
     *  @param      count       committees_per_slot * SLOTS_PER_EPOCH
     *  @returns                A sequence of active validator indices to be used 
     *                          as a committee.
     *
     *  @note       This function uses a helper function (compute_committee_helper) to
     *              generate the committee indices recursively.
     *  @note       index and count are dependent on the slot, number of committees per
     *              slot and the particular committee index number (i.e. which ranges 
     *              from 0 to less than committees_per_slot).
     *  @note       The preconditions are summarised by predicate
     *              is_valid_compute_committee_parameters.
     */
    function method compute_committee(indices: seq<ValidatorIndex>, 
                                      seed: Bytes32, 
                                      index: uint64, 
                                      count: uint64
                                     ) : seq<ValidatorIndex>
        requires is_valid_compute_committee_parameters(indices, seed, index, count)

        ensures 0 
                < |compute_committee(indices, seed, index, count)| 
                    //== (|indices| * (index as nat +1)) / count as nat - (|indices| * index as nat) / count as nat 
                <= MAX_VALIDATORS_PER_COMMITTEE as nat
        ensures forall e :: e in compute_committee(indices, seed, index, count) 
                ==> e in indices
    {
        var start := (|indices| * index as nat) / count as nat;
        var end := (|indices| * (index as nat +1)) / count as nat;
        commonDivRule(|indices| as nat * (index as nat +1), |indices| as nat * index as nat, count as nat);
        var range := range(start, end);

        compute_committee_helper(indices, seed, range)
    }

    /**
     *  Helper function to compute_committee.
     *
     *  @param      indices     A sequence of active validator indices.
     *  @param      seed        A seed value.
     *  @param      range       A subset of index positions relative to indices.
     *  @return                 A sequence of active validator indices to be used 
     *                          as a committee.
     *
     *  @note   This function method is not specified in the spec but acts as a 
     *          helper to compute_committee to implement recursion.
     */
    function method compute_committee_helper(indices: seq<ValidatorIndex>, 
                                             seed: Bytes32, 
                                             range: seq<nat>
                                            ) : seq<ValidatorIndex>
        requires |indices| < 0x10000000000000000
        requires forall i :: 0 <= i < |range| ==> range[i] as int < |indices|

        ensures |compute_committee_helper(indices, seed, range)| as nat == |range|
        ensures forall e :: e in compute_committee_helper(indices, seed, range) ==> e in indices
    {
        if |range| == 0 then []
        else [indices[compute_shuffled_index(range[0] as uint64, |indices| as uint64, seed)]] 
                + compute_committee_helper(indices, seed, range[1..])
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
     *  Return the epoch during which validator activations and exits initiated in 
     *  ``epoch`` take effect.
     *  
     *  @param  epoch   An epoch.
     *  @returns        `epoch` + 1 + MAX_SEED_LOOKAHEAD.
     */
    function method compute_activation_exit_epoch(epoch: Epoch) : Epoch
        requires epoch as int + 1 + MAX_SEED_LOOKAHEAD as int < 0x10000000000000000 
        ensures compute_activation_exit_epoch(epoch) > epoch
        ensures compute_activation_exit_epoch(epoch) > epoch + MAX_SEED_LOOKAHEAD as Epoch
    {
        epoch + 1 as Epoch + MAX_SEED_LOOKAHEAD as Epoch
    }


    ///////////////////////////////////////////////////////////////////////////////////////////
    //  Helper functions - Beacon state accessors 
    //  @note   get_domain & get_indexed_attestation are not required to implement this model.
    ///////////////////////////////////////////////////////////////////////////////////////////
    
    /**
     *  Return the epoch associated with a ``state``.
     *
     *  @param  state   A beacon state.
     *  @returns        The epoch of the state's slot.
     */
    function method get_current_epoch(state: BeaconState) : Epoch 
        ensures get_current_epoch(state) as int * SLOTS_PER_EPOCH as int 
                < 0x10000000000000000
        ensures get_current_epoch(state) * SLOTS_PER_EPOCH <= state.slot
        ensures state.slot % SLOTS_PER_EPOCH != 0 
                ==> get_current_epoch(state) * SLOTS_PER_EPOCH < state.slot
        /** A useful proof that states that the slot that corresponds
            to the current epoch is within the range of the history 
            a block roots stored in the state.block_roots. */
        ensures state.slot - get_current_epoch(state) * SLOTS_PER_EPOCH 
                <= SLOTS_PER_HISTORICAL_ROOT
    {
        compute_epoch_at_slot(state.slot)
    }

    /**
     *  Return the previous epoch associated with a ``state``.
     *
     *  @param  state   A beacon state.
     *  @returns        Epoch before state's epoch and 0 is state's epoch is 0.
     */
    function method get_previous_epoch(state: BeaconState) : Epoch 
        ensures get_previous_epoch(state) <= get_current_epoch(state)
        ensures get_previous_epoch(state) as int * SLOTS_PER_EPOCH as int 
                < 0x10000000000000000
        ensures get_previous_epoch(state) * SLOTS_PER_EPOCH <= state.slot
        ensures get_current_epoch(state) == 0 
                ==> get_current_epoch(state) == get_previous_epoch(state)
        ensures get_current_epoch(state) > 0 
                ==> get_current_epoch(state) - 1 == get_previous_epoch(state) 
        /** A useful proof that states that the slot that corresponds
            to the previous epoch is within the range of the history 
            a block roots stored in the state.block_roots. */
        ensures state.slot - get_previous_epoch(state) * SLOTS_PER_EPOCH 
                <= SLOTS_PER_HISTORICAL_ROOT
        ensures get_current_epoch(state) > 0 
                ==> get_previous_epoch(state) * SLOTS_PER_EPOCH < state.slot
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
     *  @note   Given an epoch, start slot is epoch * SLOTS_PER_EPOCH.
     *          Only the last SLOTS_PER_HISTORICAL_ROOT block roots are stored in the state.
     *          To be able to retrieve the block root, the slot of epoch must be recent
     *          i.e state.slot - epoch * SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT.
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
     */
    function method get_block_root_at_slot(state: BeaconState, slot: Slot) : Root
        requires slot < state.slot 
        requires state.slot - slot <=  SLOTS_PER_HISTORICAL_ROOT
    {
        state.block_roots[slot % SLOTS_PER_HISTORICAL_ROOT]
    }

    /**
     *  Return the randao mix at a recent ``epoch``.
     *
     *  @param  state   A beacon state.
     *  @param  epoch   A recent epoch.
     *  @returns        The stored randao_mix for the specified epoch. 
     *
     *  @note   The notion of a ``recent`` epoch is such that it is within 
     *          EPOCHS_PER_HISTORICAL_VECTOR epochs for the current epoch?
     */
    function method get_randao_mix(state: BeaconState, epoch: Epoch): Bytes32
    {
        state.randao_mixes[epoch % EPOCHS_PER_HISTORICAL_VECTOR as uint64]
    }

    /**
     *  Return the sequence of active validator indices at ``epoch``.
     *
     *  @param  sv      A sequence of validators.
     *  @param  epoch   An epoch.
     *  @returns        The the sequence of active validator indices at ``epoch``. 
     *
     *  @note   As this function does not modify the state but rather only the validators
     *          field is accessed, the function is better suited to using an input parameter
     *          of just the list of validators (rather than the entire state).
     *  @note   The spec returns a set of indices rather than a sequence.
     *          As the sequence values will be unique, the elements of the sequence are 
     *          equivalent to the elements if a resulting set.
     */
    function method get_active_validator_indices(sv: ListOfValidators, epoch: Epoch) : seq<ValidatorIndex>
        ensures |get_active_validator_indices(sv,epoch)| <= |sv|
        ensures forall i :: 0 <= i < |get_active_validator_indices(sv, epoch)| 
                ==> get_active_validator_indices(sv, epoch)[i] as nat < |sv|
        ensures forall i :: 0 <= i < |get_active_validator_indices(sv, epoch)| 
                ==> sv[get_active_validator_indices(sv, epoch)[i] ].activation_epoch 
                    <= epoch 
                    < sv[get_active_validator_indices(sv, epoch)[i]].exitEpoch
        ensures (exists i :: 0 <= i < |sv| && sv[i].activation_epoch <= epoch < sv[i].exitEpoch)
                ==> |get_active_validator_indices(sv, epoch)| > 0
    {
        if |sv| == 0 then []
        else 
            if is_active_validator(sv[|sv|-1], epoch) 
            then get_active_validator_indices(sv[..|sv|-1], epoch) + [(|sv|-1) as ValidatorIndex]
            else get_active_validator_indices(sv[..|sv|-1], epoch)
    }

    /**
     *  Return the validator churn limit for the current epoch.
     *
     *  @param  state   A beacon state.
     *  @param  epoch   An epoch.
     *  @returns        The validator churn limit for the current epoch. 
     */
    function method get_validator_churn_limit(s: BeaconState) : uint64
        ensures MIN_PER_EPOCH_CHURN_LIMIT // i.e. at least 4
               <= get_validator_churn_limit(s)  
        //     <= (|get_active_validator_indices(s.validators, get_current_epoch(s))| as uint64
        //          /CHURN_LIMIT_QUOTIENT)  
    {
        var active_validator_indices := get_active_validator_indices(s.validators, get_current_epoch(s));
        max(MIN_PER_EPOCH_CHURN_LIMIT as nat, 
            (|active_validator_indices| as uint64/CHURN_LIMIT_QUOTIENT) as nat
        ) as uint64
    }
    
    /**
     *  Return the seed at ``epoch``.
     *
     *  @param  state   A beacon state.
     *  @param  epoch   An epoch.
     *  @returns        The ``seed`` for the specified epoch. 
     *
     *  @note   This function uses a default return value and so the seed algorithm as specified
     *          in the spec is not implemented.
     */
    function method get_seed(state: BeaconState, epoch: Epoch, domain_type: DomainType): Bytes32
    {
        DEFAULT_SEED_BYTES32 // temporary return value
    }

    /**
     *  Return the number of committees in each slot for the given ``epoch``.
     *
     *  @param  state   A beacon state.
     *  @param  epoch   An epoch.
     *  @returns        The number of committees to be formed in each slot. 
     */
    function method get_committee_count_per_slot(s: BeaconState, epoch: Epoch) : uint64
        ensures 1 
                <= get_committee_count_per_slot(s,epoch) 
                <= MAX_COMMITTEES_PER_SLOT == TWO_UP_6;
    {
        max(1, 
            min(MAX_COMMITTEES_PER_SLOT as nat,  
                |get_active_validator_indices(s.validators, epoch)| 
                    / SLOTS_PER_EPOCH as nat 
                    / TARGET_COMMITTEE_SIZE as nat
               ) 
        ) as uint64
    }

    /**
     *  Return the beacon committee at ``slot`` for ``index``.
     *
     *  @param  state   A beacon state.
     *  @param  slot    A slot.
     *  @param  index   A committee index.
     *  @returns        The beacon committee at ``slot`` for ``index``.
     */
    function method get_beacon_committee(s: BeaconState, slot: Slot, index: CommitteeIndex) : seq<ValidatorIndex>
        requires is_valid_number_active_validators(|get_active_validator_indices(s.validators, compute_epoch_at_slot(slot))|)
        requires is_valid_committee_index(index, get_committee_count_per_slot(s, compute_epoch_at_slot(slot)))
        
        ensures 0 < |get_beacon_committee(s,slot,index)| <= MAX_VALIDATORS_PER_COMMITTEE as nat
        ensures forall e :: e in get_beacon_committee(s,slot,index) 
                ==> e as nat < |s.validators|
        ensures forall e :: e in get_beacon_committee(s,slot,index) 
                ==> is_active_validator(s.validators[e as nat], compute_epoch_at_slot(slot))
    {
        var epoch := compute_epoch_at_slot(slot);
        var committees_per_slot := get_committee_count_per_slot(s, epoch);
        getBeaconCommitteeLemma1(s, slot, index);
        
        compute_committee(
            get_active_validator_indices(s.validators, epoch),
            get_seed(s, epoch, DOMAIN_BEACON_ATTESTER),
            (slot % SLOTS_PER_EPOCH) * committees_per_slot + index,
            committees_per_slot * SLOTS_PER_EPOCH
        )
    } 

    /**
     *  Helper lemma to prove the preconditions needed within get_beacon_committee.
     *
     *  @param  state   A beacon state.
     *  @param  slot    A slot.
     *  @param  index   A committee index.
     *  @returns        A proof that is_valid_compute_committee_parameters is true.
     */
    lemma getBeaconCommitteeLemma1(s: BeaconState, slot: Slot, index: CommitteeIndex) 
        requires is_valid_number_active_validators(|get_active_validator_indices(s.validators, compute_epoch_at_slot(slot))|)
        requires is_valid_committee_index(index, get_committee_count_per_slot(s, compute_epoch_at_slot(slot)))
        
        ensures 
                var epoch := compute_epoch_at_slot(slot);
                var committees_per_slot := get_committee_count_per_slot(s, epoch);
                is_valid_compute_committee_parameters(
                                get_active_validator_indices(s.validators, epoch),
                                get_seed(s, epoch, DOMAIN_BEACON_ATTESTER),
                                (slot % SLOTS_PER_EPOCH) * committees_per_slot + index,
                                committees_per_slot * SLOTS_PER_EPOCH);
    {
        var epoch := compute_epoch_at_slot(slot);
        //assert epoch as nat < 0x10000000000000000;

        var committees_per_slot := get_committee_count_per_slot(s, epoch);
        //assert 1 <= committees_per_slot <= TWO_UP_6 as uint64;

        assert |get_active_validator_indices(s.validators, epoch)| <= |s.validators|;
        
        //assert forall i :: 0 <= i < |get_active_validator_indices(s.validators, epoch)| ==> 
        //    get_active_validator_indices(s.validators, epoch)[i] as nat < |s.validators|;
        
        assert 0 <= slot % SLOTS_PER_EPOCH < TWO_UP_5;
        assert 0  <= (slot % SLOTS_PER_EPOCH) * committees_per_slot + index < TWO_UP_11; 
        // i.e. max 31 * 64 + 63
        assert 32 <= committees_per_slot * SLOTS_PER_EPOCH <= TWO_UP_11;

        assert (committees_per_slot * SLOTS_PER_EPOCH) 
                >= ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index);
        assert (committees_per_slot * SLOTS_PER_EPOCH) 
                >= ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index + 1);
        assert |get_active_validator_indices(s.validators, epoch)| < 0x10000000000000000;

        divHelper(|get_active_validator_indices(s.validators, epoch)| as nat, 
                  ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index) as nat, 
                  (committees_per_slot * SLOTS_PER_EPOCH) as nat);
        divHelper(|get_active_validator_indices(s.validators, epoch)| as nat, 
                  ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index + 1) as nat, 
                  (committees_per_slot * SLOTS_PER_EPOCH) as nat);
        assert |get_active_validator_indices(s.validators, epoch)| as nat 
                    * ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index) as nat 
                    / (committees_per_slot * SLOTS_PER_EPOCH) as nat 
                < 0x10000000000000000;
        assert |get_active_validator_indices(s.validators, epoch)| as nat 
                    * ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index + 1) as nat 
                    / (committees_per_slot * SLOTS_PER_EPOCH) as nat 
                < 0x10000000000000000;
        
        divHelper2(|get_active_validator_indices(s.validators, epoch)| as nat, 
                    ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index + 1) as nat, 
                    (committees_per_slot * SLOTS_PER_EPOCH) as nat);
        assert |get_active_validator_indices(s.validators, epoch)| as nat 
                    * ((slot % SLOTS_PER_EPOCH) * committees_per_slot + index + 1) as nat 
                    / (committees_per_slot * SLOTS_PER_EPOCH) as nat 
                <= |get_active_validator_indices(s.validators, epoch)| as nat;

        assert (slot % SLOTS_PER_EPOCH) * committees_per_slot + index 
                < committees_per_slot * SLOTS_PER_EPOCH;
        assert TWO_UP_5 as nat 
                <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(slot))| 
                <= TWO_UP_11 as nat * TWO_UP_11 as nat;
        //assert 0 <= slot % SLOTS_PER_EPOCH < SLOTS_PER_EPOCH;
        getBeaconCommitteeLemma2(|get_active_validator_indices(s.validators, epoch)|, 
                                committees_per_slot as nat, 
                                (slot % SLOTS_PER_EPOCH) as nat, 
                                index as nat);
        proveActiveValidatorsSatisfyBounds(|get_active_validator_indices(s.validators, epoch)|, 
                                    committees_per_slot as nat, 
                                    (slot % SLOTS_PER_EPOCH) as nat, 
                                    index as nat);
    } 

    /**
     *  Return the beacon proposer index at the current slot.
     *
     *  @param  state   A beacon state.
     *  @returns        The proposer index at the current slot.
     *
     *  @note   The default seed is used rather than calculating the seed as per the spec.
     */
    function method get_beacon_proposer_index(state: BeaconState): ValidatorIndex
        requires |get_active_validator_indices(state.validators, get_current_epoch(state))| > 0

        ensures get_beacon_proposer_index(state) as nat < |state.validators|
        ensures is_active_validator(state.validators[get_beacon_proposer_index(state)], 
                                     get_current_epoch(state))
    {
        var epoch := get_current_epoch(state);
        var seed := DEFAULT_SEED_BYTES32;
        var indices := get_active_validator_indices(state.validators, epoch);

       compute_proposer_index(state, indices, seed)
    }

    /**
     *  Return the combined effective balance of the ``indices``.
     *
     *  @param  state   A beacon state.
     *  @param  indices A set of validator indices.
     *  @returns        The max of ``EFFECTIVE_BALANCE_INCREMENT`` and the combined effective 
     *                  balance of the ``indices``.
     *
     *  @note   ``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum to avoid divisions by zero.
     *           Math safe up to ~10B ETH, afterwhich this overflows uint64.
     */
    function method get_total_balance(s: BeaconState, indices: set<ValidatorIndex>) : Gwei
        requires forall i : ValidatorIndex :: i in indices ==> i as nat < |s.validators|
        ensures is_valid_gwei_amount(get_total_balance(s,indices) as nat)
        ensures EFFECTIVE_BALANCE_INCREMENT <= get_total_balance(s,indices) 
    {
        max(EFFECTIVE_BALANCE_INCREMENT as nat, get_total_balance_helper(s, indices) as nat) as Gwei
    }

    /**
     *  A helper function for get_total_balance to perform recursion.
     *
     *  @param  state   A beacon state.
     *  @param  indices A set of validator indices.
     *  @returns        The combined effective balance of the ``indices``.
     *
     *  @note   This function uses axiom AssumeNoGweiOverflow.
     */
    function method get_total_balance_helper(s: BeaconState, indices: set<ValidatorIndex>) : Gwei
        requires forall i : ValidatorIndex :: i in indices ==> i as nat < |s.validators|
        ensures is_valid_gwei_amount(get_total_balance_helper(s,indices) as nat)
    {
        if |indices| == 0 then 0 as Gwei
        else
            var y := PickIndex(indices);
            //assume s.validators[y].effective_balance as nat 
            //          + get_total_balance_helper(s, indices - {y}) as nat 
            //       < 0x10000000000000000;
            AssumeNoGweiOverflow(s.validators[y].effective_balance as nat 
                                    + get_total_balance_helper(s, indices - {y}) as nat);
            s.validators[y].effective_balance + get_total_balance_helper(s, indices - {y}) 
    }

    /**
     *  Pick an element from a set.
     *
     *  @param  s   A set of validator indices.
     *  @returns    An element from s.
     *
     *  @note       Could be changed to support a general type T and moved
     *              to SetHelpers.dfy.
     *  @note       This function method is not specified in the spec but acts as a 
     *              helper to get_total_balance_helper.
     *  @link{https://stackoverflow.com/questions/51207795/the-hilbert-epsilon-operator}
     */
    function method PickIndex(s: set<ValidatorIndex>): ValidatorIndex
        requires s != {}
    {
        HasMinimum(s);
        var z :| z in s && forall y :: y in s ==> z as nat <= y as nat;
        z
    }

    /**
     *  Return the combined effective balance of the active validators.
     *
     *  @param  state   A beacon state.
     *  @returns        The ombined effective balance of the active validators.
     *
     *  @note   ``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum to avoid divisions by zero.
     *  @note   This version assumes a balance of 1 per active validator.
     */
     function method get_total_active_balance(state: BeaconState) : Gwei
        ensures is_valid_gwei_amount(get_total_active_balance(state) as nat)
        //ensures EFFECTIVE_BALANCE_INCREMENT <= get_total_balance(s,indices) 
    {
        assert(|state.validators| < 0x10000000000000000);
        |state.validators| as uint64
    }

    /**
     *  Return the combined effective balance of the active validators.
     *
     *  @param  state   A beacon state.
     *  @returns        The combined effective balance of the active validators.
     *
     *  @note   ``EFFECTIVE_BALANCE_INCREMENT`` Gwei minimum to avoid divisions by zero.
     *  @note   This version implements the spec.
     */
    function method get_total_active_balance_full(s: BeaconState) : Gwei
        ensures is_valid_gwei_amount(get_total_active_balance_full(s) as nat)
        ensures EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s) 
        ensures integer_square_root(get_total_active_balance_full(s)) > 1
    {
        get_total_balance(s, 
                        seqToSet<ValidatorIndex>(get_active_validator_indices(s.validators, 
                                                 get_current_epoch(s)))
                        )
    }

    /**
     *  Return the set of attesting indices corresponding to ``data`` and ``bits``.
     *
     *  @param  s       A beacon state.
     *  @param  data    Attestation data.
     *  @param  bits    Aggregation bits.
     *  @returns        The set of attesting indices.
     */
    function method get_attesting_indices(s: BeaconState, 
                                          data: AttestationData, 
                                          bits: AggregationBits
                                         ) : set<ValidatorIndex>
        requires is_valid_number_active_validators(|get_active_validator_indices(s.validators, compute_epoch_at_slot(data.slot))|)
        requires is_valid_committee_index(data.index, get_committee_count_per_slot(s, compute_epoch_at_slot(data.slot)))
        requires is_valid_beacon_committee_length(|get_beacon_committee(s, data.slot, data.index)|, |bits|)

        ensures forall i :: i in get_attesting_indices(s, data, bits) ==> i as nat < |s.validators|
    {
        var committee := get_beacon_committee(s, data.slot, data.index);
        assert |committee| <= |bits|;
        assert forall e :: e in committee ==> e as nat < |s.validators|;
        filterIndicesxx(committee, bits)
    }

    /**
     *  A helper function for get_attesting_indices to filter indices.
     *
     *  @param  sv      A sequence of validator indices.
     *  @param  bits    Aggregation bits.
     *  @returns        set(index for i, index in enumerate(sv) if bits[i]).
     */
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
    

    ///////////////////////////////////////////////////////////////////////////////////////////
    //  Helper functions - Beacon state mutators 
    ///////////////////////////////////////////////////////////////////////////////////////////
    
    // Beacon State Mutators

    /** 
     *  Increase the validator balance at index ``index`` by ``delta``.
     *
     *  @param  s       A beacon state.
     *  @param  index   A validator index.
     *  @param  delta   A gwei amount.
     *  @returns        A new state where the validator balance at index ``index`` by 
     *                  ``delta`` is increased by delta.
     */
    function method increase_balance(s: BeaconState, index: ValidatorIndex, delta: Gwei): BeaconState 
        requires index as int < |s.balances| 
        requires s.balances[index] as int + delta as int < 0x10000000000000000
        ensures |s.balances| == |increase_balance(s,index,delta).balances|
        ensures increase_balance(s,index,delta).balances[index] == s.balances[index] + delta
        ensures increase_balance(s,index,delta) == s.(balances := increase_balance(s,index,delta).balances)
    {
        s.(
            balances := s.balances[index as int := (s.balances[index] + delta)]
        )
    }

    /** 
     *  Decrease the validator balance at index ``index`` by ``delta``.
     *
     *  @param  s       A beacon state.
     *  @param  index   A validator index.
     *  @param  delta   A gwei amount.
     *  @returns        A new state where the validator balance at index ``index`` by 
     *                  ``delta`` is decreased by delta.
     *
     *  @note           The balance cannot be negative.
     */
    function method decrease_balance(s: BeaconState, index: ValidatorIndex, delta: Gwei): BeaconState 
        // check index out of bounds
        requires index as int < |s.balances| 
        // check delta out of bounds
        ensures |s.balances| == |decrease_balance(s,index,delta).balances|
        // check balance is not negative
        ensures if s.balances[index] > delta 
                then decrease_balance(s,index,delta).balances[index] == s.balances[index] - delta
                else decrease_balance(s,index,delta).balances[index] == 0
        ensures s.validators == decrease_balance(s,index,delta).validators
        ensures decrease_balance(s,index,delta) == s.(balances := decrease_balance(s,index,delta).balances)
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

    /** 
     *  Initiate the exit of the validator with index ``index``.
     *
     *  @param  s       A beacon state.
     *  @param  index   A validator index.
     *  @returns        A new state where the validator at index ``index`` has its exitEpoch
     *                  and withdrawable_epoch brought forward, so long as it hasn't already.
     *
     *  @note   This function uses axiom AssumeNoEpochOverflow.
     */
    function method initiate_validator_exit(s: BeaconState, index: ValidatorIndex) : BeaconState
        requires |s.validators| == |s.balances|
        requires index as int < |s.validators| 
        requires minimumActiveValidators(s)
        
        ensures |s.validators| == |initiate_validator_exit(s,index).validators|
        ensures |s.balances| == |initiate_validator_exit(s,index).balances|
        ensures |initiate_validator_exit(s,index).validators| == |initiate_validator_exit(s,index).balances|
        ensures |initiate_validator_exit(s,index).validators| 
                == |initiate_validator_exit(s,index).balances|
        ensures s.validators[index].exitEpoch == FAR_FUTURE_EPOCH 
                    ==> initiate_validator_exit(s,index).validators[index].exitEpoch 
                        > get_current_epoch(s) + MAX_SEED_LOOKAHEAD
        ensures s.validators[index].exitEpoch != FAR_FUTURE_EPOCH 
                    ==> initiate_validator_exit(s,index).validators[index].exitEpoch 
                        == s.validators[index].exitEpoch
        ensures forall i :: (0 <= i < |s.validators|) && (i != index as nat) ==> 
                initiate_validator_exit(s,index).validators[i].exitEpoch == s.validators[i].exitEpoch
        ensures forall i :: (0 <= i < |s.validators|) && (i != index as nat) ==> 
                initiate_validator_exit(s,index).validators[i] == s.validators[i]
        ensures initiate_validator_exit(s,index).validators[index].exitEpoch < FAR_FUTURE_EPOCH
        ensures initiate_validator_exit(s,index).slot == s.slot
        ensures initiate_validator_exit(s,index).latest_block_header == s.latest_block_header
        ensures minimumActiveValidators(initiate_validator_exit(s,index))
        ensures initiate_validator_exit(s,index) == s.(validators := initiate_validator_exit(s,index).validators)
    {
        // # Return if validator already initiated exit
        if s.validators[index].exitEpoch != FAR_FUTURE_EPOCH then
            s
        else 
            var epoch := get_current_epoch(s);
            var exit_epochs := get_exit_epochs(s.validators);
            var exit_queue_epoch := max_epoch(exit_epochs + [compute_activation_exit_epoch(epoch)]);

            assert compute_activation_exit_epoch(epoch) in exit_epochs + [compute_activation_exit_epoch(epoch)];
            assert exit_queue_epoch > epoch + MAX_SEED_LOOKAHEAD;

            var exit_queue_churn := |get_queue_churn(s.validators, exit_queue_epoch)|;
            var validator_churn_limit := get_validator_churn_limit(s);

            var max_epoch_increment := exit_queue_epoch as nat + 1 + MIN_VALIDATOR_WITHDRAWABILITY_DELAY as nat;

            AssumeNoEpochOverflow(max_epoch_increment); 

            if exit_queue_churn  >= get_validator_churn_limit(s) as nat then 
                s.(validators := s.validators[index as nat := s.validators[index].(exitEpoch := exit_queue_epoch + 1 as Epoch,
                                                                withdrawable_epoch := (exit_queue_epoch as nat + 1 + MIN_VALIDATOR_WITHDRAWABILITY_DELAY as nat) as Epoch)])
            else
                s.(validators := s.validators[index as nat := s.validators[index].(exitEpoch := exit_queue_epoch,
                                                                withdrawable_epoch := (exit_queue_epoch as nat + MIN_VALIDATOR_WITHDRAWABILITY_DELAY as nat) as Epoch)])
    }

    /** 
     *  Slash the validator with index ``slashed_index``.
     *
     *  @param  s               A beacon state.
     *  @param  slashed_index   A validator index.
     *  @returns                A new state where the ``slashed_index`` validator is slashed.
     *
     *  @note   This function uses the axiom AssumeNoGweiOverflow.
     */
    function method slash_validator(s: BeaconState, 
                                    slashed_index: ValidatorIndex, 
                                    whistleblower_index: ValidatorIndex
                                   ): BeaconState
        requires slashed_index as nat < |s.validators| 
        requires whistleblower_index as nat < |s.validators| 
        requires |s.validators| == |s.balances|
        // i.e. |get_active_validator_indices()| > 0
        requires minimumActiveValidators(s)
        
        //ensures |get_active_validator_indices(slash_validator()| > 0
        ensures slash_validator(s, slashed_index, whistleblower_index).slot == s.slot
        ensures minimumActiveValidators(slash_validator(s, slashed_index, whistleblower_index))
        ensures |slash_validator(s, slashed_index, whistleblower_index).validators| 
                == |s.validators|
        ensures |slash_validator(s, slashed_index, whistleblower_index).validators| 
                ==  |slash_validator(s, slashed_index, whistleblower_index).balances| 
        ensures slash_validator(s, slashed_index, whistleblower_index) 
                == s.(validators := slash_validator(s, slashed_index, whistleblower_index).validators,
                      balances := slash_validator(s, slashed_index, whistleblower_index).balances,
                      slashings := slash_validator(s, slashed_index, whistleblower_index).slashings)
    {
        var epoch : Epoch := get_current_epoch(s);
        var proposer_index := get_beacon_proposer_index(s);

        var s1 := initiate_validator_exit(s, slashed_index); 
        // only validator exitEpoch & withdrawable_epoch fields possibly changed

        assert minimumActiveValidators(s1);

        // if whistleblower_index is None:
        //     whistleblower_index = proposer_index
        //  @note   'None' is not available in Dafny and so functions that call slash_validator 
        //          will have this parameter set to proposer_index.
        
        var whistleblower_reward : Gwei := (s1.validators[slashed_index].effective_balance as nat 
                                            / WHISTLEBLOWER_REWARD_QUOTIENT as nat) as Gwei;
        var proposer_reward := (whistleblower_reward as nat
                                / PROPOSER_REWARD_QUOTIENT as nat) as Gwei;
        var validator_penalty := (s1.validators[slashed_index].effective_balance as nat 
                                    / MIN_SLASHING_PENALTY_QUOTIENT as nat) as Gwei;
        
        var slashings_increase := s1.slashings[epoch as nat % EPOCHS_PER_SLASHINGS_VECTOR as nat] as nat 
                                    + s1.validators[slashed_index].effective_balance as nat;
        AssumeNoGweiOverflow(slashings_increase);

        var new_bal1 := s1.balances[proposer_index] as nat + proposer_reward as nat;
        var new_bal2 := s1.balances[whistleblower_index] as nat + whistleblower_reward  as nat;
        AssumeNoGweiOverflow(new_bal1);
        AssumeNoGweiOverflow(new_bal2);

        var s' := s1.(validators := s1.validators[slashed_index := s1.validators[slashed_index].(slashed := true,
                                                            withdrawable_epoch := max(s1.validators[slashed_index].withdrawable_epoch as nat,(epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat)) as Epoch)],
            slashings := s1.slashings[(epoch as int % EPOCHS_PER_SLASHINGS_VECTOR as nat) := s1.slashings[epoch as int % EPOCHS_PER_SLASHINGS_VECTOR as nat] + s1.validators[slashed_index].effective_balance],
            balances := increase_balance(
                            increase_balance(
                                decrease_balance(s1, slashed_index, validator_penalty), 
                                proposer_index, 
                                proposer_reward), 
                            whistleblower_index, 
                            (whistleblower_reward - proposer_reward)).balances);
            
        // @note    The triple nested mutation of balances is somewhat messy but for the moment it 
        //          allows slashed_validator to remain as a function method. 
        assert forall i :: (0 <= i < |s'.validators|) ==> 
                is_active_validator(s.validators[i], get_current_epoch(s)) 
                    == is_active_validator(s'.validators[i], get_current_epoch(s));

        assert  minimumActiveValidators(s');
        s'
    }


    ///////////////////////////////////////////////////////////////////////////////////////////
    //  Genesis - Genesis state 
    //  @note   initialize_beacon_state_from_eth1 & is_valid_genesis_state not implemented.
    ///////////////////////////////////////////////////////////////////////////////////////////


    ///////////////////////////////////////////////////////////////////////////////////////////
    //  Epoch processing - Helper functions
    ///////////////////////////////////////////////////////////////////////////////////////////

    /**
     * Return the matching source attestations.
     *
     *  @param  state   A beacon state.
     *  @param  epoch   An epoch which is either the state's epoch ior the previous one.
     *  @returns        The current (resp. previous) list of attestations if epoch is 
     *                  state's epoch (resp. epoch before state's epoch). 
     *
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
        requires get_previous_epoch(state) <= epoch <= get_current_epoch(state)
        requires is_valid_state_epoch_attestations(state)
        

        ensures |get_matching_source_attestations(state, epoch)| < 0x10000000000000000
        ensures is_valid_state_epoch_attestations(state)
    {
        if epoch == get_current_epoch(state) then
            state.current_epoch_attestations
        else 
            state.previous_epoch_attestations
    }  

    /**
     * Return the matching target attestations.
     *
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
        requires is_valid_state_epoch_attestations(state)
        
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
        requires is_valid_state_epoch_attestations(state)
        
        ensures |get_matching_head_attestations(state, epoch)| < 0x10000000000000000
        ensures forall a :: a in get_matching_head_attestations(state, epoch) ==>
                    a.data.slot < state.slot &&
                    state.slot - a.data.slot <= SLOTS_PER_HISTORICAL_ROOT &&
                    a.data.beacon_block_root == get_block_root_at_slot(state, a.data.slot)
    {
        var ax := get_matching_target_attestations(state, epoch);
        filterAttestationsyy(ax, state)
    }

    /**
     *  Collect attestations with a specific target.
     *
     *  @param  xl  A list of attestations.
     *  @param  br  A root value (hash of a block or block root). 
     *  @returns    The subset of `xl` that corresponds to attestation with target `r`.
     *  
     *  @note       This function is a helper to get_matching_target_attestations.
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

    /**
     *  Collect attestations with a specific target.
     *
     *  @param  x   A list of attestations.
     *  @param  s   A beacon state. 
     *  @returns    The subset of `xl` that corresponds to attestation with target.
     *  
     *  @note       This function is a helper to get_matching_head_attestations.
     */
    function method filterAttestationsyy(xl : seq<PendingAttestation>, s : BeaconState) : seq<PendingAttestation>
        ensures |filterAttestationsyy(xl, s)| <= |xl|
        ensures forall a :: a in xl && 
                            a.data.slot < s.slot &&
                            s.slot - a.data.slot <= SLOTS_PER_HISTORICAL_ROOT &&
                            a.data.beacon_block_root == get_block_root_at_slot(s, a.data.slot) 
                            <==> a in filterAttestationsyy(xl, s) 
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
    
    /** 
     *  Get the unslashed attesting indices.
     *
     *  @param  s               A beacon state.
     *  @param  attestations    A sequence of pending attestations.
     *  @returns                A sequence of validators such that the are all !slashed.
     */
    function method get_unslashed_attesting_indices(s: BeaconState, attestations: seq<PendingAttestation>): set<ValidatorIndex>
        requires is_valid_pending_attestions(s, attestations)

        //requires forall a :: a in attestations 
        //          ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        //requires forall a :: a in attestations 
        //          ==> TWO_UP_5 as nat 
        //              <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| 
        //              <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        //requires forall a :: a in attestations 
        //          ==> 0 
        //              < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| 
        //              <= MAX_VALIDATORS_PER_COMMITTEE as nat 

        ensures forall i  :: i in get_unslashed_attesting_indices(s, attestations) ==> i as nat < |s.validators|
        ensures forall i  :: i in get_unslashed_attesting_indices(s, attestations) ==> !s.validators[i].slashed
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

    /** 
     *  Check if a sequence of pending attestations meet the preconditions for 
     *  get_unslashed_attesting_indices.
     *
     *  @param  s               A beacon state.
     *  @param  attestations    A sequence of pending attestations.
     *  @returns                True if attestations meet the preconditions for 
     *                          valid attestations.
     *  
     *  @note   This function is a helper to several functions.
     */
    predicate is_valid_pending_attestions(s: BeaconState, attestations: seq<PendingAttestation>)
    {
        (forall a :: a in attestations 
            ==> is_valid_number_active_validators(|get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))|))
        && (forall a :: a in attestations 
            ==> is_valid_committee_index(a.data.index, get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot))))
        && (forall a :: a in attestations 
            ==> is_valid_beacon_committee_length(|get_beacon_committee(s, a.data.slot, a.data.index)|, |a.aggregation_bits|))
    }

    /** 
     *  Check if the current_epoch_attestations and previous_epoch_attestations are valid. 
     *
     *  @param  s               A beacon state.
     *  @returns                True if the attestations meet the preconditions for 
     *                          valid attestations.
     *  
     *  @note   This function is a helper to several functions.
     */
    predicate is_valid_state_epoch_attestations(s: BeaconState)
    {
        is_valid_pending_attestions(s, s.current_epoch_attestations)
        && is_valid_pending_attestions(s, s.previous_epoch_attestations)
    }
    
    /** 
     * Helper for get_unslashed_attesting_indices to implement recursion. 
     *
     *  @param  s       A beacon state.
     *  @param  indices A sequence of validator indices.
     *  @returns        Those indices such that !s.validators[i].slashed.
     *  
     *  @note   This function is a helper to get_unslashed_attesting_indices.
     */
    function method unslashed_attesting_indices_helper(s: BeaconState, indices: set<ValidatorIndex>): set<ValidatorIndex>
        requires forall i  :: i in indices ==> i as nat < |s.validators|

        ensures forall i  :: i in unslashed_attesting_indices_helper(s, indices) ==> i as nat < |s.validators|
        ensures forall i  :: i in unslashed_attesting_indices_helper(s, indices) ==> !s.validators[i].slashed
    {
       if indices == {} then {}
       else 
            var x := PickIndex(indices);
            if !s.validators[x].slashed then {x} + unslashed_attesting_indices_helper(s, indices - {x})
            else unslashed_attesting_indices_helper(s, indices - {x})
    }

    /** 
     * Return the combined effective balance of the set of unslashed validators 
     * participating in ``attestations``.
     *
     *  @param  s               A beacon state.
     *  @param  attestations    A sequence of pending attestations.
     *  @returns               The combined effective balance of unslashed validators.
     *  
     *  @note   This function is currently set to  a default value.
     */
    function method get_attesting_balance(state: BeaconState, attestations: seq<PendingAttestation>) : Gwei 
        requires |attestations| < 0x10000000000000000
        //ensures EFFECTIVE_BALANCE_INCREMENT <= get_attesting_balance(s, attestations) 
    {
        // get_total_balance(state, get_unslashed_attesting_indices(state, attestations))
        |attestations| as Gwei 
    }


    ///////////////////////////////////////////////////////////////////////////////////////////
    //  Epoch processing - Rewards and penalties helper functions
    ///////////////////////////////////////////////////////////////////////////////////////////

    /** 
     * Return the base reward.
     *
     *  @param  s       A beacon state.
     *  @param  index   A sequence of pending attestations.
     *  @returns        The base reward.
     *
     *  @note   Consider adding a lower bound.
     *  @note   This function uses the axiom AssumeNoGweiOverflow.
     */
    function method get_base_reward(s: BeaconState, index: ValidatorIndex) : Gwei
        requires index as nat < |s.validators|
        //requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        //requires integer_square_root(get_total_active_balance_full(s)) > 1
        // requires s.validators[index].effective_balance as nat 
        //         * BASE_REWARD_FACTOR as nat
        //         / integer_square_root(get_total_active_balance_full(s)) as nat 
        //         / BASE_REWARDS_PER_EPOCH as nat
        //         < 0x10000000000000000
    {
        var total_balance : Gwei := get_total_active_balance_full(s);
        assert integer_square_root(total_balance) > 1;
        
        var br := s.validators[index].effective_balance as nat 
                * BASE_REWARD_FACTOR as nat
                / integer_square_root(total_balance) as nat 
                / BASE_REWARDS_PER_EPOCH as nat;
        AssumeNoGweiOverflow(br as nat);
        
        br as Gwei 
    }

    /** 
     * Return the proposer reward.
     *
     *  @param  s                   A beacon state.
     *  @param  attesting_index     A sequence of pending attestations.
     *  @returns                    The proposer reward.
     */
    function method get_proposer_reward(s: BeaconState, attesting_index: ValidatorIndex): Gwei
        requires attesting_index as nat < |s.validators|
        //requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        //requires integer_square_root(get_total_active_balance_full(s)) > 1
        // requires s.validators[attesting_index].effective_balance as nat 
        //         * BASE_REWARD_FACTOR as nat 
        //         / integer_square_root(get_total_active_balance_full(s)) as nat 
        //         / BASE_REWARDS_PER_EPOCH as nat
        //         < 0x10000000000000000
    {
        (get_base_reward(s, attesting_index) / PROPOSER_REWARD_QUOTIENT) as Gwei  
    }
    
    /** 
     * Return the finality delay.
     *
     *  @param  s       A beacon state.
     *  @returns        The finality delay.
     *
     *  @note   This function uses the axiom AssumeFinalisedCheckpointBeforeCurrentEpoch.
     */
    function method get_finality_delay(s: BeaconState): uint64
        //requires s.finalised_checkpoint.epoch <= get_previous_epoch(s) 
    {
        AssumeFinalisedCheckpointBeforeCurrentEpoch(s, get_previous_epoch(s));
        get_previous_epoch(s) - s.finalised_checkpoint.epoch
    }
     
    /** 
     * Check if the finality delay > MIN_EPOCHS_TO_INACTIVITY_PENALTY.
     *
     *  @param  s       A beacon state.
     *  @returns        True if finality delay > MIN_EPOCHS_TO_INACTIVITY_PENALTY.
     *
     *  @note   This function uses the axiom AssumeFinalisedCheckpointBeforeCurrentEpoch.
     */
    predicate method is_in_inactivity_leak(s: BeaconState)
        //requires s.finalised_checkpoint.epoch <= get_previous_epoch(s) 
    {
        AssumeFinalisedCheckpointBeforeCurrentEpoch(s, get_previous_epoch(s));
        get_finality_delay(s) > MIN_EPOCHS_TO_INACTIVITY_PENALTY
    }
    
    /** 
     * Get eligible validator indices. 
     *
     *  @param  s       A beacon state.
     *  @returns        Those indices such that !s.validators[i].slashed.
     */
    function method get_eligible_validator_indices(s: BeaconState): seq<ValidatorIndex>
        ensures forall i :: 0 <= i < |get_eligible_validator_indices(s)|  
            ==> get_eligible_validator_indices(s)[i] as nat < |s.validators|
    {
        var previous_epoch := get_previous_epoch(s);
        get_eligible_validator_indices_helper(s.validators, previous_epoch)
    }

    /** 
     * Helper for get_eligible_validator_indices to implement recursion. 
     *
     *  @param  v       A list of validators.
     *  @param  pe      An epoch (previous epoch).
     *  @returns        Those indices such that are eligible.
     *  
     *  @note   This function is a helper to get_eligible_validator_indices.
     */
    function method get_eligible_validator_indices_helper(v: ListOfValidators, pe: Epoch): seq<ValidatorIndex>
        ensures forall i :: 0 <= i < |get_eligible_validator_indices_helper(v, pe)|  
            ==> get_eligible_validator_indices_helper(v, pe)[i] as nat < |v|
    {
        if |v| == 0 then []
        else 
            if is_active_validator(v[|v|-1], pe) || (v[|v|-1].slashed 
                && (pe as nat + 1 < v[|v|-1].withdrawable_epoch as nat)) 
            then
                get_eligible_validator_indices_helper(v[..|v|-1], pe) 
                    + [(|v|-1) as ValidatorIndex]
            else 
                get_eligible_validator_indices_helper(v[..|v|-1], pe)
    }
    
    /** 
     * Helper with shared logic for use by get source, target, and head deltas functions. 
     *
     *  @param  s               A beacon state.
     *  @param  attestations    A sequence of pending attestations.
     *  @returns                The attestation component deltas.
     */
    function method get_attestation_component_deltas(s: BeaconState, attestations: seq<PendingAttestation>) : (seq<Gwei>,seq<Gwei>)
        requires is_valid_pending_attestions(s, attestations)

        ensures |get_attestation_component_deltas(s, attestations).0| 
                == |get_attestation_component_deltas(s, attestations).1| 
                == |s.validators|
    {
        var rewards : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var penalties : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var total_balance := get_total_active_balance_full(s);
        var unslashed_attesting_indices := get_unslashed_attesting_indices(s, attestations);
        var attesting_balance := get_total_balance(s, unslashed_attesting_indices);
        var indices := get_eligible_validator_indices(s);

        get_attestation_component_deltas_helper(s, 
                                                indices, 
                                                total_balance, 
                                                unslashed_attesting_indices, 
                                                attesting_balance, 
                                                rewards, 
                                                penalties
                                               )
        
    }

    /** 
     * Helper to get_attestation_component_deltas to perform recursion. 
     *
     *  @param  s                           A beacon state.
     *  @param  indices                     A sequence of eligible validator indices.
     *  @param  total_balance               The total balance of active validators.
     *  @param  unslashed_attesting_indices A sequence of unslashed attesting indices.
     *  @param  rewards                     A sequence of rewards.
     *  @param  penalties                   A sequence of penalties.
     *  @returns                            The updated rewards and penalties.
     *  
     *
     *  @note   This function uses the axiom AssumeNoGweiOverflow.
     *  @note   The AssumeNoGweiOverflow() statements could potentially be removed by
     *          providing further lower/upper bounds on the components.
     */
    function method get_attestation_component_deltas_helper(s: BeaconState, 
                                                            indices: seq<ValidatorIndex>, 
                                                            total_balance: Gwei,
                                                            unslashed_attesting_indices: set<ValidatorIndex>,
                                                            attesting_balance: Gwei,
                                                            rewards: seq<Gwei>,
                                                            penalties: seq<Gwei>
                                                           ) : (seq<Gwei>,seq<Gwei>)
        requires |rewards| == |penalties| == |s.validators|
        requires total_balance >= EFFECTIVE_BALANCE_INCREMENT 
        requires attesting_balance >= EFFECTIVE_BALANCE_INCREMENT 
        requires forall i :: 0 <= i < |indices| ==> indices[i] as nat < |s.validators|
        
        ensures |get_attestation_component_deltas_helper(s, 
                                                         indices, 
                                                         total_balance, 
                                                         unslashed_attesting_indices, 
                                                         attesting_balance, 
                                                         rewards, 
                                                         penalties
                                                         ).0| == |rewards| == |s.validators|
        ensures |get_attestation_component_deltas_helper(s, 
                                                         indices, 
                                                         total_balance, 
                                                         unslashed_attesting_indices, 
                                                         attesting_balance, 
                                                         rewards, 
                                                         penalties
                                                         ).1| == |penalties| == |s.validators|
    {
        if |indices| == 0 then (rewards, penalties)
        else
            var index := indices[0];
            var base := get_base_reward(s, index);
            
            if index in unslashed_attesting_indices then
                var increment := EFFECTIVE_BALANCE_INCREMENT;
                
                var rewards_numerator :=  base as nat * (attesting_balance as nat / increment as nat); 
                
                assert (total_balance as nat / increment as nat) >= 1;
                assert (attesting_balance as nat / increment as nat) >= 1;
                
                if is_in_inactivity_leak(s) then    
                    var r := rewards[index as nat] as nat + base as nat;
                    AssumeNoGweiOverflow(r);
                    get_attestation_component_deltas_helper(s, 
                                                            indices[1..], 
                                                            total_balance, 
                                                            unslashed_attesting_indices, 
                                                            attesting_balance, 
                                                            rewards[index as nat := r as Gwei], 
                                                            penalties
                                                           )
                else
                    var r := rewards[index as nat] as nat + rewards_numerator as nat / (total_balance as nat / increment as nat);
                    AssumeNoGweiOverflow(r);
                    get_attestation_component_deltas_helper(s, 
                                                            indices[1..], 
                                                            total_balance, 
                                                            unslashed_attesting_indices, 
                                                            attesting_balance, 
                                                            rewards[index as nat := r as Gwei], 
                                                            penalties
                                                           )
            else
                var p:= penalties[index as nat] as nat + base as nat;
                AssumeNoGweiOverflow(p);
                get_attestation_component_deltas_helper(s, 
                                                        indices[1..], 
                                                        total_balance, 
                                                        unslashed_attesting_indices, 
                                                        attesting_balance, 
                                                        rewards, 
                                                        penalties[index as nat := p as Gwei]
                                                        )
    }
    
    /** 
     * Return attester micro-rewards/penalties for source-vote for each validator.
     *
     *  @param  s               A beacon state.
     *  @returns                (rewards,penalties).
     */
    function method get_source_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires is_valid_state_epoch_attestations(s)

        ensures |get_source_deltas(s).0| == |get_source_deltas(s).1| == |s.validators|
    {
        var matching_source_attestations := get_matching_source_attestations(s, get_previous_epoch(s));
        get_attestation_component_deltas(s, matching_source_attestations)
    }

    /** 
     * Return attester micro-rewards/penalties for target-vote for each validator.
     *
     *  @param  s               A beacon state.
     *  @returns                (rewards,penalties).
     */
    function method get_target_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat
        requires 1 <= get_previous_epoch(s) <= get_current_epoch(s)
        requires is_valid_state_epoch_attestations(s)

        ensures |get_target_deltas(s).0| == |get_target_deltas(s).1| == |s.validators|
    {
        var matching_target_attestations := get_matching_target_attestations(s, get_previous_epoch(s));
        get_attestation_component_deltas(s, matching_target_attestations)
    }

    /** 
     * Return attester micro-rewards/penalties for head-vote for each validator.
     *
     *  @param  s               A beacon state.
     *  @returns                (rewards,penalties).
     */
    function method get_head_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat
        requires 1 <= get_previous_epoch(s) <= get_current_epoch(s)
        requires is_valid_state_epoch_attestations(s)
        
        ensures |get_head_deltas(s).0| == |get_head_deltas(s).1| == |s.validators|
    {
        var matching_head_attestations := get_matching_head_attestations(s, get_previous_epoch(s));
        get_attestation_component_deltas(s, matching_head_attestations)
    }

    /** 
     * Return proposer and inclusion delay micro-rewards/penalties for each validator.
     *
     *  @param  s               A beacon state.
     *  @returns                (rewards,penalties).
     */
    function method get_inclusion_delay_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires is_valid_state_epoch_attestations(s)
        ensures |get_inclusion_delay_deltas(s).0| == |get_inclusion_delay_deltas(s).1| == |s.validators|
    {
        var rewards : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var penalties : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var matching_source_attestations := get_matching_source_attestations(s, get_previous_epoch(s));
        var unslashed_attesting_indices := get_unslashed_attesting_indices(s, matching_source_attestations);

        get_inclusion_delay_deltas_helper(s, 
                                          unslashed_attesting_indices, 
                                          matching_source_attestations, 
                                          rewards, 
                                          penalties
                                         )
    }

    /** 
     * Helper to get_attestation_component_deltas to perform recursion. 
     *
     *  @param  s                               A beacon state.
     *  @param  unslashed_attesting_indices     A sequence of unslashed attesting indices.
     *  @param  matching_source_attestations    A sequence of umatching source attestations.
     *  @param  rewards                         A sequence of rewards.
     *  @param  penalties                       A sequence of penalties.
     *  @returns                                The updated rewards and penalties.
     *  
     *
     *  @note   This function uses the axiom AssumeNoGweiOverflow.
     *  @note   The AssumeNoGweiOverflow() statements could potentially be removed by
     *          providing further lower/upper bounds on the components.
     */
    function method get_inclusion_delay_deltas_helper(s: BeaconState, 
                                                      unslashed_attesting_indices: set<ValidatorIndex>, 
                                                      matching_source_attestations: seq<PendingAttestation>, 
                                                      rewards: seq<Gwei>, 
                                                      penalties: seq<Gwei>
                                                     ) : (seq<Gwei>,seq<Gwei>)
        requires |rewards| == |penalties| == |s.validators|
        requires forall i :: i in unslashed_attesting_indices ==> i as int < |s.validators|
        
        ensures |get_inclusion_delay_deltas_helper(s, 
                                                   unslashed_attesting_indices, 
                                                   matching_source_attestations, 
                                                   rewards, 
                                                   penalties
                                                   ).0| == |rewards| == |s.validators|
        ensures |get_inclusion_delay_deltas_helper(s, 
                                                   unslashed_attesting_indices, 
                                                   matching_source_attestations, 
                                                   rewards, 
                                                   penalties
                                                   ).1| == |penalties| == |s.validators|
    {
        if unslashed_attesting_indices == {} then (rewards, penalties)
        else
            var index := PickIndex(unslashed_attesting_indices);
            var attestation := get_min_attestation(matching_source_attestations, index, |rewards|);
            
            var r := rewards[attestation.proposer_index as nat] as nat + get_proposer_reward(s, index) as nat;
            AssumeNoGweiOverflow(r);
            
            // intermediate rewards update
            var rewards' := rewards[attestation.proposer_index as nat := r as Gwei];
            var max_attester_reward := get_base_reward(s, index) - get_proposer_reward(s, index);

            AssumeAttesttionInclusionDelayGreaterThanZero(attestation);
            var r2 := rewards'[index as nat] as nat + max_attester_reward as nat / attestation.inclusion_delay as nat;
            AssumeNoGweiOverflow(r2);
            
            get_inclusion_delay_deltas_helper(s, 
                                              unslashed_attesting_indices - {index}, 
                                              matching_source_attestations, 
                                              rewards'[index as nat := r2 as Gwei], 
                                              penalties         
                                             ) // no penalties
    }

    /** 
     * Helper to get_attestation_component_deltas_helper to get the min attestation
     * for a particular index.
     *
     *  @note   This function has not been implemented but is assumed.
     */
    function method {:axiom} get_min_attestation(sa : seq<PendingAttestation>, 
                                        index: ValidatorIndex,
                                        index_bound: nat) : PendingAttestation
        ensures get_min_attestation(sa, index, index_bound).proposer_index as nat < index_bound
    // {}
    
    /** 
     * Return inactivity reward/penalty deltas for each validator.
     *
     *  @param  s               A beacon state.
     *  @returns                (rewards,penalties).
     */
    function method get_inactivity_penalty_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat
        requires s.slot - get_previous_epoch(s) *  SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT 
        requires 1 <= get_previous_epoch(s) //<= get_current_epoch(s)
        requires is_valid_state_epoch_attestations(s)
 
        ensures |get_inactivity_penalty_deltas(s).0| == |get_inactivity_penalty_deltas(s).1| == |s.validators|
    {
        var rewards : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var penalties : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);

        if (is_in_inactivity_leak(s)) then
            var matching_target_attestations 
                    := get_matching_target_attestations(s, get_previous_epoch(s));
            var matching_target_attesting_indices 
                    := get_unslashed_attesting_indices(s, matching_target_attestations);
            var eligible_validator_indices 
                    := get_eligible_validator_indices(s);
            get_inactivity_penalty_deltas_helper(s, 
                                                 eligible_validator_indices, 
                                                 matching_target_attesting_indices, 
                                                 rewards, 
                                                 penalties
                                                )
        else    
            (rewards,penalties)
    }

    /** 
     * Helper to get_attestation_component_deltas to perform recursion. 
     *
     *  @param  s                   A beacon state.
     *  @param  eligible_indices    A sequence of eligible indices.
     *  @param  target_indicess     A sequence of matching target attestations.
     *  @param  rewards             A sequence of rewards.
     *  @param  penalties           A sequence of penalties.
     *  @returns                    The updated rewards and penalties.
     *  
     *  @note   This function uses the axiom AssumeNoGweiOverflow.
     *  @note   The AssumeNoGweiOverflow() statements could potentially be removed by
     *          providing further lower/upper bounds on the components.
     */
    function method get_inactivity_penalty_deltas_helper(s: BeaconState, 
                                                         eligible_indices: seq<ValidatorIndex>, 
                                                         target_indices: set<ValidatorIndex>,
                                                         rewards: seq<Gwei>,
                                                         penalties: seq<Gwei>
                                                        ) : (seq<Gwei>,seq<Gwei>)
        requires |rewards| == |penalties| == |s.validators|
        requires forall i :: 0 <= i < |eligible_indices| 
                    ==> eligible_indices[i] as nat < |s.validators|
        
        ensures |get_inactivity_penalty_deltas_helper(s, 
                                                      eligible_indices, 
                                                      target_indices, 
                                                      rewards, 
                                                      penalties
                                                     ).0| == |rewards| == |s.validators|
        ensures |get_inactivity_penalty_deltas_helper(s, 
                                                      eligible_indices, 
                                                      target_indices, 
                                                      rewards, 
                                                      penalties
                                                    ).1| == |penalties| == |s.validators|
    {
        if |eligible_indices| == 0 then (rewards, penalties)
        else
            var base_reward := get_base_reward(s,eligible_indices[0]);
            var proposer_reward := get_proposer_reward(s, eligible_indices[0]);
            var first_part_of_penalty := BASE_REWARDS_PER_EPOCH as nat 
                                            * base_reward as nat 
                                            - proposer_reward as nat;
            AssumeNoGweiOverflow(first_part_of_penalty);

            if eligible_indices[0] !in target_indices then
                var effective_balance := s.validators[eligible_indices[0] as nat].effective_balance as nat;
                assert INACTIVITY_PENALTY_QUOTIENT as nat > 0;

                var temp : nat := effective_balance as nat * get_finality_delay(s) as nat;
                var second_part_of_penalty : nat := (temp / INACTIVITY_PENALTY_QUOTIENT as nat) as nat;
                AssumeNoGweiOverflow(second_part_of_penalty);
                var total_penalty := penalties[eligible_indices[0] as nat] as nat 
                                        + first_part_of_penalty as nat 
                                        + second_part_of_penalty as nat;
                AssumeNoGweiOverflow(total_penalty);
                var penalties' := penalties[eligible_indices[0] as nat := total_penalty as Gwei];
                assert |penalties'| == |penalties|;
                get_inactivity_penalty_deltas_helper(s, eligible_indices[1..], target_indices, rewards, penalties')
            else
                var total_penalty := penalties[eligible_indices[0] as nat] as nat + first_part_of_penalty as nat;
                AssumeNoGweiOverflow(total_penalty);
                var penalties' := penalties[eligible_indices[0] as nat := total_penalty as Gwei];
                assert |penalties'| == |penalties|;
                get_inactivity_penalty_deltas_helper(s, eligible_indices[1..], target_indices, rewards, penalties')
    }

    /** 
     * Return attestation reward/penalty deltas for each validator.
     *
     *  @param  s               A beacon state.
     *  @returns                (rewards,penalties).
     */
    function method get_attestation_deltas(s: BeaconState) : (seq<Gwei>, seq<Gwei>)
        requires 1 <= get_previous_epoch(s) //<= get_current_epoch(s)
        // i.e. this means it isn't applicable to the GENESIS_EPOCH
        requires is_valid_state_epoch_attestations(s)

        ensures |get_attestation_deltas(s).0| == |get_attestation_deltas(s).1| == |s.validators|
    {
        var rewards : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var penalties : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var (sr, sp) := get_source_deltas(s);
        var (tr, tp) := get_target_deltas(s);
        var (hr, hp) := get_head_deltas(s);
        var (ddr, ddp) := get_inclusion_delay_deltas(s);
        var (pdr, pdp) := get_inactivity_penalty_deltas(s);

        assert |sr| == |tr| == |hr| == |ddr| == |pdr| == |s.validators|;
        assert |sp| == |tp| == |hp| == |ddp| == |pdp| == |s.validators|;

        (get_attestation_deltas_helper_sum_rewards(sr, tr, hr, ddr, pdr, rewards),
         get_attestation_deltas_helper_sum_penalties(sp, tp, hp, ddp, pdp, penalties)
        )
    }

    /** 
     * Helper to recurse through the rewards updates in get_attestation_deltas. 
     *  
     *  @note   This function uses the axiom AssumeNoGweiOverflow.
     *  @note   The AssumeNoGweiOverflow() statements could potentially be removed by
     *          providing further lower/upper bounds on the components.
     */
    function method get_attestation_deltas_helper_sum_rewards(sr: seq<Gwei>, 
                                                              tr: seq<Gwei>, 
                                                              hr: seq<Gwei>, 
                                                              ddr: seq<Gwei>, 
                                                              pdr: seq<Gwei>, 
                                                              rewards: seq<Gwei>
                                                             ) : seq<Gwei>
        requires |sr| == |tr| == |hr| == |ddr| == |pdr| <= |rewards|
        ensures |get_attestation_deltas_helper_sum_rewards(sr, tr, hr, ddr, pdr, rewards)| 
                == |rewards|
    {
        if |sr| == 0 then rewards
        else   
            var r0 := rewards[0] as nat + sr[0] as nat + tr[0] as nat + hr[0] as nat + ddr[0] as nat + pdr[0] as nat;
            AssumeNoGweiOverflow(r0);
            get_attestation_deltas_helper_sum_rewards(sr[1..], 
                                                        tr[1..], 
                                                        hr[1..], 
                                                        ddr[1..], 
                                                        pdr[1..], 
                                                        rewards[0 := r0 as Gwei]
                                                        )
    }

    /** 
     * Helper to recurse through the penalties updates in get_attestation_deltas. 
     *  
     *  @note   This function uses the axiom AssumeNoGweiOverflow.
     *  @note   The AssumeNoGweiOverflow() statements could potentially be removed by
     *          providing further lower/upper bounds on the components.
     */
    function method get_attestation_deltas_helper_sum_penalties(sp: seq<Gwei>, 
                                                                tp: seq<Gwei>, 
                                                                hp: seq<Gwei>, 
                                                                ddp: seq<Gwei>, 
                                                                pdp: seq<Gwei>, 
                                                                penalties: seq<Gwei>
                                                               ) : seq<Gwei>
        requires |sp| == |tp| == |hp| == |ddp| == |pdp| <= |penalties|
        ensures |get_attestation_deltas_helper_sum_penalties(sp, tp, hp, ddp, pdp, penalties)| 
                == |penalties|
    {
        if |sp| == 0 then penalties
        else    
            var p0 := penalties[0] as nat + sp[0] as nat + tp[0] as nat + hp[0] as nat + ddp[0] as nat + pdp[0] as nat;
            AssumeNoGweiOverflow(p0);
            get_attestation_deltas_helper_sum_penalties(sp[1..], 
                                                        tp[1..], 
                                                        hp[1..], 
                                                        ddp[1..], 
                                                        pdp[1..], 
                                                        penalties[0 := p0 as Gwei]
                                                    )
    }


    ///////////////////////////////////////////////////////////////////////////////////////////
    //  Block processing - Operations helper functions
    ///////////////////////////////////////////////////////////////////////////////////////////

    /**
     * Extract a validator from a single deposit.
     *
     *  @param  d       A single deposit.
     *  @returns        A validator created from the deposit information
     *
     *  @note           The `effective_balance` is not an active field in the current model 
     *                  but the code to set this field is included as a comment for future 
     *                  reference.
     */
    function method get_validator_from_deposit(d: Deposit): Validator
        ensures get_validator_from_deposit(d).effective_balance <= MAX_EFFECTIVE_BALANCE as Gwei
    {
        var amount := d.data.amount; 
        var effective_balance 
                := min((amount as nat- amount as nat % EFFECTIVE_BALANCE_INCREMENT as nat) as nat, 
                        MAX_EFFECTIVE_BALANCE as nat
                      );

        Validator(
                d.data.pubkey, 
                d.data.withdrawal_credentials,
                effective_balance as Gwei, 
                false, 
                FAR_FUTURE_EPOCH, 
                FAR_FUTURE_EPOCH, 
                FAR_FUTURE_EPOCH, 
                FAR_FUTURE_EPOCH,
                DEFAULT_EXECUTION_ADDRESS
                )
    }

    ///////////////////////////////////////////////////////////////////////////////////////////
    // Additional misc helper functions, predicates and lemmas
    // @note    These functions are not included in the spec but are needed in Dafny.
    //          In many cases they provide functionality that is built in to Python but
    //          not built in to Dafny, e.g. append functionality for sequences.
    ///////////////////////////////////////////////////////////////////////////////////////////

    // Helper function methods

    /**
     *  Append a new validator.
     *
     *  @param      sv      A list of validators.
     *  @param      v       A validator.
     *  @returns            sv.append(v).
     */
    function method validator_append(sv: ListOfValidators, v: Validator): ListOfValidators
        requires |sv| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
    {
        sv + [v]
    }
    
    /**
     *  Append a new balance entry.
     *
     *  @param      sb      A list of balances.
     *  @param      b       A balance.
     *  @returns            sb.append(b).
     */
    function method balance_append(sb: ListOfBalances, b: Gwei): ListOfBalances
        requires |sb| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
    {
        sb + [b]
    }

     /**
     *  Get the index of a validator. 
     *
     *  @param      pk      A sequence of BLSPubkeys.
     *  @param      pubkey  A pubkey.
     *  @returns            i such that pk[i] == pubkey.
     *
     *  @note   Helper function as no alternative indexing functionality available.
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

    /**
     *  Sorted intersection of two sets of sorted validator indices.
     *
     *  @param      a   A sorted list of validators.
     *  @param      b   A sorted list of validators.
     *  @returns        The sorted intersection of a and b.
     */
    function method sorted_intersection(a : seq<ValidatorIndex>, b: seq<ValidatorIndex>): seq<uint64>
        requires forall i,j :: 0 <= i < j < |a| ==> a[i] < a[j]
        requires forall i,j :: 0 <= i < j < |b| ==> b[i] < b[j]
        ensures forall i,j :: 0 <= i < j < |sorted_intersection(a,b)| 
                ==> sorted_intersection(a,b)[i] < sorted_intersection(a,b)[j]
        ensures forall i :: 0 <= i < |sorted_intersection(a,b)| 
                ==> sorted_intersection(a,b)[i] as ValidatorIndex in a 
                    && sorted_intersection(a,b)[i] as ValidatorIndex in b
        ensures sorted_intersection(a,b) == sorted_intersection_fn(a,b)
    {
        if |a| == 0 then []
        else (if a[0] in b then [a[0] as uint64] else []) + sorted_intersection(a[1..], b)
    }

    /**
     *  Get the exit epoches from a list of validators, excluding any equal to FAR_FUTURE_EPOCH .
     *
     *  @param      sv      A list of validators.
     *  @returns            A sequence of epochs such that none are the FAR_FUTURE_EPOCH.
     */
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

    /**
     *  Get the validators whose exit epoch is the exit_queue_epcoh.
     *
     *  @param      sv                  A list of validators.
     *  @param      exit_queue_epoch    An epoch.
     *  @returns                        A list of validators.
     */
    function method get_queue_churn(sv: ListOfValidators, exit_queue_epoch: Epoch) : seq<Validator>
    {
        if |sv| == 0 
            then []
        else 
            if sv[0].exitEpoch == exit_queue_epoch 
                then [sv[0]] + get_queue_churn(sv[1..], exit_queue_epoch)
                else get_queue_churn(sv[1..], exit_queue_epoch)
    }

    /**
     *  Get the maximum epoches.
     *
     *  @param      se      A sequence of epochs.
     *  @returns            The largest epoch in se.
     */
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
     *  @returns    True if all bits are set to 1.
     */
    function method all(xs: seq<bool>) : bool
    {
        forall i :: 0 < i < |xs| ==> xs[i]
    }
    
    /**
     *  Count instances of d in a list of eth1_data.
     *
     *  @param      l   A list of Eth1 data.
     *  @param      d   Eth1 data.  
     *  @returns    The number of matches of d within l.
     */
     function method count_eth1_data_votes(l: ListOfEth1Data, d: Eth1Data) : nat
    {
        if |l| == 0 then 0
        else 
            if (l[0] == d) then 1 + count_eth1_data_votes(l[1..], d)
            else count_eth1_data_votes(l[1..], d)
     }
    
    /** 
     * Returns the list of validators eligible for activation.
     *
     *  @param  s   A beacon state.
     *  @param  i   A positive integer.
     *  @returns    The list of validators eligible for activation.
     */
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

    /** 
     * Returns the total slashings amount.
     *
     *  @param  slashings   A sequence of gwei.
     *  @returns            The sum of ``slashings``.
     *
     *  @note   This function uses the axiom AssumeNoGweiOverflow.
     */
    function method get_total_slashings(slashings: seq<Gwei>): Gwei
    {
        if |slashings| == 0 then 0 as Gwei
        else 
            var total := slashings[0] as nat + get_total_slashings(slashings[1..]) as nat;
            AssumeNoGweiOverflow(total);
            total as Gwei
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
     *  Sete the effective balance at index ``index`` to ``eb``.
     *
     *  @param  s       A beacon state.
     *  @param  index   A validator index.
     *  @param  eb      A gwei amount.
     *  @returns        A new state where the validator effective balance at ``index`` is 
     *                  set to ``eb``.
     */
    function method set_effective_balance(s: BeaconState, index: ValidatorIndex, eb: Gwei): BeaconState 
        requires index as int < |s.validators| 
        requires eb as nat < 0x10000000000000000
        ensures |s.validators| == |set_effective_balance(s, index, eb).validators|
        ensures set_effective_balance(s,index,eb).validators[index].effective_balance == eb
        ensures set_effective_balance(s,index,eb) == s.(validators := set_effective_balance(s,index,eb).validators)
    {
        s.(validators := s.validators[index as nat := s.validators[index].(effective_balance := eb as Gwei)])
    }

    /** 
     *  Sete the activation_eligibility_epoch at index ``index`` to ``e``.
     *
     *  @param  s       A beacon state.
     *  @param  index   A validator index.
     *  @param     e    An epoch.
     *  @returns        A new state where the validator activation_eligibility_epoch at ``index`` is 
     *                  set to ``e``.
     */
    function method set_activation_eligibility_epoch(s: BeaconState, index: ValidatorIndex, e: Epoch): BeaconState 
        requires index as int < |s.validators| 
        requires e as nat < 0x10000000000000000
        ensures |s.validators| == |set_activation_eligibility_epoch(s, index, e).validators|
        ensures set_activation_eligibility_epoch(s,index,e).validators[index].activation_eligibility_epoch == e
        ensures set_activation_eligibility_epoch(s,index,e) == s.(validators := set_activation_eligibility_epoch(s,index,e).validators)
    {
        s.(validators := s.validators[index as nat := s.validators[index].(activation_eligibility_epoch := e)])
    }

    /** 
     *  Sete the activation_epoch at index ``index`` to ``e``.
     *
     *  @param  s       A beacon state.
     *  @param  index   A validator index.
     *  @param     e    An epoch.
     *  @returns        A new state where the validator activation_epoch at ``index`` is 
     *                  set to ``e``.
     */
    function method set_activation_epoch(s: BeaconState, index: ValidatorIndex, e: Epoch): BeaconState 
        requires index as int < |s.validators| 
        requires e as nat < 0x10000000000000000
        ensures |s.validators| == |set_activation_epoch(s, index, e).validators|
        ensures set_activation_epoch(s,index,e).validators[index].activation_epoch == e
        ensures set_activation_epoch(s,index,e) == s.(validators := set_activation_epoch(s,index,e).validators)
    {
        s.(validators := s.validators[index as nat := s.validators[index].(activation_epoch := e)])
    }

    /**
     *  Return the sequence of validator eligible for activation.
     *
     *  @param  s       A beacon state.
     *  @returns        The the sequence of validator indices such that for all indices returned 
     *                  is_eligible_for_activation is true. 
     */
    function method get_validator_indices_activation_eligible(sv: ListOfValidators, fce: Epoch) : seq<ValidatorIndex>
        ensures |get_validator_indices_activation_eligible(sv, fce)| <= |sv|
        ensures forall i :: 0 <= i < |get_validator_indices_activation_eligible(sv, fce)| 
                ==> get_validator_indices_activation_eligible(sv, fce)[i] as nat < |sv|
        ensures forall i :: 0 <= i < |get_validator_indices_activation_eligible(sv, fce)| 
                ==> sv[get_validator_indices_activation_eligible(sv, fce)[i] ].activation_eligibility_epoch 
                    <= fce 
                    && sv[get_validator_indices_activation_eligible(sv, fce)[i]].activation_epoch == FAR_FUTURE_EPOCH
    {
        if |sv| == 0 then []
        else 
            //if is_eligible_for_activation()
            if sv[|sv|-1].activation_eligibility_epoch <= fce 
                    && sv[|sv|-1].activation_epoch == FAR_FUTURE_EPOCH 
            then get_validator_indices_activation_eligible(sv[..|sv|-1], fce) + [(|sv|-1) as ValidatorIndex]
            else get_validator_indices_activation_eligible(sv[..|sv|-1], fce)
    }

    
    /**
     *  The set of validators attesting to a target is larger than the set 
     *  of validators attesting to a link with that target. 
     *
     *  @param  xa      A seq of attestations.
     *  @param  src     The source checkpoint of the link.
     *  @param  tgt     The target checkpoint of the link.
     */
    lemma {:induction xa} attForTgtLargerThanLinks(xa : seq<PendingAttestation>, 
                                                   src : CheckPoint, 
                                                   tgt: CheckPoint)
        ensures collectValidatorsAttestatingForLink(xa, src, tgt) 
                <= collectValidatorsIndicesAttestatingForTarget(xa, tgt) 
        ensures |collectValidatorsAttestatingForLink(xa, src, tgt)| 
                <= |collectValidatorsIndicesAttestatingForTarget(xa, tgt)| 
    {
        assert(collectValidatorsAttestatingForLink(xa, src, tgt) 
            <= collectValidatorsIndicesAttestatingForTarget(xa, tgt) );
        cardIsMonotonic(collectValidatorsAttestatingForLink(xa, src, tgt), 
                        collectValidatorsIndicesAttestatingForTarget(xa, tgt)
                        );
    }

    // Helper predicates 

    /**
     *  Check if there is at least one active validator for a given epoch..
     *
     *  @param      s       A beacon state.
     *  @param      epoch   A beacon state.
     *  @returns            True if there exists a validator that is active in the 
     *                      current epoch, otherwise False.
     *  @note       This predicate is not specified in the spec but acts as a helper
     *              to other components where a there must be at least one active validator.
     */
    predicate minimumActiveValidators(s: BeaconState)
        ensures minimumActiveValidators(s) 
            ==> |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
    {
        //|get_active_validator_indices(s.validators, get_current_epoch(s))| > 0
        exists i :: 0 <= i < |s.validators| 
                && s.validators[i].activation_epoch 
                    <= get_current_epoch(s) 
                    < s.validators[i].exitEpoch
    }

    /**
     *  Check if an attestation is well formed.
     *
     *  @param      s       A beacon state.
     *  @param      a       An attestation.
     *  @returns            True if ``a`` satisfied the well formed criteria.
     *  @note       This predicate is not specified in the spec but acts as a helper
     *              to other components where an attestation must be well formed.
     */
    predicate attestationIsWellFormed(s: BeaconState, a: Attestation)
    {
        (get_previous_epoch(s) <= a.data.target.epoch <= get_current_epoch(s))  
        /** Epoch of target matches epoch of the slot the attestation is made. */
        && (a.data.target.epoch == compute_epoch_at_slot(a.data.slot))
        /** Attestation is not too old and not too recent. */
        && (a.data.slot as nat + MIN_ATTESTATION_INCLUSION_DELAY as nat 
            <= s.slot as nat 
            <= a.data.slot as nat + SLOTS_PER_EPOCH as nat)
        
        && (a.data.index < get_committee_count_per_slot(s, a.data.target.epoch))
        // Preconditions for get_beacon_committee
        && (TWO_UP_5 as nat 
            <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| 
            <= TWO_UP_11 as nat * TWO_UP_11 as nat )
        && (a.data.index < TWO_UP_6) 
        // this comes from the assert on attestations in process_attestations
        // same as above
        //&& a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) 
        // at most 64 committees per slot 
    
        && (|a.aggregation_bits| == |get_beacon_committee(s, a.data.slot, a.data.index)|)
        
        && (if a.data.target.epoch == get_current_epoch(s) then  
            a.data.source == s.current_justified_checkpoint
           else 
            a.data.source == s.previous_justified_checkpoint)
    }

    // Helper lemmas

    /**
     *  A proof that if the same validator indices in sv1 and sv2 are active validators
     *  then sv1 and sv2 will the same result from get_active_validator_indices.
     *
     *  @param  s                       A beacon state. 
     *  @param  slashed_index           A validator index.
     *  @param  whistleblower_index     A validator index.
     *  @return     A proof that get_active_validator_indices(sv1, epoch) 
     *                 == get_active_validator_indices(sv2, epoch).
     */
    lemma sameActiveValidatorsImpliesSameActiveIndices(sv1: ListOfValidators, 
                                                       sv2: ListOfValidators, 
                                                       epoch: Epoch)
        requires |sv1| == |sv2|   
        requires forall i :: (0 <= i < |sv1|) 
                    ==> is_active_validator(sv1[i], epoch) 
                        == is_active_validator(sv2[i], epoch)
        ensures get_active_validator_indices(sv1, epoch) 
                == get_active_validator_indices(sv2, epoch)
    {
        if |sv1| == 0 {
            assert get_active_validator_indices(sv2, epoch) 
                == get_active_validator_indices(sv1, epoch);
        }
        else {
            sameActiveValidatorsImpliesSameActiveIndices(sv1[..|sv1|-1], 
                                                         sv2[..|sv2|-1], 
                                                        epoch
                                                        );
        }
    }

    /**
     *  A proof that slashing a validator preserves the active status of all validators.
     *
     *  @param  s                       A beacon state. 
     *  @param  slashed_index           A validator index.
     *  @param  whistleblower_index     A validator index.
     *  @return     A proof that slashing a validator preserves the active status of 
     *              all validators.
     */
    lemma slashValidatorPreservesActiveValidators(s: BeaconState, 
                                                  slashed_index: ValidatorIndex, 
                                                  whistleblower_index: ValidatorIndex
                                                 )
        requires slashed_index as int < |s.validators| 
        requires whistleblower_index as int < |s.validators| 
        requires |s.validators| == |s.balances|
        requires minimumActiveValidators(s)
        
        ensures get_active_validator_indices(s.validators, get_current_epoch(s)) ==
                get_active_validator_indices(slash_validator(s,
                                                             slashed_index,
                                                             whistleblower_index).validators, 
                                             get_current_epoch(s)
                                            )
    {
        var epoch : Epoch := get_current_epoch(s);
        var proposer_index := get_beacon_proposer_index(s);
        var s' := initiate_validator_exit(s, slashed_index); 
        // only validator exitEpoch & withdrawable_epoch fields possibly changed

        // show initiate validator exit doesn't change the set of active validator indices
        assert |s.balances| == |s'.balances|;
        assert |s'.balances| == |s'.validators|;
        assert epoch == get_current_epoch(s');
        assert |get_active_validator_indices(s.validators, get_current_epoch(s))| > 0;
        
        assert forall i :: (0 <= i < |s.validators|) && (i != slashed_index as int)
                ==> initiate_validator_exit(s,slashed_index).validators[i].exitEpoch 
                    == s.validators[i].exitEpoch;
        
        assert forall i :: (0 <= i < |s.validators|) && (i != slashed_index as int)
                 ==> s'.validators[i].exitEpoch == s.validators[i].exitEpoch;
        
        assert forall i :: (0 <= i < |s'.validators|)
                ==> is_active_validator(s.validators[i], epoch) 
                    == is_active_validator(s'.validators[i], epoch);

        //initiateValidatorExitPreservesActiveValidators(s.validators, s'.validators, epoch);
        sameActiveValidatorsImpliesSameActiveIndices(s.validators, s'.validators, epoch);
        assert get_active_validator_indices(s'.validators, epoch) 
                == get_active_validator_indices(s.validators, epoch);
        assert |get_active_validator_indices(s'.validators, epoch)| > 0;

        s' := slash_validator(s,slashed_index,whistleblower_index);
        assert forall i :: (0 <= i < |s.validators|) && (i != slashed_index as int) 
                ==> s'.validators[i].exitEpoch == s.validators[i].exitEpoch;

        assert forall i :: (0 <= i < |s'.validators|) 
                ==> is_active_validator(s.validators[i], epoch) 
                    == is_active_validator(s'.validators[i], epoch);

        sameActiveValidatorsImpliesSameActiveIndices(s.validators, s'.validators, epoch);
        assert get_active_validator_indices(s'.validators, epoch)
                == get_active_validator_indices(s.validators, epoch);
    }
    
    /**
     *  A proof that the total balances of increase_balance(s,index,delta).balances is 
     *  equivalent to total_balances(s.balances) + delta.
     *
     *  @param  s       A beacon state. 
     *  @param  index   A validator index.
     *  @param  delta   A validator index.
     *  @return     A proof that total_balances(increase_balance(s,index,delta).balances) 
     *              == total_balances(s.balances) + delta as int.
     */
    lemma updateExistingBalance(s: BeaconState, index: ValidatorIndex, delta: Gwei)
        requires index as int < |s.balances| 
        requires s.balances[index] as int + delta as int < 0x10000000000000000
        requires |s.balances| < VALIDATOR_REGISTRY_LIMIT as int

        ensures total_balances(increase_balance(s,index,delta).balances) 
                == total_balances(s.balances) + delta as int
    {
        if index as int < |s.balances|-1 {
            assert increase_balance(s,index,delta).balances 
                    == increase_balance(s,index,delta).balances[..index] 
                        + [increase_balance(s,index,delta).balances[index]] 
                        + increase_balance(s,index,delta).balances[(index+1)..];
                                                                
            distBalancesProp(increase_balance(s,index,delta).balances[..index], 
                            [increase_balance(s,index,delta).balances[index]]
                            );
            distBalancesProp(increase_balance(s,index,delta).balances[..index]
                                +[increase_balance(s,index,delta).balances[index]], 
                            increase_balance(s,index,delta).balances[(index+1)..]
                            );
            assert s.balances 
                    == s.balances[..index] 
                        + [s.balances[index]] 
                        + s.balances[(index+1)..];
            
            distBalancesProp(s.balances[..index], [s.balances[index]]);
            distBalancesProp(s.balances[..index]+[s.balances[index]], 
                             s.balances[(index+1)..]
                             );
        }
        else {
            assert increase_balance(s,index,delta).balances 
                    == increase_balance(s,index,delta).balances[..index] 
                        + [increase_balance(s,index,delta).balances[index]];
            distBalancesProp(increase_balance(s,index,delta).balances[..index], 
                            [increase_balance(s,index,delta).balances[index]]
                            );
            assert s.balances == s.balances[..index] + [s.balances[index]] ;
            distBalancesProp(s.balances[..index], [s.balances[index]]);
        }
    }

    /**
     *  A proof that if attestationIsWellFormed(s, a) and state ``s1`` has the same
     *  validators, slot, current_justified_checkpoint and previous_justified_checkpoint
     *  then a is also well formed for state ``s1``.
     *
     *  @param  s       A beacon state. 
     *  @param  s1      A beacon state.
     *  @param  a       An attestation.
     *  @return     A proof that attestationIsWellFormed(s1, a).
     */
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
     *  A proof that if attestationIsWellFormed(s, a) then is_valid_number_active_validators,
     *  is_valid_committee_index and is_valid_beacon_committee_length.
     *
     *  @param  s       A beacon state. 
     *  @param  a       An attestation.
     *  @return         A proof that is_valid_number_active_validators,
     *                  is_valid_committee_index and is_valid_beacon_committee_length.
     */
    lemma AttestationHelperLemma2(s: BeaconState, a: Attestation)
        requires attestationIsWellFormed(s,a)
        ensures is_valid_number_active_validators(|get_active_validator_indices(s.validators, 
                                                                                compute_epoch_at_slot(a.data.slot))|
                                                 )
        ensures is_valid_committee_index(a.data.index, 
                                         get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot))
                                         )
        ensures is_valid_beacon_committee_length(|get_beacon_committee(s, a.data.slot, a.data.index)|, 
                                                 |a.aggregation_bits|
                                                )
    { // Thanks Dafny
    } 

    /**
     *  A proof that a state maintains the status of is_valid_state_epoch_attestations.
     *
     *  @param  s   A beacon state. 
     *  @return     A proof that is_valid_state_epoch_attestations(s) is true.
     *
     *  @note       This proof is assumed. A strategy to remove the use of this axiom
     *              could be to examine more carefully the state fields use to determine
     *              is_valid_state_epoch_attestations so as to better assess whether
     *              the is_valid_state_epoch_attestations property holds after a state is
     *              updated.
     *  @note       This axiom is used in updateEffectiveBalanceHelper.
     */
    lemma {:axiom } AssumeIsValidStateEpoch_Attestations(s: BeaconState)
        ensures is_valid_state_epoch_attestations(s)
    // {}

    /**
     *  A proof that a state maintains at least one active validator.
     *
     *  @param  s   A beacon state. 
     *  @return     A proof that is_valid_state_epoch_attestations(s) is true.
     *
     *  @note       This proof is assumed. A strategy to remove the use of this axiom
     *              could be to examine more carefully the state fields use to determine
     *              is_valid_state_epoch_attestations so as to better assess whether
     *              the is_valid_state_epoch_attestations property holds after a state is
     *              updated.
     *  @note       This axiom is used in updateEffectiveBalanceHelper.
     */
    lemma {:axiom } AssumeMinimumActiveValidators(s: BeaconState)
        ensures minimumActiveValidators(s)
    // {}


}