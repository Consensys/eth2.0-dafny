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
include "../utils/NativeTypes.dfy"
include "../utils/SetHelpers.dfy"
include "../ssz/Constants.dfy"

include "BeaconChainTypes.dfy"
include "validators/Validators.dfy"

/**
 *  Beacon chain helper functional specifications.
 */
module BeaconHelperSpec {

    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened NativeTypes
    import opened SetHelpers
    import opened Constants

    import opened BeaconChainTypes
    import opened Validators
    import opened AttestationsTypes
    
    // Predicates
    /**
     *  Check whether a set of validator indices are valid
     *  i.e. within range such that index < |s.validators|.
     *
     *  @param      s       A beacon state.
     *  @param      indices A sequence of validator indices as uint64.
     *  @returns            True if all indices < |s.validators|.
     */
    predicate valid_state_indices(s: BeaconState, indices: seq<uint64>)
    {
        forall i :: 0 <= i < |indices| ==> indices[i] as int < |s.validators|
    }


    // Functions

    /**
     *  Collect pubkey in a list of validators.
     *
     *  @param      xv  A list of validators,
     *  @returns        The set of keys helpd byt the validators in `xv`.
     */
    function keysInValidators(xv : seq<Validator>) : set<BLSPubkey>
        decreases xv
    {
        if |xv| == 0 then  
            {}
        else 
            { xv[0].pubkey } + keysInValidators(xv[1..])
    }

    /**
     *  Extract the list of validators from a sequence of proposer slashings.
     *
     *  @param      ps  A list of proposer slashings.
     *  @returns        The sequence of validator indices for ps as ints.
     *
     *  @note           Return index type could be changed to uint64.
     */
    function get_PS_validator_indices(ps: seq<ProposerSlashing>): seq<int>
        ensures |get_PS_validator_indices(ps)| == |ps|
    {
        if |ps| == 0 then []
        else [ps[0].header_1.proposer_index as int] + get_PS_validator_indices(ps[1..])
    }

    /**
     *  Extract the list of validators from a sequence of voluntary exits.
     *
     *  @param      ve  A list of voluntary exits.
     *  @returns        The sequence of validator indices for ve as ints.
     *
     *  @note           Return index type could be changed to uint64 but int
     *                  was used here for convenience.
     */
    function get_VolExit_validator_indices(ve: seq<VoluntaryExit>): seq<int>
        ensures |get_VolExit_validator_indices(ve)| == |ve|
    {
        if |ve| == 0 then []
        else [ve[0].validator_index as int] + get_VolExit_validator_indices(ve[1..])
    }

    /**
     *  Sorted intersection of two sets of sorted validator indices.
     *
     *  @param      a   A sorted list of validators.
     *  @param      b   A sorted list of validators.
     *  @returns        The sorted intersection of a and b.
     */
    function sorted_intersection_fn(a : seq<ValidatorIndex>, b: seq<ValidatorIndex>): seq<uint64>
        requires forall i,j :: 0 <= i < j < |a| ==> a[i] < a[j]
        requires forall i,j :: 0 <= i < j < |b| ==> b[i] < b[j]
        ensures forall i,j :: 0 <= i < j < |sorted_intersection_fn(a,b)| 
                ==> sorted_intersection_fn(a,b)[i] < sorted_intersection_fn(a,b)[j]
        ensures forall i :: 0 <= i < |sorted_intersection_fn(a,b)| 
                ==> sorted_intersection_fn(a,b)[i] as ValidatorIndex in a 
                    && sorted_intersection_fn(a,b)[i] as ValidatorIndex in b
    {
        if |a| == 0 then []
        else (if a[0] in b then [a[0] as uint64] else []) + sorted_intersection_fn(a[1..], b)
    }

    /**
     *  Get the total of a sequence of deposits as a nat.
     *
     *  @param      deposits    A sequence of deposits.
     *  @returns                The total of all deposit amounts as a nat.
     */
    function total_deposits(deposits: seq<Deposit>): nat
    {
        if |deposits| == 0 then 0
        else total_deposits(deposits[..|deposits|-1]) + deposits[|deposits|-1].data.amount as nat
    }

    /**
     *  Get the total of a sequence of balances as a nat.
     *
     *  @param      bal     A sequence of balance amounts.
     *  @returns            The total of all balances as a nat.
     */
    function total_balances(bal: seq<Gwei>): nat
    {
        if |bal| == 0 then 0
        else bal[0] as nat + total_balances(bal[1..])
    }

    /**
     *  Collect set of indices of validators attesting a link.
     *
     *  @param  xa      A seq of attestations.
     *  @param  src     The source checkpoint of the link.
     *  @param  tgt     The target checkpoint of the link.
     *  @returns        The set of validators's indices that vote for (src. tgt) in `xa`. 
     */
     function collectValidatorsAttestatingForLink(xa : seq<PendingAttestation>, src : CheckPoint, tgt: CheckPoint) : set<nat>
        ensures forall e :: e in collectValidatorsAttestatingForLink(xa, src, tgt) ==>
            e < MAX_VALIDATORS_PER_COMMITTEE as nat
        ensures |collectValidatorsAttestatingForLink(xa, src, tgt)| <= MAX_VALIDATORS_PER_COMMITTEE as nat
        decreases xa
    {
        if |xa| == 0 then 
            { }
        else 
            unionCardBound(trueBitsCount(xa[0].aggregation_bits),
                collectValidatorsAttestatingForLink(xa[1..], src, tgt), MAX_VALIDATORS_PER_COMMITTEE as nat);
            (if xa[0].data.source == src && xa[0].data.target == tgt then 
                trueBitsCount(xa[0].aggregation_bits)
            else 
                {}
            ) + collectValidatorsAttestatingForLink(xa[1..], src, tgt)
    }

    /**
     *  Collect set of indices of validators attesting a link to a given target.
     *
     *  @param  xa      A seq of attestations.
     *  @param  tgt     The target checkpoint of the link.
     *  @returns        The set of validators's indices that vote for (_. tgt) in `xa`. 
     */
    function collectValidatorsIndicesAttestatingForTarget(xa : seq<PendingAttestation>, tgt: CheckPoint) : set<nat>
        ensures forall e :: e in collectValidatorsIndicesAttestatingForTarget(xa, tgt) ==>
            e < MAX_VALIDATORS_PER_COMMITTEE as nat
        ensures |collectValidatorsIndicesAttestatingForTarget(xa, tgt)| <= MAX_VALIDATORS_PER_COMMITTEE as nat
        decreases xa
    {
        if |xa| == 0 then 
            { }
        else 
            unionCardBound(trueBitsCount(xa[0].aggregation_bits),
                collectValidatorsIndicesAttestatingForTarget(xa[1..], tgt), MAX_VALIDATORS_PER_COMMITTEE as nat);
            (if xa[0].data.target == tgt then 
                trueBitsCount(xa[0].aggregation_bits)
            else 
                {}
            ) + collectValidatorsIndicesAttestatingForTarget(xa[1..], tgt)
    }

    /**
     *  Collect the set of indices for which xb[i] is true.
     *  
     *  @param  xb  A sequence of bools.
     *  @returns    The number of elements that are true in `xb`.
     */
    function trueBitsCount(xb : seq<bool>) : set<nat> 
        ensures |trueBitsCount(xb)| <= |xb|
        ensures forall i :: i in trueBitsCount(xb) <==> 0 <= i < |xb| && xb[i]
        decreases xb
    {
        if |xb| == 0 then 
            {}
        else 
            (if xb[|xb| - 1] then { |xb| - 1 } else {}) + trueBitsCount(xb[..|xb| - 1])
    }

    /**
     *  Check if ``indices``, ``seed``, ``index``, and ``count`` are valid inputs
     *  to compute_committee.
     *
     *  @param      indices     A sequence of active validator indices.
     *  @param      seed        A seed value.
     *  @param      index       (slot % SLOTS_PER_EPOCH) * committees_per_slot + CommitteeIndex
     *  @param      count       committees_per_slot * SLOTS_PER_EPOCH
     *  @returns                True if the inputs satisfy the requirements of
     *                          compute_committee.
     */
    predicate is_valid_compute_committee_parameters(indices: seq<ValidatorIndex>, 
                                                    seed: Bytes32, 
                                                    index: uint64, 
                                                    count: uint64
                                                   ) 
    {
        count > 0
        && index < count
        && (0 < |indices| < 0x10000000000000000)
        && (|indices|  * index as nat / count as nat  < 0x10000000000000000)
        && (|indices| * (index as nat +1) / count as nat < 0x10000000000000000)
        && (|indices| * (index as nat +1) / count as nat <= |indices| )
        && (|indices| * (index as nat +1) / count as nat > |indices| * index as nat / count as nat)
        && (0 
            < (|indices| * (index as nat + 1)) / (count as nat) 
                - (|indices| * index as nat ) / count as nat 
            <= MAX_VALIDATORS_PER_COMMITTEE as nat)
    }

    /**
     *  Check if ``n``is a valid number of active validators.
     *
     *  @param  n   A positive integer.   
     *  @returns    True if 32 <= n <= 2^22
     */
    predicate is_valid_number_active_validators(n: nat) 
    {
        TWO_UP_5 as nat <= n <= TWO_UP_11 as nat * TWO_UP_11 as nat 
    }

    /**
     *  Check if ``i`` is a valid committee index.
     *
     *  @param  i       A positive integer.   
     *  @param  ccps    The committee count per slot.   
     *  @returns        True if i < ccps <= 64
     */
    predicate is_valid_committee_index(i: CommitteeIndex, ccps: uint64) 
    {
        i as nat < ccps as nat <= TWO_UP_6 as nat
    }

    /**
     *  Check if ``i`` is a valid gwei  amount.
     *
     *  @param  i       A positive integer.   
     *  @returns        True if i < 0x10000000000000000
     */
    predicate is_valid_gwei_amount(i: nat)
    {
        i < 0x10000000000000000
    }

    /**
     *  Check if ``len_bc``is a valid beacon committee length given ``len_bits``.
     *
     *  @param      len_bc      A positive integer.
     *  @param      len_bits    A positive integer.
     *  @returns                True if len_bc < len_bits <=
     *                          len_bc < len_bits <= MAX_VALIDATORS_PER_COMMITTEE.
     */
    predicate is_valid_beacon_committee_length(len_bc: nat, len_bits: nat)
    {
        (0 < len_bc <= len_bits <= MAX_VALIDATORS_PER_COMMITTEE as nat)
    }


    predicate is_valid_withdrawal_amount(withdrawal_amount: nat)
    {
        withdrawal_amount < 0x10000000000000000
    }


}