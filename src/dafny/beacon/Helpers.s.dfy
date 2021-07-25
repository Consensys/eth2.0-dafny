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

include "../utils/Eth2Types.dfy"
include "../utils/MathHelpers.dfy"
include "../utils/NativeTypes.dfy"

include "../ssz/Constants.dfy"

include "BeaconChainTypes.dfy"
include "Helpers.dfy"
include "validators/Validators.dfy"

/**
 *  Beacon chain helper functional specifications.
 */
module BeaconHelperSpec {

    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened MathHelpers
    import opened NativeTypes

    import opened Constants

    import opened BeaconChainTypes
    import opened BeaconHelpers
    import opened Validators


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

    function get_VolExit_validator_indices(ve: seq<VoluntaryExit>): seq<int>
        ensures |get_VolExit_validator_indices(ve)| == |ve|
    {
        if |ve| == 0 then []
        else [ve[0].validator_index as int] + get_VolExit_validator_indices(ve[1..])
    }

    function get_PS_validator_indices(ps: seq<ProposerSlashing>): seq<int>
        ensures |get_PS_validator_indices(ps)| == |ps|
    {
        if |ps| == 0 then []
        else [ps[0].header_1.proposer_index as int] + get_PS_validator_indices(ps[1..])
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

    predicate valid_state_indices(s: BeaconState, indices: seq<uint64>)
    {
        forall i :: 0 <= i < |indices| ==> indices[i] as int < |s.validators|
    }
    

}