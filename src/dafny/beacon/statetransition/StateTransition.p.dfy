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

include "../Helpers.dfy"
include "../Helpers.s.dfy"
include "../BeaconChainTypes.dfy"
include "../../ssz/Constants.dfy"

/**
 *  Beacon chain helper functional specifications.
 */
module StateTransitionProofs {

    //  Import some beacon chain helpers and types.  
    import opened BeaconHelpers
    import opened BeaconHelperSpec
    import opened BeaconChainTypes
    import opened Constants
    

    // Proofs related to state transition.

    /**
     *  This lemma establishes that the minimum number of active validators is 1.
     *
     *  @param  s   A beacon state. 
     *  @return     The proof is currently assumed.
     *
     *  @notes      It is assumed that there will always be at least one active validator.
     *              An alternative to this assumption lemma would be to add preconditions to assert 
     *              that the number of active validators cannot drop to zero.
     */
    lemma SetMinimumNumberOfValidators(s: BeaconState)
        ensures minimumActiveValidators(s)
    // {}

    /**
     *  This lemma establishes that all previous_epoch_attestations meet processing requirements.
     *
     *  @param  s   A beacon state. 
     *  @return     The proof is currently assumed.
     *
     *  @notes      It is assumed that all previous epoch attestations, and in fact all current epoch attestations,
     *              meet these requirements. 
     *              These properties could be confirmed as part of process_attestation.
     */
    lemma PreviousEpochAttestationsProperties(s: BeaconState)
        requires |s.validators| == |s.balances|
        ensures forall a :: a in s.previous_epoch_attestations ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6 
        ensures forall a :: a in s.previous_epoch_attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        ensures forall a :: a in s.previous_epoch_attestations ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    // {} 

}