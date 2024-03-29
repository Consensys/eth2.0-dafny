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


include "../utils/MathHelpers.dfy"
include "../ssz/Constants.dfy"
include "attestations/AttestationsTypes.dfy"

/**
 *  Proofs relating to the bounds on active validators required to form committees.
 */
module ActiveValidatorBounds {

    //  Import some constants, types and beacon chain helpers.
    import opened MathHelpers
    import opened Constants
    
    /**
     *  A proof that if len_indices > 2^22 then at least one committee formed will be of a length 
     *  that breaches the upper bound of MAX_VALIDATORS_PER_COMMITTEE.
     *
     *  @param  len_indices     A positive integer representing the number of active validators. 
     *  @param  CPS             A positive integer representing the number of committees per slot. 
     *  @return                 A proof that if len_indices > 2^22 then at least one committee formed 
     *                          will be of a length that breaches the upper bound of 
     *                          MAX_VALIDATORS_PER_COMMITTEE.
     */
    lemma proveAtLeastOneCommitteeFormedBreachsBound(len_indices: nat, CPS: nat)
        requires TWO_UP_11 as nat * TWO_UP_11 as nat < len_indices 
        requires CPS == max(1, 
                            min(MAX_COMMITTEES_PER_SLOT as nat, 
                                len_indices/ SLOTS_PER_EPOCH  as nat/ TARGET_COMMITTEE_SIZE as nat) as nat
                            )
        ensures 
            exists cIndex, slot  | 0 <= cIndex < CPS && 0 <= slot < SLOTS_PER_EPOCH as nat :: 
            ((len_indices * ((slot * CPS + cIndex) + 1) / (CPS * SLOTS_PER_EPOCH as nat)) 
            - (len_indices * (slot * CPS + cIndex)  / (CPS * SLOTS_PER_EPOCH as nat)) 
            > MAX_VALIDATORS_PER_COMMITTEE as nat)
    {
        assert CPS == 64;
        
        assert exists cIndex, slot  | 0 <= cIndex < CPS && 0 <= slot < SLOTS_PER_EPOCH as nat :: 
               ((len_indices * ((slot * CPS + cIndex) + 1) / (CPS * SLOTS_PER_EPOCH as nat)) 
               - (len_indices * (slot * CPS + cIndex)  / (CPS * SLOTS_PER_EPOCH as nat)) 
               > MAX_VALIDATORS_PER_COMMITTEE as nat)
               by
               {
                    assert 
                    (len_indices * ((31 * CPS + 63) + 1) / (CPS * SLOTS_PER_EPOCH as nat)) 
                    - (len_indices * (31 * CPS + 63)  / (CPS * SLOTS_PER_EPOCH as nat)) 
                    > MAX_VALIDATORS_PER_COMMITTEE as nat;
               }
    }

    /**
     *  A proof that if len_indices > 2^22 then at least one committee formed will be of a length 
     *  that breaches the upper bound of MAX_VALIDATORS_PER_COMMITTEE.
     *
     *  @param  len_indices     A positive integer representing the number of active validators. 
     *  @param  CPS             A positive integer representing the number of committees per slot. 
     *  @param  slot            A positive integer representing the slot. 
     *  @param  cIndex          A positive integer representing the committee index. 
     *  @return                 A proof that if len_indices >= ((2^22) + (2^11)) then all committees 
     *                          formed will be of a length that breaches the upper bound of 
     *                          MAX_VALIDATORS_PER_COMMITTEE.
     */
    lemma proveAllCommitteesFormedBreachBound(len_indices: nat, CPS: nat, slot: nat, cIndex: nat)
        requires TWO_UP_5 as nat <= len_indices 
        requires CPS == max(1, 
                            min(MAX_COMMITTEES_PER_SLOT as nat, 
                                len_indices/ SLOTS_PER_EPOCH  as nat/ TARGET_COMMITTEE_SIZE as nat) as nat
                            )
        requires 0 <= slot < SLOTS_PER_EPOCH as nat// i.e. slot % SPE
        requires 0 <= cIndex < CPS

        ensures var start :=  (len_indices * (slot * CPS + cIndex) ) / (CPS * SLOTS_PER_EPOCH as nat);
                var end := (len_indices * ((slot * CPS + cIndex) + 1)) / (CPS * SLOTS_PER_EPOCH as nat);
                len_indices >= ((TWO_UP_11 * TWO_UP_11) + TWO_UP_11) as nat 
                    ==> end - start > MAX_VALIDATORS_PER_COMMITTEE as nat
                // at this point all committees formed will breach the maximum size bound
    {
        var start :=  (len_indices * (slot * CPS + cIndex) ) / (CPS * SLOTS_PER_EPOCH as nat);
        var end := (len_indices * ((slot * CPS + cIndex) + 1)) / (CPS * SLOTS_PER_EPOCH as nat);

        assert len_indices >= ((TWO_UP_11 * TWO_UP_11) + TWO_UP_11) as nat 
            ==> end - start > MAX_VALIDATORS_PER_COMMITTEE as nat;
    }

    /**
     *  A proof that if 32 <= len_indices <= > 2^22 then all committees formed will be of 
     *  0 < length <= MAX_VALIDATORS_PER_COMMITTEE.i.e. a valid length
     *
     *  @param  len_indices     A positive integer representing the number of active validators. 
     *  @param  CPS             A positive integer representing the number of committees per slot. 
     *  @param  slot            A positive integer representing the slot. 
     *  @param  cIndex          A positive integer representing the committee index. 
     *  @return                 A proof that if 32 <= len_indices <= > 2^22 then all committees 
     *                          formed will be of a valid length.
     */
    lemma proveActiveValidatorsSatisfyBounds(len_indices: nat, CPS: nat, slot: nat, cIndex: nat)
        // The valid range required for the number of active validators
        requires TWO_UP_5 as nat <= len_indices <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires CPS == max(1, 
                            min(MAX_COMMITTEES_PER_SLOT as nat, 
                                len_indices/ SLOTS_PER_EPOCH  as nat/ TARGET_COMMITTEE_SIZE as nat) as nat
                            )
        requires 0 <= slot < SLOTS_PER_EPOCH as nat;
        requires 0 <= cIndex < CPS;

        ensures var start :=  (len_indices * (slot * CPS + cIndex) ) / (CPS * SLOTS_PER_EPOCH as nat);
                var end := (len_indices * ((slot * CPS + cIndex) + 1)) / (CPS * SLOTS_PER_EPOCH as nat);
    
                0 < end - start <= MAX_VALIDATORS_PER_COMMITTEE as nat
    {
        var start :=  (len_indices * (slot * CPS + cIndex) ) / (CPS * SLOTS_PER_EPOCH as nat);
        var end := (len_indices * ((slot * CPS + cIndex) + 1)) / (CPS * SLOTS_PER_EPOCH as nat);

        assert  TWO_UP_18 as nat <= len_indices ==> CPS == 64;
        assert TWO_UP_18 as nat <= len_indices <= TWO_UP_11 as nat * TWO_UP_11 as nat && CPS == 64 
                ==> 0 < end - start <= MAX_VALIDATORS_PER_COMMITTEE as nat;

        assert 63 * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat 
                    <= len_indices 
                    < TWO_UP_18 as nat && CPS == 63 
                ==> 0 < end - start <= MAX_VALIDATORS_PER_COMMITTEE as nat;

        assert forall i :: 2 <= i <= 63 
                && (i-1) * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat 
                    <= len_indices 
                    < i * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat 
                ==> CPS == i-1 ;
    
        assert forall i :: 2 <= i <= 63 
                && (i-1) * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat 
                    <= len_indices 
                    < i * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat && CPS == i-1 
                ==> 0 < end - start <= MAX_VALIDATORS_PER_COMMITTEE as nat;

        assert len_indices < 2 * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat 
                ==> CPS == 1;
        assert TWO_UP_5 as nat <= len_indices < 2 * SLOTS_PER_EPOCH as nat * TARGET_COMMITTEE_SIZE as nat 
                && CPS == 1 
                ==> 0 < end - start <= MAX_VALIDATORS_PER_COMMITTEE as nat;

        assert TWO_UP_5 as nat <= len_indices <= TWO_UP_11 as nat * TWO_UP_11 as nat 
                ==> 0 < end - start <= MAX_VALIDATORS_PER_COMMITTEE as nat;
    
    }

}