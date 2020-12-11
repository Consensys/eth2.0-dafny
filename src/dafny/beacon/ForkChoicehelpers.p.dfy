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

include "../ssz/Constants.dfy"
include "../utils/Eth2Types.dfy"
include "attestations/AttestationsTypes.dfy"
include "attestations/AttestationsHelpers.dfy"
include "BeaconChainTypes.dfy"
include "Helpers.dfy"
include "ForkChoiceTypes.dfy"
include "ForkChoiceHelpers.dfy"

/**
 * Fork choice rule for the Beacon Chain.
 */
module ForkChoiceHelpersProofs {
    
    import opened Constants
    import opened Eth2Types
    import opened BeaconChainTypes
    import opened BeaconHelpers
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened ForkChoiceTypes
    import opened ForkChoiceHelpers

   
    /**
     *  A checkpoint (B, j > 0) that is justified must have more then 2/3 of
     *  ingoing votes.
     *
     *  @param  i       An index in `ebbs`.
     *  @param  xb      Sequence of blocks roots (last one expected to be genesis block root).
     *  @param  ebbs    A sequence of EBB from epoch |ebbs| - 1 to 0. Last element must
     *                  be pointing to last element of `xv`.
     *  @param  links   The votes (attestations).
     */
    lemma {:induction i} justifiedMustHaveTwoThirdIncoming(i: nat, xb : seq<Root>, ebbs: seq<nat>,  links : seq<PendingAttestation>)
        /** i is an index in ebbs not epoch 0. Each index represent an epoch so must be unint64. */
        requires i + 1 < |ebbs| 
        requires |ebbs| <= 0x10000000000000000
        /** `xb` has at least one block. */
        requires |xb| >= 1
        /** The last element of ebbs is the EBB at epoch 0 and should be the last block in `xb`. */
        requires ebbs[|ebbs| - 1] == |xb| - 1
        
        /** (xb[ebbs[j]], j) is the EBB at epoch |ebbs| - j and must be an index in `xb`.  */
        requires forall i :: 0 <= i < |ebbs| ==> ebbs[i] < |xb|
        ensures isJustified(i, xb, ebbs, links) ==>
            |collectAttestationsForTarget(links, CheckPoint(i as Epoch, xb[ebbs[i]]))| >= ( 2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
    {
        if isJustified(i, xb, ebbs, links) {
            assert(i < |ebbs| - 1);
            //  i is not last element of `xv` and cannot be epoch 0.
            assert( exists j :: i < j < |ebbs| - 1 && isJustified(j, xb, ebbs, links) 
                && |collectAttestationsForLink(links, CheckPoint(j as Epoch, xb[ebbs[j]]), CheckPoint(i as Epoch, xb[ebbs[i]]))| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);
            var j :|  i < j < |ebbs| - 1 && isJustified(j, xb, ebbs, links) && |collectAttestationsForLink(links, CheckPoint(j as Epoch, xb[ebbs[j]]), CheckPoint(i as Epoch, xb[ebbs[i]]))| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;
            assert(|collectAttestationsForLink(links, CheckPoint(j as Epoch, xb[ebbs[j]]), CheckPoint(i as Epoch, xb[ebbs[i]]))| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);
            attForTgtLargerThanLinks(links, CheckPoint(j as Epoch, xb[ebbs[j]]), CheckPoint(i as Epoch, xb[ebbs[i]]));
        }
    }

    /**
     *  The index of the first (left to right, 0 to |xb| - 1) justified ebb.
     */
    function lastJustified(xb : seq<Root>, ebbs: seq<nat>,  links : seq<PendingAttestation>): nat
        /** `xb` has at least one block. */
        requires |xb| >= 1
        requires 1 <= |ebbs| <= 0x10000000000000000
        /** The last element of ebbs is the EBB at epoch 0 and should be the last block in `xb`. */
        requires ebbs[|ebbs| - 1] == |xb| - 1
        /** (xb[ebbs[j]], j) is the EBB at epoch |ebbs| - j and must be an index in `xb`.  */
        requires forall i :: 0 <= i < |ebbs| ==> ebbs[i] < |xb|

        ensures lastJustified(xb, ebbs, links) < |ebbs|
        ensures isJustified(lastJustified(xb, ebbs, links), xb, ebbs, links)
        ensures forall i :: 0 <= i < lastJustified(xb, ebbs, links) ==> 
            !isJustified(i, xb, ebbs, links)
    //  R1: we can compute it, but this requires a lemma to shit a result on
    //  isJustified(i, ebbs[1..], ...) to isJustified(1 + i, ebbs)
    // {
    //     if isJustified(0, xb, ebbs, links) then 
    //         // assert(isJustified(0,  xb, ebbs, links));
    //         0
    //     else 
    //          // use of a lemma would be needed here, see R1 above.
    //         // assert(isJustified(1 + lastJustified(xb, ebbs[1..], links), xb, ebbs, links));
    //         1 + lastJustified(xb, ebbs[1..], links)
    // }

    /**
     *  
     *  @param  i       An index in the sequence of ebbs.
     *  @param  xb      A sequence of block roots.
     *  @param  ebbs    A sequence of indices. (xb[ebbs(j)],j) is EBB(xb, |ebbs| - 1 - j).
     *                  The last element (xb[ebbs[|ebbs| - 1]], |ebbs| - 1 - (|ebbs| - 1) )
     *                  i.e. (xb[|xb| - 1], 0) is assumed to be justified.
     *  @param  links   The attestations (votes).
     *  @returns        Whether (xb[ebbs[i]], i) is justified according to the votes in *                  `links`.         
     *  @note           ebbs contains EBB for epochs |ebbs| - 1 down to 0. 
     */
    predicate isJustified(i: nat, xb : seq<Root>, ebbs: seq<nat>,  links : seq<PendingAttestation>)
        /** i is an index in ebbs, and each index represent an epoch so must be unint64. */
        requires i < |ebbs| <= 0x10000000000000000
        /** `xb` has at least one block. */
        requires |xb| >= 1
        /** The last element of ebbs is the EBB at epoch 0 and should be the last block in `xb`. */
        requires ebbs[|ebbs| - 1] == |xb| - 1
        
        /** (xb[ebbs[j]], j) is the EBB at epoch |ebbs| - j and must be an index in `xb`.  */
        requires forall i :: 0 <= i < |ebbs| ==> ebbs[i] < |xb|

        decreases |ebbs| - i 
    {
        // true
        if i == |ebbs| - 1 then 
            // Last block in the list is assumed to be justified.
            true
        else 
            //  There should be a justified block at a higher index `j` that is justified
            //  and a supermajority link from `j` to `i`.
            exists j  :: i < j < |ebbs| - 1 && isJustified(j, xb, ebbs, links) 
                && |collectAttestationsForLink(
                    links, 
                    CheckPoint(j as Epoch, xb[ebbs[j]]), 
                    CheckPoint(i as Epoch, xb[ebbs[i]]))| 
                        >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
    }
}