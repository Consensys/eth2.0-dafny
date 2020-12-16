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

include "../../utils/Eth2Types.dfy"
include "../../utils/SetHelpers.dfy"
include "../../ssz/Constants.dfy"
include "../forkchoice/ForkChoiceTypes.dfy"
include "../forkchoice/ForkChoiceHelpers.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../Helpers.dfy"
include "../BeaconChainTypes.dfy"
include "../statetransition/EpochProcessing.s.dfy"

/**
 *  Helpers for Epoch processing.
 */
module EpochProcessingHelpers {
    
    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened Constants
    import opened ForkChoiceTypes
    import opened ForkChoiceHelpers
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened BeaconHelpers
    import opened BeaconChainTypes
    import opened EpochProcessingSpec

    /**
     *  RuleI for slashing. 
     *  A validator cannot vote more than once for a given epoch.
     */
    // predicate ruleI(xa : seq<PendingAttestation>) 
    // {
    //     forall a1, a2 :: a1 in xa && a2 in xa ==>

    // }

    /**
     *  The last justified checkpoint in view(s).
     *  @param  s       A state
     *  @param  store   A store.
     *  @returns        The most recent justified checkpoint in view(s).
     */

    function lastJustifiedCheckPoint(s: BeaconState, store: Store) : CheckPoint 
        requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
        requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
        requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

    {
        var r := get_block_root(s, get_current_epoch(s));
        var roots := chainRoots(r, store); 
        //  |ebbsIndices| ==  get_current_epoch(s) + 1
        var ebbsIndices := computeAllEBBsIndices(roots, get_current_epoch(s), store);
        var lastJustified := lastJustified(roots, ebbsIndices, store.attestations);
        CheckPoint((|ebbsIndices| - 1 - lastJustified) as Epoch, roots[ebbsIndices[lastJustified]])
    }

    /**
     */
    function computeCheckPoints(s: BeaconState, store: Store) : seq<CheckPoint> 
        requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
        requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
        requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

        ensures |computeCheckPoints(s, store)| == get_current_epoch(s) as nat + 1
        ensures var r := get_block_root(s, get_current_epoch(s));
                var roots := chainRoots(r, store); 
                var ebbsIndices := computeAllEBBsIndices(roots, get_current_epoch(s), store);
                forall i :: 0 <= i <  |computeCheckPoints(s, store)| ==> 
                    computeCheckPoints(s, store)[i] == 
                        CheckPoint(get_current_epoch(s) - i as Epoch, roots[ebbsIndices[i]])              

        // ensures |computeCheckPoints(s, store| == get_current_epoch(s) as nat + 1
    // {
        // var r := get_block_root(s, get_current_epoch(s));
        // var roots := chainRoots(r, store); 
        // var ebbsIndices := computeAllEBBsIndices(roots, get_current_epoch(s), store);
        // // assert(|ebbsIndices| ==  get_current_epoch(s) + 1);
        // // var r : seq<CheckPoint> := 
        // var r : seq<nat> :| forall i :: 0 <= i < 10 ==> r[i] == i;
        // r 
    // }

    /**
     *  Whether a checkpoint is justified in the view that corresponds to a state.
     */
    predicate isJustifiedCheckPoint(cp : CheckPoint, s: BeaconState, store: Store) 
        requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
        requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
        requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)
    {
        var r := get_block_root(s, get_current_epoch(s));
        var roots := chainRoots(r, store); 
        var ebbsIndices := computeAllEBBsIndices(roots, get_current_epoch(s), store);
        exists i :: 0 <= i < |ebbsIndices| && isJustified(i, roots, ebbsIndices, store.attestations)
            && cp == CheckPoint((|ebbsIndices| - i) as Epoch, roots[ebbsIndices[i]])
    }

    /**
     *  If a checkpoint is justified and there is a supermajority link from it to 
     *  a more recent one, the more recent one is justified too.
     */
    lemma addJustified(cp1 : CheckPoint, cp2: CheckPoint, s: BeaconState, store: Store, links: seq<PendingAttestation>) 
        requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
        requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
        requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

        requires isJustifiedCheckPoint(cp1, s, store)
        //  cp2 is a checkpoint in view(s)
        // requires exists 
        requires |collectAttestationsForLink(
                    links, 
                    cp1, 
                    cp2)| 
                        >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
        // requires  
    {

    }


    /**
     *  Whether a checkpoint is the most recent justified in the view from s.
     */
    predicate isMostRecentJustifiedCheckPoint(cp : CheckPoint, s: BeaconState, store: Store) 
        requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
        requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
        requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

    {
        var r := get_block_root(s, get_current_epoch(s));
        var roots := chainRoots(r, store); 
        var ebbsIndices := computeAllEBBsIndices(roots, get_current_epoch(s), store);
        // exists i :: 0 <= i < |ebbsIndices| && isJustified(i, roots, ebbsIndices, store.
        var lastJustified := lastJustified(roots, ebbsIndices, store.attestations);
        cp == CheckPoint((|ebbsIndices| - lastJustified) as Epoch, roots[ebbsIndices[lastJustified]])
    }

    
  
}