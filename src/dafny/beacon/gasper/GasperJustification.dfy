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

include "../../ssz/Constants.dfy"
include "../../utils/Eth2Types.dfy"
include "../../utils/NativeTypes.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../BeaconChainTypes.dfy"
include "../Helpers.dfy"
include "../forkchoice/ForkChoiceTypes.dfy"
include "./GasperEBBs.dfy"
  
/**
 *  Provide definitions of chain, well-formed store, EBB, justified.
 */
module GasperJustification {
    
    import opened Constants
    import opened Eth2Types
    import opened NativeTypes
    import opened BeaconChainTypes
    import opened BeaconHelpers
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened ForkChoiceTypes
    import opened GasperEBBs
   
    //  Justification definitions.

    /**
     *  Whether a checkpoint at a given epoch is justified or not.
     *
     *  @param  ebbs    A sequence of block roots. Should be the checkpoints (EBBs)
     *                  at each epoch |ebbs| - 1,  ... |ebbs| - 1 - k, ... 0.
     *                  (ebbs[|ebbs| - 1 - k], k) is the EBB at epoch k.
     *  @param  e       An epoch <= |ebbs| - 1.
     *  @param  store   A store.
     *
     *  @returns        Whether the EBB at epoch e is justified according to the votes in *                  `links`.         
     *  @note           ebbs should be such that ebbs[|ebbs| - 1] has slot 0. 
     *
     *  epoch       0                    e                              |ebbs| - 1
     *              |............   .... |....    .....|...................|..........
     *  ChkPt  ebbs[|ebbs| - 1] ... (ebbs[|ebbs| - 1 - e], e) ....    ebbs[0]
     *  
     */
    predicate isJustifiedEpoch(ebbs: seq<Root>, e: Epoch, store: Store)
        /** e is an epoch in ebbs, and each index represent an epoch so must be uint64. */
        requires e as nat <= |ebbs| - 1 <= MAX_UINT64

        /** The block roots are in the store. */
        requires forall k:: 0 <= k < |ebbs| ==> ebbs[k] in store.blocks.Keys 

        decreases e
    {
        if e as nat == 0 then 
            //  Last block in the list is justified if it is genesis (i.e. slot == 0).
            //  This is the sole purpose of the `store` paramneter. 
            //  root at index |ebbs| - 1 - 0 is the EBB at epoch 0. 
            store.blocks[ebbs[|ebbs| - 1]].slot == 0 
        else 
            //  There should be a justified block at a previous epoch j
            //  that is justified and a supermajority link from `j` to `e`.
            exists j: Epoch :: 
                j < e  
                && isJustifiedEpoch(ebbs, j, store) 
                && |collectValidatorsAttestatingForLink(
                    store.rcvdAttestations, 
                    CheckPoint(j as Epoch, ebbs[|ebbs| - 1 - j as nat]), 
                    CheckPoint(e as Epoch, ebbs[|ebbs| - 1 - e as nat]))| 
                        >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
    }
 
    /**
     *  @param  br      A block root.
     *  @param  e       An epoch.
     *  @param  store   A store.
     *  @param  links   A list of attestations.
     *
     *  @returns        Whether the EBB at epoch e is justified according to the votes in *                  `links`.         
     *  @note           ebbs should be such that ebbs[|ebbs| - 1] has slot 0. 
     *
     *  
     *
     *  epoch       0                    e                              |ebbs| - 1
     *              |............   .... |....    .....|...................|..........
     *  ChkPt  ebbs[|ebbs| - 1] ... (ebbs[|ebbs| - 1 - e], e) ....    ebbs[0]
     *  
     */
    predicate isJustifiedEpochFromRoot(br: Root, e: Epoch, store: Store) 
        requires br in store.blocks.Keys 
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  
    {
        //  Compute the EBBs from `br` before epoch e 
        var cr := computeAllEBBsFromRoot(br, e, store);
        //  There are e + 1 EBBs in cr indexed from 0 to |e|
        //  cr[0] is the EBB at epoch e, cr[k] at epoch e - k, cr[|cr| - 1 == e] 
        //  at epoch e - |cr| + 1 == 0
        assert(|cr| == e as nat + 1);
        //  Return whether epoch e is justified in `cr`
        isJustifiedEpoch(cr, e, store)
    }

    predicate isJustified(cp: CheckPoint, store: Store)
        /** The block root must in the store.  */
        requires cp.root in store.blocks.Keys         
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        decreases cp.epoch 
    {
        if cp.epoch == 0 then // should be a the genesis block
            store.blocks[cp.root].slot == 0 
        else 
            exists cp2 : CheckPoint ::
                cp2.epoch < cp.epoch 
                && cp2.root in chainRoots(cp.root, store)
                && isJustified(cp2, store)
                && |collectValidatorsAttestatingForLink(store.rcvdAttestations, cp2, cp)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1   
    }


    lemma justifiedMustHaveTwoThirdIncoming2(cp: CheckPoint, store: Store)
        /** The block root must in the store.  */
        requires cp.root in store.blocks.Keys         
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        /** Checkpoint at epoch e is justified. */
        requires cp.epoch > 0 && isJustified(cp, store)
        /** Checkpoint at epoch e has more than 2/3 incoming votes. */
        ensures 
            //  The total number of attestations to EBB at epoch e is a supermajority.
            |collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp)| 
                >= ( 2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
    {
        var cpsrc : CheckPoint :| cpsrc.epoch < cp.epoch && cpsrc.root in chainRoots(cp.root, store)
            && |collectValidatorsAttestatingForLink(store.rcvdAttestations, cpsrc, cp)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;
        attForTgtLargerThanLinks(store.rcvdAttestations, cpsrc, cp);
    }

    /**
     *  The most recent justified EBB before epoch.
     */
    function lastJustified(br: Root, e: Epoch, store: Store): (c :  CheckPoint)
        /** The block root must in the store.  */
        requires br in store.blocks.Keys
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)        
        
        ensures 0 <= c.epoch <= e 
        ensures 
            var cr := computeAllEBBsFromRoot(br, e, store);
            isJustifiedEpochFromRoot(br, c.epoch, store) &&
            c.root == cr[e - c.epoch]
            && forall k :: c.epoch < k <= e ==> !isJustifiedEpochFromRoot(br, k, store)
}
