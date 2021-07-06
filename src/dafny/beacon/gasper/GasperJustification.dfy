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
     *  @param  links   A list of attestations.
     *
     *  @returns        Whether the EBB at epoch e is justified according to the votes in *                  `links`.         
     *  @note           ebbs should be such that ebbs[|ebbs| - 1] has slot 0. 
     *
     *  epoch       0                    e                              |ebbs| - 1
     *              |............   .... |....    .....|...................|..........
     *  ChkPt  ebbs[|ebbs| - 1] ... (ebbs[|ebbs| - 1 - e], e) ....    ebbs[0]
     *  
     */
    predicate isJustifiedEpoch(ebbs: seq<Root>, e: Epoch, store: Store, links : seq<PendingAttestation>)
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
                && isJustifiedEpoch(ebbs, j, store, links) 
                && |collectValidatorsAttestatingForLink(
                    links, 
                    CheckPoint(j as Epoch, ebbs[|ebbs| - 1 - j as nat]), 
                    CheckPoint(e as Epoch, ebbs[|ebbs| - 1 - e as nat]))| 
                        >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
    }

    /**
     *  Lift justification status to fromRoot.
     *  
     *  @param  br      A block root.
     *  @param  e1      An epoch.
     *  @param  j       An epoch.
     *  @param  store   A store.
     *  @param  links   A list of attestations.
     *
     *  @return         Proves that if an epoch e1 is justified in xs, and in the e1 + 1 
     *                  EBBs, from root bh, a previous epoch j < e1 is such 
     *                  that j is justified in xs, then j is justified in the 
     *                  xs from bh. 
     */
    lemma liftFromRoot(bh: Root, e1: Epoch, j: Epoch, store: Store, links: seq<PendingAttestation>)

        requires bh in store.blocks.Keys 
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        /** Epoch e1 is justified. */
        requires isJustifiedEpochFromRoot(bh, e1, store, links)
        /** There is an epoch before e1 that is justified. */
        requires j < e1 && isJustifiedEpoch(
               computeAllEBBsFromRoot(bh, e1, store), j, store, store.rcvdAttestations)
        /** Then epoch j is also justified from bh. */
        ensures  
            isJustifiedEpochFromRoot(bh, j, store, links)
    {
        assume(isJustifiedEpochFromRoot(bh, j, store, links));
    }

    /**  */
    lemma liftFromRootCP(bh: Root, cp: CheckPoint, store: Store, links: seq<PendingAttestation>)

        requires bh in store.blocks.Keys 
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        /** cp is justified. */
        requires cp.epoch > 0 
        requires cp.root in store.blocks.Keys
        requires isJustifiedCheckPointFromRoot(bh, cp, store, links)

        // requires j < cp1.epoch && isJustifiedEpoch(
        //        computeAllEBBsFromRoot(bh, e1, store), j, store, store.rcvdAttestations)
        /** There is a checkpoint before cp that is justified. */
        ensures  
            exists cp2 : CheckPoint :: 
                cp2.epoch < cp.epoch &&
                cp2.root in store.blocks.Keys &&
                cp2.root in chainRoots(cp.root, store) &&
                isJustifiedCheckPointFromRoot(bh, cp2, store, links)
    {
        assume(exists cp2 : CheckPoint :: cp2.epoch < cp.epoch &&
            cp2.root in store.blocks.Keys &&
            cp2.root in chainRoots(cp.root, store) &&
            isJustifiedCheckPointFromRoot(bh, cp2, store, links));
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
    predicate isJustifiedEpochFromRoot(br: Root, e: Epoch, store: Store, links : seq<PendingAttestation>) 
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
        isJustifiedEpoch(cr, e, store, links)
    }

    predicate isJustifiedCheckPointFromRoot(br: Root, cp: CheckPoint, store: Store, links : seq<PendingAttestation>) 
        requires br in store.blocks.Keys 
        requires cp.root in store.blocks.Keys
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  
    {
        //  Compute the EBBs from `br` before epoch e 
        var cr := computeAllEBBsFromRoot(br, cp.epoch, store);
        //  There are e + 1 EBBs in cr indexed from 0 to |e|
        //  cr[0] is the EBB at epoch e, cr[k] at epoch e - k, cr[|cr| - 1 == e] 
        //  at epoch e - |cr| + 1 == 0
        assert(|cr| == cp.epoch as nat + 1);
        //  Return whether epoch e is justified in `cr`
        cp.root == cr[0] && isJustifiedEpoch(cr, cp.epoch, store, links)
    }

    /**
     *  Whether a checkpoint is justified in a store.
     *  
     *  @param  cp      A checkpoint.
     *  @param  store   A store.
     *  @returns        Whether cp is justified but some attestations in store.
     */
    predicate isJustified(cp: CheckPoint, store: Store)
        /** The block root must in the store.  */
        requires cp.root in store.blocks.Keys         
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  
    {
        exists br: Root :: 
            br in store.blocks.Keys 
            // && cp.root == computeAllEBBsFromRoot(br, cp.epoch, store)[0]
            && isJustifiedEpochFromRoot(br, cp.epoch, store, store.rcvdAttestations) 
    }

    predicate isJustified2(cp: CheckPoint, store: Store)
        /** The block root must in the store.  */
        requires cp.root in store.blocks.Keys         
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        decreases cp.epoch 
    {
        if cp.epoch == 0 then // should be a the genesis block
        // @todo
            true
        else 
            exists cp2 : CheckPoint ::
                cp2.epoch < cp.epoch 
                && cp2.root in chainRoots(cp.root, store)
                && isJustified2(cp2, store)
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
        requires cp.epoch > 0 && isJustified2(cp, store)
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
    function lastJustified(br: Root, e: Epoch, store: Store, links : seq<PendingAttestation>): (c :  CheckPoint)
        /** The block root must in the store.  */
        requires br in store.blocks.Keys
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)        
        
        ensures 0 <= c.epoch <= e 
        ensures 
            var cr := computeAllEBBsFromRoot(br, e, store);
            isJustifiedEpochFromRoot(br, c.epoch, store, links) &&
            c.root == cr[e - c.epoch]
            && forall k :: c.epoch < k <= e ==> !isJustifiedEpochFromRoot(br, k, store, links)

    /**
     *  A checkpoint (B, j > 0) that is justified must have more then 2/3 of
     *  ingoing votes.
     *  
     *  @param  br      A block root.
     *  @param  e       An epoch.
     *  @param  store   A store.
     *  @param  links   A list of attestations.
     *
     *  @returns        Whether the EBB at epoch e is justified according to the votes in *                  `links`.         
     *  @note           ebbs should be such that ebbs[|ebbs| - 1] has slot 0. 
     *
     */
    lemma {:induction e} justifiedMustHaveTwoThirdIncoming(br: Root, e: Epoch, store: Store, links : seq<PendingAttestation>)
        /** The block root must in the store.  */
        requires br in store.blocks.Keys
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)
        /** Checkpoint at epoch e is justified. */
        requires e > 0 && isJustifiedEpochFromRoot(br, e, store, links)
        /** Checkpoint at epoch e has more than 2/3 incoming votes. */
        ensures 
            //  The EBBs before e. The checkpoint at e is (cr[0], e)
            var cr := computeAllEBBsFromRoot(br, e, store);
            //  The total number of attestations to EBB at epoch e is a supermajority.
            |collectValidatorsIndicesAttestatingForTarget(links, CheckPoint(e, cr[0]))| 
                >= ( 2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
    {
        if e > 0 && isJustifiedEpochFromRoot(br, e, store, links) {
            var cr := computeAllEBBsFromRoot(br, e, store);
            assert(isJustifiedEpoch(cr, e, store, links));
            assert(|cr| == e as nat + 1);
            assert( exists j :: j < e 
                && isJustifiedEpoch(cr, j, store, links) 
                && |collectValidatorsAttestatingForLink(links, CheckPoint(j as Epoch, cr[|cr| - 1 - j as nat]), CheckPoint(e, cr[0]))| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);
            var j :|  j < e  
                && isJustifiedEpoch(cr, j, store, links) 
                && 
                    |collectValidatorsAttestatingForLink(
                            links, 
                            CheckPoint(j as Epoch,  cr[|cr| - 1 - j as nat]),   // source
                            CheckPoint(e, cr[0]))|                              // target
                    >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;
            //  The number of total attestations for the target is larger than 
            //  than the number of attestations for target from each source
            attForTgtLargerThanLinks(links, 
                CheckPoint(j as Epoch, cr[|cr| - 1 - j as nat]), 
                CheckPoint(e, cr[0])
            );
            assert(|collectValidatorsIndicesAttestatingForTarget(links, CheckPoint(e, cr[0]))| >= ( 2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);
        }
    }

     

    /**
     *  A checkpoint (B, j > 0) that is justified must have more then 2/3 of
     *  ingoing votes.
     *  
     *  @param  br      A block root.
     *  @param  e       An epoch.
     *  @param  store   A store.
     *  @param  links   A list of attestations.
     *
     *  @returns        Whether the EBB at epoch e is justified according to the votes in *                  `links`.         
     *  @note           ebbs should be such that ebbs[|ebbs| - 1] has slot 0. 
     *
     */
    lemma {:induction false} justifiedCheckPointMustHaveTwoThirdIncoming(br: Root, cp: CheckPoint, store: Store, links : seq<PendingAttestation>)
        /** The block root must in the store.  */
        requires br in store.blocks.Keys

        requires cp.root in store.blocks.Keys

        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        /** Checkpoint at epoch e is justified. */
        requires cp.epoch > 0 && isJustifiedCheckPointFromRoot(br, cp, store, links)

        /** Checkpoint at epoch e has more than 2/3 incoming votes. */
        ensures |collectValidatorsIndicesAttestatingForTarget(links, cp)| 
                >= ( 2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
    {
        var cr := computeAllEBBsFromRoot(br, cp.epoch, store);
        assert(|cr| == cp.epoch as nat + 1);
        assert(cp.root == cr[0]);
        justifiedMustHaveTwoThirdIncoming(br, cp.epoch, store, links);
    }
}
