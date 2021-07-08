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
include "./GasperJustification.dfy"
/**
 *  Provide definitions of chain, well-formed store, EBB, justified.
 */
module GasperFinalisation {
    
    import opened Constants
    import opened Eth2Types
    import opened NativeTypes
    import opened BeaconChainTypes
    import opened BeaconHelpers
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened ForkChoiceTypes
    import opened GasperEBBs
    import opened GasperJustification

    //  Finalisation definition.   
            
    /** 
     *  Whether checkpoint at epoch f is 1-finalised.
     *  
     *  @param  br      A block root.
     *  @param  f       An epoch.
     *  @param  store   A store.
     *  @param  links   A list of attestations.
     *
     *  @returns        Whether the checkpoint c at epoch f in the EBBs from br,
     *                  is 1-finalised. It is iff (i) c is justifiedm and (ii) there
     *                  is supermajority link from c to the checkpoint at epoch f + 1.   
     *  @note           ebbs should be such that ebbs[|ebbs| - 1] has slot 0. 
     *
     */
    predicate isOneFinalisedFromRoot(br: Root, f: Epoch, store: Store, links : seq<PendingAttestation>)
        requires br in store.blocks.Keys 
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  
        /** f is an epoch in ebbs, and each index represents an epoch so must be uint64.
         *  f + 1 must be an epoch
         */
        requires 0 <= f as nat + 1 <= MAX_UINT64 
    {
        //  Compute the EBBs from `br` before epoch f + 1 
        var ebbs := computeAllEBBsFromRoot(br, f + 1, store);
        //  1-finalised: EBB at epoch f is justified (take suffix of ebbs that
        // contains the ebbs from epoch f to epoch 0) 
        isJustifiedEpoch(ebbs[1..], f, store, links) &&
        //  and it justifies the next EBB. note: the EBBs are in reverse order in `ebbs`
        |collectValidatorsAttestatingForLink(
            links,  
            CheckPoint(f, ebbs[|ebbs| - 1 - f as nat]),                     //  source
            CheckPoint(f + 1, ebbs[|ebbs| - 1 - (f + 1) as nat]))|          //  target
                >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
    }

    /** 
     *  Whether a checkpoint is 1-finalised relative to a given block head.
     *  
     *  @param  br      A block root.
     *  @param  cp      A checkpoint.
     *  @param  store   A store.
     *  @param  links   A list of attestations.
     *
     *  @returns        Whether the checkpoint cp is 1-finalised.
     *                  It is iff (i) cp is justified and (ii) there is a supermajority
     *                  link from cp to the next checkpoint at epoch cp.epoch + 1.   
     *
     */
     predicate isOneFinalisedCheckPointFromRoot(br: Root, cp: CheckPoint, store: Store, links : seq<PendingAttestation>) 
        /** The block root is in store. */
        requires br in store.blocks.Keys 
        /** The checkpoint is valid. */
        requires cp.root in store.blocks.Keys
        requires 0 <= cp.epoch as nat + 1 <= MAX_UINT64 

        /** The store is well-formed. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  
    {        
        //  1-finalised must be justified
        isJustifiedCheckPointFromRoot(br, cp, store, links) 
        //  and it justifies the next EBB. note: the EBBs are in reverse order in `ebbs`
        && 
            var f := cp.epoch;
            //  Compute the EBBs from `br` before epoch cp.epoch + 1 
            var ebbs := computeAllEBBsFromRoot(br, f + 1, store);
            |collectValidatorsAttestatingForLink(
                links,  
                CheckPoint(f, ebbs[|ebbs| - 1 - f as nat]),                     //  source
                CheckPoint(f + 1, ebbs[|ebbs| - 1 - (f + 1) as nat]))|          //  target
                    >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
    }
    
    predicate isOneFinalised(cp: CheckPoint, store: Store) 
        /** The block root must in the store.  */
        requires cp.root in store.blocks.Keys      
        requires 0 <= cp.epoch as nat + 1 <= MAX_UINT64 
   
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

    {
        exists br: Root :: 
            br in store.blocks.Keys 
            // && cp == CheckPoint(cp.epoch, computeAllEBBsFromRoot(br, cp.epoch, store)[0])
            && cp.root == computeAllEBBsFromRoot(br, cp.epoch, store)[0]
            && isOneFinalisedFromRoot(br, cp.epoch, store, store.rcvdAttestations) 
    }

    predicate isOneFinalised2(cp: CheckPoint, store: Store) 
        /** The block root must in the store.  */
        requires cp.root in store.blocks.Keys      
        requires 0 <= cp.epoch as nat + 1 <= MAX_UINT64 
   
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  
    {
        //  cp is justified
        isJustified2(cp, store)
        //  it justifies a checkpoint at epoch cp.epoch + 1
        && exists cp2 : CheckPoint ::
            cp2.epoch == cp.epoch + 1
            && cp2.root in store.blocks.Keys 
            && cp.root in chainRoots(cp2.root, store)
            && |collectValidatorsAttestatingForLink(store.rcvdAttestations, cp, cp2)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1   
    }

    /**
     *  
     *  @param  i       An index in the sequence of ebbs. This is not the epoch
     *                  of a checkpoint but rather the epoch is |ebbs| - 1 - i 
     *  @param  xb      A sequence of block roots from most recent to genesis root.
     *  @param  ebbs    A sequence of indices. (xb[ebbs(j)],j) is EBB(xb, |ebbs| - 1 - j).
     *                  The last element (xb[ebbs[|ebbs| - 1]], |ebbs| - 1 - (|ebbs| - 1) )
     *                  i.e. (xb[|xb| - 1], 0) is assumed to be justified.
     *  @param  links   All the attestations received so far.
     *  @returns        Whether (xb[ebbs[i]], i) is 2-finalised according to the votes in *                  `links`.         
     *  @note           ebbs contains EBB for epochs |ebbs| - 1 down to 0. 
     */
    // predicate isTwoFinalised(i: nat, xb : seq<Root>, ebbs: seq<nat>,  links : seq<PendingAttestation>)
    //     /** i is an index in ebbs, and each index represents an epoch so must be uint64.
    //      *  i is not the first or second index as to be 1-finalised it needs to have at least on descendant.
    //      */
    //     requires 1 < i < |ebbs|  <= 0x10000000000000000
    //     // requires 0 < i 
    //     /** `xb` has at least two blocks. */
    //     requires |xb| >= 3
    //     /** The last element of ebbs is the EBB at epoch 0 and should be the last block in `xb`. */
    //     requires ebbs[|ebbs| - 1] == |xb| - 1
        
    //     /** (xb[ebbs[j]], j) is the EBB at epoch |ebbs| - j and must be an index in `xb`.  */
    //     requires forall i :: 0 <= i < |ebbs| ==> ebbs[i] < |xb|

    //     decreases |ebbs| - i 
    // {
    //     //  2-finalised
    //     isJustified(i, xb, ebbs, links) &&
    //     //  index i - 1 is justified two 
    //     isJustified(i - 1, xb, ebbs, links) &&
    //     //  index i - 2 is justified by i
    //     //  note: the EBBs are in reverse order in `ebbs`
    //     |collectValidatorsAttestatingForLink(
    //         links, 
    //         CheckPoint(i as Epoch, xb[ebbs[i]]),                //  source
    //         CheckPoint((i - 2) as Epoch, xb[ebbs[i - 2]]))|     //  target
    //              >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
    // }

    /** 
     *  A 1-finalised checkpoint is justified.
     *  
     *  @param  br      A block root.
     *  @param  f       An epoch.
     *  @param  store   A store.
     *  @param  links   A list of attestations.
     *
     */
    lemma oneFinalisedImpliesJustifiedFromRoot(br: Root, f: Epoch, store: Store, links : seq<PendingAttestation>)
        requires br in store.blocks.Keys 
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  
        /** f is an epoch in ebbs, and each index represents an epoch so must be uint64.
         *  f + 1 must be an epoch
         */
        requires 0 < f as nat + 1 <= MAX_UINT64 
        /** Checkpoint at Epoch f is 1-finalised. */
        requires isOneFinalisedFromRoot(br, f, store, links)
        /** ChecvkPoint at Epoch f is justified. */
        ensures isJustifiedEpochFromRoot(br, f, store, links)
    {
        var cr := computeAllEBBsFromRoot(br, f + 1, store);
        var cr2 := computeAllEBBsFromRoot(br, f , store);
        succEBBsFromRoot(br, f + 1 , store);
    }

    lemma oneFinalisedImpliesJustifiedFromRootCP(br: Root, cp: CheckPoint, store: Store, links : seq<PendingAttestation>)
        requires br in store.blocks.Keys 
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  
        /** f is an epoch in ebbs, and each index represents an epoch so must be uint64.
         *  f + 1 must be an epoch
         */
        requires cp.root in store.blocks.Keys
        requires 0 < cp.epoch as nat + 1 <= MAX_UINT64 
        /** Checkpoint at Epoch f is 1-finalised. */
        requires isOneFinalisedCheckPointFromRoot(br, cp, store, links)
        /** ChecvkPoint at Epoch f is justified. */
        ensures isJustifiedCheckPointFromRoot(br, cp, store, links)
    {
        var cr := computeAllEBBsFromRoot(br, cp.epoch + 1, store);
        var cr2 := computeAllEBBsFromRoot(br, cp.epoch , store);
        succEBBsFromRoot(br, cp.epoch + 1 , store);
    }

    /** 
     *  A 1-finalised checkpoint is justified.
     *  
     *  @param  br      A block root.
     *  @param  f       An epoch.
     *  @param  store   A store.
     *  @param  links   A list of attestations.
     *
     */
    // lemma oneFinalisedImpliesJustified(cp: CheckPoint, store: Store)
    //     /** Checkpoint is valid. */
    //     requires cp.root in store.blocks.Keys 
    //     requires 0 < cp.epoch as nat + 1 <= MAX_UINT64 
    //     /** The store is well-formed, each block with slot != 0 has a parent
    //         which is itself in the store. */
    //     requires isClosedUnderParent(store)
    //     requires isSlotDecreasing(store)  
        
    //     /** Checkpoint cp is 1-finalised. */
    //     requires isOneFinalised(cp, store)

    //     /** CheckPoint cp is justified. */
    //     ensures isJustified(cp, store)
    // {
    //     //  Get a witness for one-finalisation.
    //     var br :| br in store.blocks.Keys && isOneFinalisedFromRoot(br, cp.epoch, store, store.rcvdAttestations);
    //     //  Apply version of this lemma from root.
    //     oneFinalisedImpliesJustifiedFromRoot(br, cp.epoch, store, store.rcvdAttestations);
    // }

    lemma oneFinalisedImpliesJustified(cp: CheckPoint, store: Store)
        // requires br in store.blocks.Keys 
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  
        /** f is an epoch in ebbs, and each index represents an epoch so must be uint64.
         *  f + 1 must be an epoch
         */
        requires cp.root in store.blocks.Keys
        requires 0 < cp.epoch as nat + 1 <= MAX_UINT64 
        /** Checkpoint at Epoch f is 1-finalised. */
        requires isOneFinalised2(cp, store)
        ensures isJustified2(cp, store)
    {
        //  Thanks Dafny
    }
}
