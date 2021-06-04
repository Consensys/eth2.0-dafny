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

/**
 *  Provide definitions of chain, well-formed store, EBB, justified.
 */
module GasperHelpers {
    
    import opened Constants
    import opened Eth2Types
    import opened NativeTypes
    import opened BeaconChainTypes
    import opened BeaconHelpers
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened ForkChoiceTypes
   
    //   EBBs

    /**
     *  Compute all the EBBs in a chain of block roots.
     *
     *  @param  xb      A sequence of block roots which is a chain. First element
     *                  is the block with highest slot.
     *  @param  e       An epoch.
     *  @param  store   A store.
     *  @return         The sequence `s` of EBBs for each epoch 0 <= e' <= e in reverse order i.e.
     *                  the EBB at epoch e' is s[e = e'] with s[0] the EBB at epoch e and 
     *                  s[|s| - 1] the EBB at epoch 0.
     *  @note           LEBB(xb) can be obtained by 
     *                      computeEBBsForAllEpochs(xb, epoch(first(xb)), store)[0].
     *  
     *  epoch   0            1            2            3            4            5           6
     *          |............|............|............|............|............|...........|
     *  block   b5----------->b4---------->b3---->b2------>b1--------->b0      
     *  slot    0             32           65      95      105        134
     *       
     *  For any sequence xb == [..,b5], EBB(xb, 0) == (b5, 0).
     *
     *  Example 1. xb == [b0, b1, b2, b3, b4, b5].
     *  if e >= 5, EBB(xb, e) == (b0, e). 
     *  If e == 4, EBB(xb, 4) == b1 (last block in epoch 4). 
     *  As epoch(b0) == 4, LEBB(xb) == EBB(xb, epoch(b0)) == b1.
     *
     *  Example 2. xb == [b4, b5].
     *  If e >= 2, EBB(xb,e) == (b4, e). If e == 1, EBB(xb, 1) == (b4,1).
     *  LEBB(xb) == (32, 1).
     *  
     *  Example 3. xb == [b2, b3, b4, b5].
     *  If e >= 3, EBB(xb, e) == (b2, 3). 
     *  If e == 2, EBB(xb, 2) == (b4, 2).
     *  If e == 1, EBB(xb, 1) == (b0, 1).
     *  LEBB(xb) == (b4, 2).
     *  computeEBBsForAllEpochs(xb, 6) = [b0, b0, b1, b2, b4, b5, b5]
     *
     */
    function computeEBBsForAllEpochs(xb: seq<Root>, e: Epoch, store: Store): seq<Root>

        requires |xb| >= 1
        /** A (slot decreasing) chain of roots. */
        requires isChain(xb, store)

        /** The result is in the range of xb. */
        ensures |computeEBBsForAllEpochs(xb, e, store)| == e as nat + 1

        /** All the block roots are in the store. */
        ensures forall b:: b in computeEBBsForAllEpochs(xb, e, store) ==> b in store.blocks.Keys

        /** EBB for epoch 0 is a block with slot == 0. */
        ensures store.blocks[computeEBBsForAllEpochs(xb, e, store)[e]].slot == 0  

        /** The slots of the EBB at epoch k is less or equal to k * SLOTS_PER_EPOCH. */
        ensures forall k:: 0 <= k <= e ==>
            //  EBBs are collected in reverse order, so EBB at epoch k has index e - k
            store.blocks[computeEBBsForAllEpochs(xb, e, store)[e - k]].slot as nat <= k as nat * SLOTS_PER_EPOCH as nat

        decreases xb, e
    {
        if store.blocks[xb[0]].slot as nat <= e as nat * SLOTS_PER_EPOCH as nat then 
            //  first block is a good one. If e > 0 continue with e - 1, stop otherwise.
            assert(e == 0 ==> store.blocks[xb[0]].slot == 0);
            [xb[0]] + 
                (if e > 0 then computeEBBsForAllEpochs(xb, e - 1, store) else [])
        else 
            //  First block has too large a slot, search suffix of xb.
            //  Note that this implies that the slot > 0 and hence |xb| >= 2 
            assert(|xb| >= 2);
            computeEBBsForAllEpochs(xb[1..], e, store)
    }

    /**
     *  Compute all the EBBs in a chain starting at a given block root.
     *
     *  @param  br      A block root.
     *  @param  e       An epoch.
     *  @param  store   A store.
     *  @return         The sequence `s` of EBBs for each epoch 0 <= e' <= e in reverse order i.e.
     *                  the EBB at epoch e' is s[e = e'] with s[0] the EBB at epoch e and 
     *                  s[|s| - 1] the EBB at epoch 0.
     *  @note           LEBB(br) is defined by 
     *                      computeAllEBBsFromRoot(xb, epoch(first(xb)), store)[0].
     */
    function computeAllEBBsFromRoot(br: Root, e: Epoch, store: Store): seq<Root>
        /** The block root must in the store.  */
        requires br in store.blocks.Keys
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        /** The result is in the range of xb. */
        ensures |computeAllEBBsFromRoot(br, e, store)| == e as nat + 1

        /** All the block roots are in the store. */
        ensures forall b:: b in computeAllEBBsFromRoot(br, e, store) ==> b in store.blocks.Keys

        /** EBB for epoch 0 is a block with slot == 0. */
        ensures store.blocks[computeAllEBBsFromRoot(br, e, store)[e]].slot == 0  

        /** The slots of the EBB at epoch k is less or equal to k * SLOTS_PER_EPOCH. */
        ensures forall k:: 0 <= k <= e ==>
            //  EBBs are collected in reverse order, so EBB at epoch k has index e - k
            store.blocks[computeAllEBBsFromRoot(br, e, store)[e - k]].slot as nat <= k as nat * SLOTS_PER_EPOCH as nat
    {
        var cr := chainRoots(br, store);
        computeEBBsForAllEpochs(cr, e, store)
    }

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
     *
     *  @param  br      A block root.
     *  @param  e1      An epoch.
     *  @param  j       An epoch.
     *  @param  store   A store.
     *  @param  links   A list of attestations.
     *
     *  @return         Proves that if an epoch e1 is justified in xs, the e1 + 1 
     *                  EBBs, from root bh, and a previous epoch j < e1 is such 
     *                  that j is justified in the xs, then j is justified in the 
     *                  xs from nh. 
     */
    lemma foo(bh: Root, e1: Epoch, j: Epoch, store: Store, links : seq<PendingAttestation>)

        requires bh in store.blocks.Keys 
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        requires isJustifiedEpochFromRoot(bh, e1, store, links)
        requires j < e1 && isJustifiedEpoch(
               computeAllEBBsFromRoot(bh, e1, store), j, store, store.rcvdAttestations)
        ensures  
            isJustifiedEpochFromRoot(bh, j, store, links)
    {
        assume(isJustifiedEpochFromRoot(bh, j, store, links));
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

    /**
     *  The most recent justified EBB before epoch.
     */
    function lastJustified(br: Root, e: Epoch, store: Store, links : seq<PendingAttestation>): (l : Epoch)
        /** The block root must in the store.  */
        requires br in store.blocks.Keys
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)        ensures 0 <= l <= e
        ensures 
            var cr := computeAllEBBsFromRoot(br, e, store);
            isJustifiedEpochFromRoot(br, l, store, links) &&
            forall k :: l < k <= e ==> !isJustifiedEpochFromRoot(br, k, store, links)

    //  Finalisation definition.   
            
    /** 
     *  Whether checkpoint at epoch f is 1-finalised.
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

    //  Some useful lemmas about the sequence of EBBs.

    /**
     *  If first block has an epoch larger than e, the blocks in the EBBs before
     *  `e` are in tail(xb).
     *
     *  @param  xb      A sequence of block roots which is a chain. First element
     *                  is the block with highest slot.
     *  @param  e       An epoch.
     *  @param  store   A store.    
     */
    lemma skipFirstBlock(xb: seq<Root>, e: Epoch, store: Store)
        requires |xb| >= 1
        /** A (slot decreasing) chain of roots. */
        requires isChain(xb, store)
        /** The first block's epoch is larger than e.  */
        requires store.blocks[xb[0]].slot as nat > e as nat * SLOTS_PER_EPOCH as nat 
        /** The blocks in the EBBs before e are in tail(xb) */
        ensures computeEBBsForAllEpochs(xb, e, store) == computeEBBsForAllEpochs(xb[1..], e, store)
    {   //  Thanks Dafny
    }

    /**
     *  Relate EBBs at successive epochs.
     *
     *  @param  xb      A sequence of block roots which is a chain. First element
     *                  is the block with highest slot.
     *  @param  e       An epoch.
     *  @param  store   A store.    
     */
    lemma {:induction xb, e} succEBBs(xb: seq<Root>, e: Epoch, store: Store)
        requires |xb| >= 1
        /** A (slot decreasing) chain of roots. */
        requires isChain(xb, store)
        /** Not epoch 0. */
        requires e > 0 
        /** The EBBs from epoch e - 1 are the suffix of the EBBs at epoch e. */
        ensures 
            computeEBBsForAllEpochs(xb, e - 1, store) == computeEBBsForAllEpochs(xb, e, store)[1..]

        decreases xb, e 
    {
        if store.blocks[xb[0]].slot as nat <= e as nat * SLOTS_PER_EPOCH as nat {
            //  Thanks Dafny
        } else {
            if e - 1 == 0 {
                //  Thanks Dafny 
            } else {
                calc == {
                    computeEBBsForAllEpochs(xb, e - 1, store);
                    {  skipFirstBlock(xb, e, store); }
                    computeEBBsForAllEpochs(xb[1..], e - 1, store);
                }
                succEBBs(xb[1..], e - 1, store);
            }
        }
    }

    /**
     *  Relate EBBs at successive epochs.
     *
     *  @param  br      A block root.
     *  @param  e       An epoch.
     *  @param  store   A store.
     *  @return         See ensures.
     */
    lemma succEBBsFromRoot(br: Root, e: Epoch, store: Store)
        /** The block root must in the store.  */
        requires br in store.blocks.Keys
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)
        /** Not epoch 0 */
        requires e > 0 
        /** The EBBs from epoch e - 1 are the suffix of the EBBs at epoch e. */
        ensures computeAllEBBsFromRoot(br, e - 1, store) == 
            computeAllEBBsFromRoot(br, e, store)[1..]
    {
        var cr := chainRoots(br, store);
        succEBBs(cr, e, store);
    }

    /**
     *  The height of a block is one less than the length of 
     *  the chain of ancestors.
     *  
     *  @param  br      A block root.
     *  @param  e       An epoch.
     *  @param  store   A store.
     */
    lemma {:induction br} heightOfBlockIsLengthOfAncestorsChain(br: Root, store: Store)
        /** The block root must in the store.  */
        requires br in store.blocks.Keys
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)
        /** Lenght constraint. */
        ensures 0 <= height(br, store) == |chainRoots(br, store)| - 1

        decreases store.blocks[br].slot
    {   //  Thanks Dafny
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
     *  A 1-finalsised checkpoint is justified.
     *  
     *  @param  br      A block root.
     *  @param  f       An epoch.
     *  @param  store   A store.
     *  @param  links   A list of attestations.
     *
     */
    lemma oneFinalisedImpliesJustified(br: Root, f: Epoch, store: Store, links : seq<PendingAttestation>)
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
}
