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
 *  Provide definitions of Epoch Boundaty Blocks (check points).
 */
module GasperEBBs {
    
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
     *  @param  xb      A sequence of block roots which is a chain. First element
     *                  is the block with highest slot.
     *  @param  e       An epoch.
     *  @param  store   A store.
     *
     *  @returns        The slot of the block of a checkpoint at epoch 0 has slot 0.
     */
    lemma checkPointAtEpochZeroHasSlotZero(xb: seq<Root>, e: Epoch, store: Store)
        requires |xb| >= 1
        /** A (slot decreasing) chain of roots. */
        requires isChain(xb, store)

        ensures 
            var cp0 := computeEBBsForAllEpochs(xb, e, store)[e];
            store.blocks[cp0].slot == 0      

    {   //  Thanks Dafny
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

    /**
     *  The last Epoch Boudary Block.
     *  
     *  @param  br      A block root.
     *  @param  e       An epoch.
     *  @param  store   A store.
     */
    function lastEBB(br: Root, e: Epoch, store: Store): CheckPoint
        /** The block root must in the store.  */
        requires br in store.blocks.Keys
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)
    {
        var xb := computeAllEBBsFromRoot(br, e, store);
        CheckPoint(e, xb[0])
    }

    /**
     *  The height of a block is one less than the length of 
     *  the chain of ancestors. [page 8, 3.1 of GasperFFG paper].
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
   
}
