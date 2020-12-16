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
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../BeaconChainTypes.dfy"
include "../Helpers.dfy"
include "ForkChoiceTypes.dfy"

/**
 *  Provide definitions of chain, well-formed store, EBB, justified.
 */
module ForkChoiceHelpers {
    
    import opened Constants
    import opened Eth2Types
    import opened BeaconChainTypes
    import opened BeaconHelpers
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened ForkChoiceTypes
   
    /**
     *  Whether an attestation is well-formed.
     *
     *  @param  a       An attestattion.
     *  @param  store   A store.
     *  @param  links   A sequence of votes.
     */
    predicate isValidAttestation(a : AttestationData, store: Store, links: seq<PendingAttestation>) 
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)
        /** The head block in `a` is in the store. */
        requires a.beacon_block_root in store.blocks.Keys
    {
        //  The chain from a.beacon_block_root
        var xc := chainRoots(a.beacon_block_root, store);
        //  ep(a)
        var ep :=  compute_epoch_at_slot(a.slot);
        //  LEBB(a), LE(a) in the attestation
        var indexOfLEBB := computeEBB(xc, ep, store);
        //  EBBS
        var ebbs := computeAllEBBsIndices(xc, ep, store);
        //  Index of Last justified checkpoint in ebbs, LJ(a). in [0..ep]
        var indexOfLJ := lastJustified(xc, ebbs, links) as Epoch;
        assert(0 <= indexOfLJ <= ep); 

        //  The target root must be the last epoch boundary pair in chain(a.beacon_block_root)
        //  xc[indexOfLEBB] is the block root for epoch ep in chain(a.beacon_block_root)
        a.target == CheckPoint(ep, xc[indexOfLEBB])
        &&
        //  The source must be the last justified pair in chain(a.beacon_block_root)
        a.source == CheckPoint(ep - indexOfLJ, xc[ebbs[indexOfLJ]])
    }

    /**
     *  A well-formed store is a store for which each block
     *  with a slot > 0 has a parent in the store.
     *  Downward closure for the parent relation.
     *
     *  @param  store   A store.
     */
    predicate isClosedUnderParent(store: Store) 
    {
        forall k :: k in store.blocks.Keys && store.blocks[k].slot > 0 ==>
            store.blocks[k].parent_root in store.blocks.Keys
    }

    /**
     *  A store where the slots of parent blocks decrease.
     *
     *  @param  store   A store.
     */
    predicate isSlotDecreasing(store: Store)
        requires isClosedUnderParent(store)
    {
        forall k :: k in store.blocks.Keys && store.blocks[k].slot > 0 ==>
            store.blocks[store.blocks[k].parent_root].slot < store.blocks[k].slot
    }

    /**
     *  A chain of blocks roots is a totally ordered (decreasing, slot-wise)
     *  sequence of block roots, such that the slot of last block is zero.
     *  In this definition it is not required that the blocks are linkted
     *  with the parent_root relation.
     *
     *  @param  xr      A non-empty seq of block roots.
     *  @param  store   A store.
     *
     *  @example of a chain of size 6.  
     *  xr = [br5, br4, br3, br2, br1, br0] with 
     *  store.blocks[br5].slot == 0
     *  store.blocks[brk].slot >  store.blocks[brk - 1].slot for k >=1 
     */
    predicate isChain(xr: seq<Root>, store: Store)  
    {
        |xr| >= 1
        &&
        (forall i :: 0 <= i < |xr| ==> xr[i] in store.blocks.Keys)
        && 
        store.blocks[xr[|xr| - 1]].slot == 0 
        && 
        if |xr| == 1 then 
            //  last block with slot 0 is assumed to be a chain.
            true
        else 
            store.blocks[xr[0]].parent_root == xr[1] 
            && store.blocks[xr[0]].slot > store.blocks[xr[1]].slot
            && isChain(xr[1..], store)
    }

    /**
     *  The ancestors of a block root, as block roots.
     *  
     *  @param  br      A hash root of a block that is in the `store`.
     *  @param  store   A store (similar to the view of the validator).
     *  @returns        The ancestors's roots of the block `br` in  `store` with
     *                  `br` first and oldest (genesis) the last element of the sequence.
     *
     *  @example. br block at slot 264. 
     *  Store ancestors from br given by: br == b0 and then b1, b2, ... b5.
     *  |chainRoots(br, store)| == 6, chainRoots(br, store)[i] == bi
     *  store.blocks[chainRoots(br, store)[5]].slot ==  store.blocks[b5].slot == 0
     *  store.blocks[b5].slot == 0
     *  store.blocks[brk].slot >  store.blocks[brk - 1].slot for k >=1 
     *          |............|............|............|............|............|  ...
     *  block   b5----------->b4---------->b3---->b2------>b1------->b0 == br     
     *  slot    0             64           129    191      213       264
     */
    function chainRoots(br: Root, store: Store) : seq<Root>
        /** The block root must in the store.  */
        requires br in store.blocks.Keys
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        ensures |chainRoots(br, store)| >= 1
        /** Result is a slot-decreasing chain of linked roots the last one is slot 0..  */
        ensures isChain(chainRoots(br, store), store)
        // ensures forall i :: 0 <= i < |chainRoots(br, store)| ==>
        //     chainRoots(br, store)[i] in store.blocks.Keys 
        // ensures forall i :: 0 <= i < |chainRoots(br, store)| - 1 ==>
        //     store.blocks[chainRoots(br, store)[i]].parent_root == chainRoots(br, store)[i + 1]
        // ensures forall i :: 0 <= i < |chainRoots(br, store)| - 1 ==>
        //     store.blocks[chainRoots(br, store)[i]].slot > store.blocks[chainRoots(br, store)[i + 1]].slot
        // ensures  store.blocks[chainRoots(br, store)[|chainRoots(br, store)| - 1 ]].slot == 0 

        //  Computation always terminates as slot number decreases (well-foundedness).
        decreases store.blocks[br].slot
    {
        if ( store.blocks[br].slot == 0 ) then
            //  Should be the genesis block.
            [ br ]
        else 
            [ br ] + chainRoots(store.blocks[br].parent_root, store)
    }

    /**
     *  Compute the first block root in chain with slot number less than or equal to an epoch.
     *  Also known as EBB in the Gasper paper.
     *
     *  @param  xb      A sequence of block roots which is a chain. First element
     *                  is the block with highest slot.
     *  @param  e       An epoch.
     *  @param  store   A store.
     *  @return         The index i of the first block root in xb (left to right) with 
     *                  slot number less than or equal to the epoch `e`. 
     *  @note           We don't need the assumption that the list of blocks in `xb`
     *                  are ordered by slot number.
     *  @note           LEBB(xb) is defined by computeEBB(xb, epoch(first(xb))).
     *  
     *  epoch   0            1            2            3            4            5  
     *          |............|............|............|............|............|....
     *  block   b5----------->b4---------->b3---->b2------>b1------->b0      
     *  slot    0             64           129    191      213       264
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
     *  LEBB(xb) == (64, 1).
     *  
     *  Example 3. xb == [b2, b3, b4, b5].
     *  If e >= 3, EBB(xb, e) == (b2, 3). 
     *  If 1 <= e <= 2, EBB(xb, 2) == (64,e).
     *  LEBB(xb) == (64, 1).
     */
    function computeEBB(xb : seq<Root>, e :  Epoch, store: Store) : nat

        requires |xb| >= 1
        /** A slot decreasing chain of roots. */
        requires isChain(xb, store)

        ensures forall i :: 0 <= i < |xb| ==>
            xb[i] in store.blocks.Keys 
        /** The result is in the range of xb. */
        ensures computeEBB(xb, e, store) < |xb|
        ensures xb[computeEBB(xb, e, store)] in store.blocks.Keys
        /** The slot of the result is bounded. */
        ensures store.blocks[xb[computeEBB(xb, e, store)]].slot as nat <= e as nat * SLOTS_PER_EPOCH as nat 
        /** The prefix of xb[..result] has slots >  e * SLOTS_PER_EPOCH. */
        ensures forall j :: 0 <= j < computeEBB(xb, e, store) ==>
            store.blocks[xb[j]].slot as nat > e as nat * SLOTS_PER_EPOCH as nat

        /** This is guaranteed to termninate because the slot of the last 
         *  element of xb is 0 and condition of the if will eventually hold.
         */
        decreases xb 
    {
        // if |xb| == 1 then 
        //     //  only one choice, must be the block with slot == 0
        //     0
        // else 
        if store.blocks[xb[0]].slot as nat <= e as nat * SLOTS_PER_EPOCH as nat then 
            //  first block is a good one
            0
        else 
            //  first block has too large a slot, search suffix of xb.
            1 + computeEBB(xb[1..], e, store)
    }

    /**
     *  The EBB for epoch 0 is the last element of `xb`.
     *
     *  @param  xb      A sequence of block roots, the last one with slot == 0.
     *  @param  e       An epoch.
     *  @param  store   A store.
     */
    lemma {:induction xb} ebbForEpochZeroIsLast(xb : seq<Root>, e :  Epoch, store: Store)
        requires |xb| >= 1
        /** A slot decreasing chain of roots. */
        requires isChain(xb, store)

        ensures computeEBB(xb, 0, store) == |xb| - 1
    {   //  Thanks Dafny
    }
   
    /**
     *  Compute all the EBBs in a chain of block roots.
     *
     *  @param  xb      A sequence of block roots, the last one has slot equal to 0.
     *  @param  e       An epoch.
     *  @param  store   A store.
     *  @returns        The sequence of e + 1 EBBs for each epoch 0 <= e' <= e.
     *                  Element at index 0 <= k < |computeAllEBBsIndices()| is 
     *                  EBB(xb, e - k).
     *
     *  epoch   0            1            2            3            4            5  ...
     *          |............|............|............|............|............|  ...
     *  block   b5----------->b4---------->b3---->b2------>b1------->b0      
     *  slot    0             64           129    191      213       264
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
     *  LEBB(xb) == (64, 1).
     *  
     *  Example 3. xb == [b2, b3, b4, b5].
     *  If e >= 3, EBB(xb, e) == (b2, 3). 
     *  If 1 <= e <= 2, EBB(xb, 2) == (64,e).
     *  LEBB(xb) == (64, 1).
     */
    function computeAllEBBsIndices(xb : seq<Root>, e :  Epoch, store: Store) : seq<nat>
        requires |xb| >= 1
        /** A slot decreasing chain of roots. */
        requires isChain(xb, store)

        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

        /** Each epoch has a block associated to. */
        ensures |computeAllEBBsIndices(xb, e, store)| == e as nat + 1
        /** The index for each epoch is in the range of xb. */
        ensures forall i :: 0 <= i < e as nat + 1 ==> computeAllEBBsIndices(xb, e, store)[i] < |xb|
        /** The sequence returned is in decreasing order slot-wise. */
        ensures forall i :: 1 <= i < e as nat + 1 ==> 
            store.blocks[xb[computeAllEBBsIndices(xb, e, store)[i - 1]]].slot >= store.blocks[xb[computeAllEBBsIndices(xb, e, store)[i]]].slot
        /** The epoch e - i boundary block has a slot less than (e - i) * SLOTS_PER_EPOCH. */
        ensures forall i :: 0 <= i < e as nat + 1 
            ==> store.blocks[xb[computeAllEBBsIndices(xb, e, store)[i]]].slot as nat <= (e as nat - i) * SLOTS_PER_EPOCH as nat 
        /** The  blocks at index j less than the epoch e - i boundary block have a slot 
            larger than  (e - i) * SLOTS_PER_EPOCH. */
        ensures forall i :: 0 <= i < e as nat + 1 ==> 
            forall j :: 0 <= j < computeAllEBBsIndices(xb, e, store)[i] ==>
            store.blocks[xb[j]].slot as nat > (e as nat - i) * SLOTS_PER_EPOCH as nat
        ensures computeAllEBBsIndices(xb, e, store)[|computeAllEBBsIndices(xb, e, store)| - 1] == |xb| - 1
        
        decreases e 
    {
        ebbForEpochZeroIsLast(xb, e, store);
        //  Get the first boundary block less than or equal to e
        [computeEBB(xb, e, store)] +
        (
            //  if e > 0 recursive call, otherwise, terminate.
            if e == 0 then 
                []
            else 
                computeAllEBBsIndices(xb, e - 1, store)
        )
    }

    /**
     *  The index of the first (left to right) i.e. most recent justified ebb.
     *  
     *  @param  i       An index in the sequence of ebbs.
     *  @param  xb      A sequence of block roots.
     *  @param  ebbs    A sequence of indices. (xb[ebbs(j)],j) is EBB(xb, |ebbs| - 1 - j).
     *                  The last element (xb[ebbs[|ebbs| - 1]], |ebbs| - 1 - (|ebbs| - 1) )
     *                  i.e. (xb[|xb| - 1], 0) is assumed to be justified.
     *  @param  links   All the attestations received so far.
     *  @returns        Whether (xb[ebbs[i]], i) is justified according to the votes in *                  `links`.         
     *  @note           ebbs contains EBB for epochs |ebbs| - 1 down to 0. 
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
     *  @param  i       An index in the sequence of ebbs. This is the epoch
     *                  of a checkpoint but rather the epoch is |ebbs| - 1 - i 
     *  @param  xb      A sequence of block roots.
     *  @param  ebbs    A sequence of indices. (xb[ebbs(j)],j) is EBB(xb, |ebbs| - 1 - j).
     *                  The last element (xb[ebbs[|ebbs| - 1]], |ebbs| - 1 - (|ebbs| - 1) )
     *                  i.e. (xb[|xb| - 1], 0) is assumed to be justified.
     *  @param  links   All the attestations received so far.
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
