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
// include "../utils/NativeTypes.dfy"
include "Attestations.dfy"
include "BeaconChainTypes.dfy"
// include "StateTransition.dfy"
include "Helpers.dfy"
// include "../utils/SeqHelpers.dfy"

include "ForkChoiceTypes.dfy"

/**
 * Fork choice rule for the Beacon Chain.
 */
module ForkChoiceHelpers {
    
    import opened Constants
    import opened Eth2Types
    // import opened NativeTypes
    import opened BeaconChainTypes
    // import opened StateTransition
    import opened BeaconHelpers
    import opened Attestations
    import opened ForkChoiceTypes
    // import opened SeqHelpers
   
    /**
     *  The view defined by a block.
     *  
     *  @param  br      A hash root of a block.
     *  @param  store   A store (similar to the view of the validator).
     *  @returns        The ancestors of the block `br` in  `store`.
     */
    function chain(br: Root, store: Store) : seq<BeaconBlock>
        requires br in store.blocks.Keys
        requires forall k :: k in store.blocks.Keys && store.blocks[k].slot > 0 ==>
            store.blocks[k].parent_root in store.blocks.Keys
            && store.blocks[store.blocks[k].parent_root].slot < store.blocks[k].slot 

        ensures |chain(br, store)| >= 1
        ensures chain(br, store)[|chain(br, store)| - 1].slot == 0 
        //  Computation always terminates as slot number decreases (well-foundedness).
        decreases store.blocks[br].slot
    {
        if ( store.blocks[br].slot == 0 ) then
            //  Should be the genesis block.
            [ store.blocks[br] ]
        else 
            [ store.blocks[br] ] + chain(store.blocks[br].parent_root, store)
    }

    /**
     *  Same as above but using block roots and stores instead of blocks.
     */
    function chainRoots(br: Root, store: Store) : seq<Root>
        requires br in store.blocks.Keys
        requires forall k :: k in store.blocks.Keys && store.blocks[k].slot > 0 ==>
            store.blocks[k].parent_root in store.blocks.Keys
            && store.blocks[store.blocks[k].parent_root].slot < store.blocks[k].slot 

        ensures |chainRoots(br, store)| >= 1
        /** All the root values collected must be in the store.blocks map. */
        ensures forall r :: r in chainRoots(br, store) ==> r in store.blocks.Keys
        /** The last root value id mapped to a block with slot 0. */
        ensures store.blocks[chainRoots(br, store)[|chainRoots(br, store)| - 1]].slot == 0 
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
     *  Compute the first epoch boundary block.
     *
     *  @param  xb  A sequence of blocks.
     *  @param  e   An epoch.
     *  @return     The index i of the first block in xb (left to right) with 
     *              slot number less the epoch `e` slot. 
     *  @note       We don't need the assumption that the list of blocks in `xb`
     *              are ordered by slot number.
     */
    function computeFirstEBBIndex(xb : seq<BeaconBlock>, e :  Epoch) : nat
        requires |xb| >= 1
        /** Last block has slot 0. */
        requires xb[|xb| - 1].slot == 0 

        /** The result is in the range of xb. */
        ensures computeFirstEBBIndex(xb, e) < |xb|
        /** The slot of the result is bounded. */
        ensures xb[computeFirstEBBIndex(xb, e)].slot as nat <= e as nat * SLOTS_PER_EPOCH as nat 
        /** The prefix of xb[..result] has slots >  e * SLOTS_PER_EPOCH. */
        ensures forall j :: 0 <= j < computeFirstEBBIndex(xb, e) ==>
            xb[j].slot as nat > e as nat * SLOTS_PER_EPOCH as nat
        decreases xb 
    {
        if |xb| == 1 then 
            //  only one choice, must be the block with slot == 0
            0
        else if xb[0].slot as nat <= e as nat * SLOTS_PER_EPOCH as nat then 
            //  first block isd a good one
            0
        else 
            //  first block has too large a slot, search suffix of xb.
            1 + computeFirstEBBIndex(xb[1..], e)
    }

    /**
     *  Compute the first epoch boundary block root.
     *
     *  @param  xb      A sequence of block roots.
     *  @param  e       An epoch.
     *  @param  store   A store.
     *  @return         The index i of the first block root in xb (left to right) with 
     *                  slot number less the epoch `e` slot. 
     *  @note           We don't need the assumption that the list of blocks in `xb`
     *                  are ordered by slot number.
     */
    function computeFirstEBBIndexFromRoots(xb : seq<Root>, e :  Epoch, store: Store) : nat
        requires |xb| >= 1
        requires forall r :: r in xb ==> r in store.blocks.Keys 
        /** Last block has slot 0. */
        requires store.blocks[xb[|xb| - 1]].slot == 0 

        /** The result is in the range of xb. */
        ensures computeFirstEBBIndexFromRoots(xb, e, store) < |xb|
        /** The slot of the result is bounded. */
        ensures store.blocks[xb[computeFirstEBBIndexFromRoots(xb, e, store)]].slot as nat <= e as nat * SLOTS_PER_EPOCH as nat 
        /** The prefix of xb[..result] has slots >  e * SLOTS_PER_EPOCH. */
        ensures forall j :: 0 <= j < computeFirstEBBIndexFromRoots(xb, e, store) ==>
            store.blocks[xb[j]].slot as nat > e as nat * SLOTS_PER_EPOCH as nat
        decreases xb 
    {
        if |xb| == 1 then 
            //  only one choice, must be the block with slot == 0
            0
        else if store.blocks[xb[0]].slot as nat <= e as nat * SLOTS_PER_EPOCH as nat then 
            //  first block isd a good one
            0
        else 
            //  first block has too large a slot, search suffix of xb.
            1 + computeFirstEBBIndexFromRoots(xb[1..], e, store)
    }

    /**
     *  Compute the subsequence of indices of epoch boundary blocks.
     *  @param  xb  A sequence of blocks.
     *  @param  e   An epoch.
     *  @returns    The sequence of EBBs indices in xb from epoch e to epoch 0.
     *  @note       We don't need the assumption that the list of blocks in `xb`
     *              are ordered by slot number.
     *  @note       In the Gasper paper, there is a definition of a epoch boundary pair (A, j).
     *              If xb is a chain (e.g. view(B)), (A, j) is the j-th epoch boundary block
     *              iff xb[computeEBBs(xb, j)] == A.
     */
    function computeEBBs(xb : seq<BeaconBlock>, e :  Epoch) : seq<nat>
        requires |xb| >= 1
        /** Last block has slot 0. */
        requires xb[|xb| - 1].slot == 0 

        /** Each epoch has a block associated to. */
        ensures |computeEBBs(xb, e)| == e as nat + 1
        /** The index for each epoch is in the range of xb. */
        ensures forall i :: 0 <= i < e as nat + 1 ==> computeEBBs(xb, e)[i] < |xb|
        /** The sequence returned is in decreasing order slot-wise. */
        ensures forall i :: 1 <= i < e as nat + 1 ==> 
            xb[computeEBBs(xb, e)[i - 1]].slot >= xb[computeEBBs(xb, e)[i]].slot
        /** The epoch e - i boundary block has a slot less than (e - i) * SLOTS_PER_EPOCH. */
        ensures forall i :: 0 <= i < e as nat + 1 
            ==> xb[computeEBBs(xb, e)[i]].slot as nat <= (e as nat - i) * SLOTS_PER_EPOCH as nat 
        /** The  blocks at index j less than the epoch e - i boundary block have a slot 
            larger than  (e - i) * SLOTS_PER_EPOCH. */
        ensures forall i :: 0 <= i < e as nat + 1 ==> 
            forall j :: 0 <= j < computeEBBs(xb, e)[i] ==>
            xb[j].slot as nat > (e as nat - i) * SLOTS_PER_EPOCH as nat

        decreases e 
    {
        //  Get the first boundary block
        [computeFirstEBBIndex(xb, e)] +
        (
            //  if e > 0 recursive call, otherwise, terminate.
            if e == 0 then 
                []
            else 
                computeEBBs(xb, e - 1)
        )
    }

    /**
     *  Compute the subsequence of indices of epoch boundary block roots..
     *  @param  xb      A sequence of block roots.
     *  @param  e       An epoch.
     *  @param  store   A store.
     *  @returns        The sequence of EBBs indices in xb from epoch e to epoch 0.
     *  @note           We don't need the assumption that the list of blocks in `xb`
     *                  are ordered by slot number.
     *  @note           In the Gasper paper, there is a definition of a epoch boundary pair (A, j).
     *                  If xb is a chain (e.g. view(B)), (A, j) is the j-th epoch boundary block
     *                  iff xb[computeEBBs(xb, j)] == A.
     */
    function computeEBBsFromRoots(xb : seq<Root>, e :  Epoch, store: Store) : seq<nat>
        requires |xb| >= 1
        requires forall r :: r in xb ==> r in store.blocks.Keys 
        /** Last block has slot 0. */
        requires store.blocks[xb[|xb| - 1]].slot == 0 

        /** Each epoch has a block associated to. */
        ensures |computeEBBsFromRoots(xb, e, store)| == e as nat + 1
        /** The index for each epoch is in the range of xb. */
        ensures forall i :: 0 <= i < e as nat + 1 ==> computeEBBsFromRoots(xb, e, store)[i] < |xb|
        /** The sequence returned is in decreasing order slot-wise. */
        ensures forall i :: 1 <= i < e as nat + 1 ==> 
            store.blocks[xb[computeEBBsFromRoots(xb, e, store)[i - 1]]].slot >= store.blocks[xb[computeEBBsFromRoots(xb, e, store)[i]]].slot
        /** The epoch e - i boundary block has a slot less than (e - i) * SLOTS_PER_EPOCH. */
        ensures forall i :: 0 <= i < e as nat + 1 
            ==> store.blocks[xb[computeEBBsFromRoots(xb, e, store)[i]]].slot as nat <= (e as nat - i) * SLOTS_PER_EPOCH as nat 
        /** The  blocks at index j less than the epoch e - i boundary block have a slot 
            larger than  (e - i) * SLOTS_PER_EPOCH. */
        ensures forall i :: 0 <= i < e as nat + 1 ==> 
            forall j :: 0 <= j < computeEBBsFromRoots(xb, e, store)[i] ==>
            store.blocks[xb[j]].slot as nat > (e as nat - i) * SLOTS_PER_EPOCH as nat

        decreases e 
    {
        //  Get the first boundary block
        [computeFirstEBBIndexFromRoots(xb, e, store)] +
        (
            //  if e > 0 recursive call, otherwise, terminate.
            if e == 0 then 
                []
            else 
                computeEBBsFromRoots(xb, e - 1, store)
        )
    }

    /**
     *  LEBB definition.
     *
     *  @param  br      A block root. Ideally the block root of an attestation.
     *  @param  store   The current view.
     *  @returns        The latest epoch boudasry block for `br`.
     */
    function latestEBBs(br: Root, store: Store) :  BeaconBlock
        requires br in store.blocks.Keys
        requires forall k :: k in store.blocks.Keys && store.blocks[k].slot > 0 ==>
            store.blocks[k].parent_root in store.blocks.Keys
            && store.blocks[store.blocks[k].parent_root].slot < store.blocks[k].slot
        
    {
        //  seq of beacon blocks (ancestors of br)
        var ch := chain(br, store);
        var bl := store.blocks[br];
        var slot := bl.slot;
        var lebbIndex := computeFirstEBBIndex(ch, compute_epoch_at_slot(slot));
        ch[lebbIndex]
    }

    /**
     *  Justification definition.
     *  
     *  @param  i           An index in `xv`.
     *  @param  xv          A sequence of EBB ordered by epochs from largest (first) to 0 (last).
     *                      Each xv[i] is an EBB for epoch i.
     *  @param  links       The attestations with src and tgt checkpoints.
     *  @param  refSet      A non-negative int typically the number of validators.
     *  @returns            Whether the checkpoint `xv[i]` is justified.
     *
     *  @note               The difficulty (if any) here is that `xv` has blocks but
     *                      links has attestations wich src and target that are roots.
     *                      So we need the store and the map root --> block to make the link.  
     */
    predicate isJustified(i: nat, xv : seq<CheckPoint>, links : seq<PendingAttestation>, refSet: nat) 
        requires |xv| >= 1
        requires i < |xv|
        /** The checkpoints must be in decreasing order epoch-wise.  */
        requires forall i :: 0 <= i < |xv| ==> xv[i].epoch as nat == |xv| - i 
        /** SuperMajority link requires src.epoch < tgt.epoch. */
        // requires forall i, j :: 0 <= i < j < |xv| ==> xv[i].epoch > xv[j].epoch
        decreases |xv| - i 
    {
        if i == |xv| - 1 then 
            //  Genesis block with slot 0 is justified.
            true
        else 
            //  there should be a justified block at a higher index
            exists j {:induction j} :: i < j < |xv| - 1 && isJustified(j, xv, links, refSet) 
                && superMajorityLink(xv[j], xv[i], links, refSet)
    }

}