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
// include "Helpers.dfy"
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
    // import opened BeaconHelpers
    import opened Attestations
    import opened ForkChoiceTypes
    // import opened SeqHelpers
   
    /**
     *  The chain defined by a block.
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
     *  The strict prefix of a chain.
     */
    function strictChain(br: Root, store: Store) : seq<BeaconBlock>
        requires br in store.blocks.Keys
        requires  store.blocks[br].slot > 0
        requires forall k :: k in store.blocks.Keys && store.blocks[k].slot > 0 ==>
            store.blocks[k].parent_root in store.blocks.Keys
            && store.blocks[store.blocks[k].parent_root].slot < store.blocks[k].slot 

        //  Computation always terminates as slot number decreases (well-foundedness).
        decreases store.blocks[br].slot
    {
        chain(store.blocks[br].parent_root, store)
    }


    /**
     *  The epoch boundary block (EBB) at epoch j for chain(B). 
     *  @param  br      A block root.
     *  @param  store   The store.
     *  @param  j       A epoch number.
     */
    // function epochBoundaryBlocks(br: Root, store: Store, j : nat) : Root 
    //     // requires j <= compute_epoch_at_slot() 
    // {
    //     //  get the chain for br in the store
    //     var c := chain(br, store);
    //     br
    // }

    /**
     *  Compute the first epoch boundary block.
     *
     *  @param  xb  A sequence of blocks.
     *  @param  e   An epoch.
     *  @return     The index i of the first block in xb (left to right) with 
     *              slot number less the epoch `e` slot. 
     */
    function computeFirstEBBIndex(xb : seq<BeaconBlock>, e :  nat) : nat
        requires |xb| >= 1
        /** Last block has slot 0. */
        requires xb[|xb| - 1].slot == 0 
        /** Slots of blocks are monotonically decreasing. */
        requires forall i ::  1 <= i < |xb| ==> xb[i - 1].slot > xb[i].slot 

        /** The result is in the range of xb. */
        ensures computeFirstEBBIndex(xb, e) < |xb|
        /** The slot of the result is bounded. */
        ensures xb[computeFirstEBBIndex(xb, e)].slot as nat <= e * SLOTS_PER_EPOCH as nat 
        /** The prefix of xb[..result] has slots >  e * SLOTS_PER_EPOCH. */
        ensures forall j :: 0 <= j < computeFirstEBBIndex(xb, e) ==>
            xb[j].slot as nat > e * SLOTS_PER_EPOCH as nat
        decreases xb 
    {
        if |xb| == 1 then 
            0
        else if xb[0].slot as nat <= e * SLOTS_PER_EPOCH as nat then 
            0
        else 
            1 + computeFirstEBBIndex(xb[1..], e)
    }

    /**
     *  Compute the subsequence of indices of epoch boundary blocks.
     *  @param  xb  A sequence of blocks.
     *  @param  e   An epoch.
     *  @param  k   An index in `xb`.
     */
    function computeEBBs(xb : seq<BeaconBlock>, e :  nat) : seq<nat>
        requires |xb| >= 1
        /** Last block has slot 0. */
        requires xb[|xb| - 1].slot == 0 
        /** Slots of blocks are monotonically decreasing. */
        requires forall i ::  1 <= i < |xb| ==> xb[i - 1].slot > xb[i].slot 

        /** Each epoch has a block associated to. */
        ensures |computeEBBs(xb, e)| == e + 1
        /** The index for each epoch is in the range of xb. */
        ensures forall i :: 0 <= i < e + 1 ==> computeEBBs(xb, e)[i] < |xb|
        /** The sequence returned is in decreasing order. */
        ensures forall i :: 1 <= i < e + 1 ==> 
            xb[computeEBBs(xb, e)[i - 1]].slot >= xb[computeEBBs(xb, e)[i]].slot
        /** The epoch e - i boundary block has a slot less than (e - i) * SLOTS_PER_EPOCH. */
        ensures forall i :: 0 <= i < e + 1 
            ==> xb[computeEBBs(xb, e)[i]].slot as nat <= (e - i) * SLOTS_PER_EPOCH as nat 
        /** The  blocks at index j less than the epoch e - i boundary block have a slot 
            larger than  (e - i) * SLOTS_PER_EPOCH. */
        ensures forall i :: 0 <= i < e + 1 ==> 
            forall j :: 0 <= j < computeEBBs(xb, e)[i] ==>
            xb[j].slot as nat > (e - i) * SLOTS_PER_EPOCH as nat

        decreases e 
    {
        [computeFirstEBBIndex(xb, e)] +
        (
            if e == 0 then 
                []
            else 
                computeEBBs(xb, e - 1)
        )
    }

    /**
     *  Justification definition.
     *  
     *  @param  c   A checkpoint.
     *  @param   
     */
    // predicate isJustified(c: CheckPoint, store: Store, genesisBlockRoot: Root ) 
    // {
    //     if c.epoch == 0 then 
    //         // should be genesis block
    //         c.root ==  genesisBlockRoot
    //     else 
    //         exists b1 :: b1 in strictChain(c.root, store) && isJustified(b1, store, genesisBlockRoot)
    //         // && superMajority()
    // }
}