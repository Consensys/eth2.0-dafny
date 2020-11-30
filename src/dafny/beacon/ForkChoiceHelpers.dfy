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


    function computeEBBs(xb : seq<BeaconBlock>, e :  nat) : seq<BeaconBlock>
        requires |xb| >= 1
        /** Last block has slot 0. */
        requires xb[|xb| - 1].slot == 0 
        // requires forall i ::  1 <= i < |xb| ==> xb[i - 1].slot > xb[i].slot 
        // requires forall i :: 0 <= i < |xb| && xb[i].slot == 0 ==> i == |xb| - 1
        // ensures forall i :: 0 <= i < |xb| 
        ensures |computeEBBs(xb, e)| == e + 1
       
        ensures computeEBBs(xb, e)[e] == xb[|xb| - 1]
        ensures forall i ::  0 <= i < e + 1 ==> 
            computeEBBs(xb, e)[e].slot as nat <= i *  SLOTS_PER_EPOCH as nat

        decreases e, xb
    {
        if e == 0 then 
            [xb[|xb| - 1]]
        else 
            //  not epoch zero
            assert(e >= 1);
            if xb[0].slot as nat <= e * SLOTS_PER_EPOCH as nat then 
                //  found EBB for epoch e
                [xb[0]] + computeEBBs(xb, e - 1)
            else 
                //  current head block slot is too large and e >= 1
                //  this implies that |xb| >= 2
                assert(|xb| >= 2);
                computeEBBs(xb[1..], e)
    }

    /**
     *  The result of computeEBBs for slot j is the block with the largest
     *  slot <= j * SLOTS_PER_EPOCH
     */
    // lemma foo101(xb : seq<BeaconBlock>, e :  nat)
    //     requires |xb| >= 1
    //     /** Last block has slot 0. */
    //     requires xb[|xb| - 1].slot == 0 
    //     ensures 
    // {

    // }


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