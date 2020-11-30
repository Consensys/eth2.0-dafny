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

// include "../ssz/Constants.dfy"
include "../utils/Eth2Types.dfy"
// include "../utils/NativeTypes.dfy"
include "Attestations.dfy"
include "BeaconChainTypes.dfy"
// include "StateTransition.dfy"
// include "Helpers.dfy"

include "ForkChoiceTypes.dfy"

/**
 * Fork choice rule for the Beacon Chain.
 */
module ForkChoiceHelpers {
    
    // import opened Constants
    import opened Eth2Types
    // import opened NativeTypes
    import opened BeaconChainTypes
    // import opened StateTransition
    // import opened BeaconHelpers
    import opened Attestations
    import opened ForkChoiceTypes

    /**
     *  A supermajority set.
     *  @param  a   A list of attestations.
     *  @param  b   A list of attestations.
     *  @returns    Whether |a| is more than two thirds of |b|.
     *  @note       This predicate is actually stronger than |a| >= (2 |b|) / 3
     *              but this is what is defined in the specs. 
     */
    predicate superMajority(a: seq<PendingAttestation>, b: nat) 
    {
        |a| * 3 >= b * 2 
    }


    /**
     *  The chain defined by a block.
     *  
     *  @param  br      A hash root of a block.
     *  @param  store   A store (similar to the view of the validator).
     *  @returns        Collect the ancestors of the block `br` in  `store`.
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