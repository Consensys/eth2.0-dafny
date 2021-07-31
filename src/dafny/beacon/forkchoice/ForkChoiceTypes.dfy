/*
 * Copyright 2021 ConsenSys Software Inc.
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

include "../../utils/Eth2Types.dfy"
include "../../utils/NativeTypes.dfy"
include "../BeaconChainTypes.dfy"
include "../attestations/AttestationsTypes.dfy"

/**
 *  Provide datatype for fork choice rule (and LMD-GHOST)
 */
module ForkChoiceTypes {

    import opened Eth2Types
    import opened NativeTypes
    import opened BeaconChainTypes
    import opened AttestationsTypes


     /**
     *  The store (memory) recording the blocks and the states.
     *  
     *  @param  time                    Current time?
     *  @param  genesis_time            Genesis time of the genesis_state. 
     *  @param  justified_checkpoint    Latest epoch boundary block that is justified.
     *  @param  finalised_checkpoint    Latest epoch boundary block that is finalised.
     *  @param  blocks                  The map (dictionary) from hash to blocks.
     *  @param  block_states            The map (dictionary) from hash to block states.
     *
     *  @param  threshold               Not in the store as per eth2.0 specs but
     *                                  used here as the constant numebr of validators.
     *
     *  @param  rcvdAttestations        Attestations received so far (not limited to recent ones).
     *                                  Used for verification.
     *  @note                           From the spec 
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/fork-choice.md#on_block}           
     *  @todo                           It seems that blocks and block_states should have the same
     *                                  keys at any time. This is proved in invariant0.
     */
    datatype Store = Store (
        time: uint64,
        genesis_time: uint64,
        justified_checkpoint : CheckPoint,
        finalised_checkpoint: CheckPoint,
        // best_justified_checkpoint: CheckPoint,
        blocks : map<Root, BeaconBlock>,
        block_states : map<Root, BeaconState>,
        threshold: nat,
        ghost rcvdAttestations : ListOfAttestations //  attestations received so far. Used for verification
        // checkpoint_states: map<CheckPoint, BeaconState>
        // latest_messages: Dict[ValidatorIndex, LatestMessage]
    )

    /**
     *  A well-formed store is a store for which each block
     *  with a slot > 0 has a parent in the store.
     *  Downward closure for the parent relation.
     *
     *  @param  store   A store.
     */
    predicate isClosedUnderParent(store: Store) 
    {
        forall k {:trigger store.blocks[k]}:: k in store.blocks.Keys && store.blocks[k].slot > 0 ==>
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
     *
     *  @param  xr      A non-empty seq of block roots.
     *  @param  store   A store.
     *  @note           There are equivalent possible definitions but this one
     *                  works well for verification.
     *
     *  @example of a chain of size 6.  
     *  xr = [br5, br4, br3, br2, br1, br0] with 
     *  a. store.blocks[br0].slot == 0
     *  b. store.blocks[brk].slot >  store.blocks[brk - 1].slot for k >=1 
     *  xr is a chain if (---> is the descendant relation):
     *  1. br0 ---> br1 ---> br2 ---> br3 ---> br4 ---> br5 and
     *  2. a. and b.
     */
    predicate isChain(xr: seq<Root>, store: Store)  
        decreases xr
    {
        |xr| >= 1
        &&
        (forall i :: 0 <= i < |xr| ==> xr[i] in store.blocks.Keys)
        &&  
        store.blocks[xr[|xr| - 1]].slot == 0 
        && 
        if |xr| == 1 then 
            //  last block with slot 0 is assumed to be a chain.
            store.blocks[xr[0]].slot == 0 
        else 
            && store.blocks[xr[0]].parent_root == xr[1] 
            && store.blocks[xr[0]].slot > store.blocks[xr[1]].slot
            && isChain(xr[1..], store)
    }

    /**
     *  An alternative simpler definition of isChain that should be equivalent to
     *  isChain. However, using it makes the verification of some methods/functions
     *  inconclusive. 
     */
    predicate isChain2(xr: seq<Root>, store: Store)  
        decreases xr
    {
        |xr| >= 1
        &&
        // (forall i :: 0 <= i < |xr| ==> xr[i] in store.blocks.Keys)
        xr[0] in store.blocks.Keys
        &&  
        // store.blocks[xr[|xr| - 1]].slot == 0 
        // && 
        if |xr| == 1 then 
            //  last block with slot 0 is assumed to be a chain.
            // true
            store.blocks[xr[0]].slot == 0 
        else 
            xr[1] in store.blocks.Keys
            && store.blocks[xr[0]].parent_root == xr[1] 
            && store.blocks[xr[0]].slot > store.blocks[xr[1]].slot
            && isChain2(xr[1..], store)
    }

    /**
     *  The ancestors of a block root, as a sequence of block roots.
     *  
     *  @param  br      A hash root of a block that is in the `store`.
     *  @param  store   A store (similar to the view of the validator).
     *  @returns        The ancestors's roots of the block `br` in  `store` with
     *                  `br` first and oldest (genesis) is the last element of the sequence.
     *
     *  @example. br block at slot 134. 
     *  Store ancestors from br given by: br == b0 and then b1, b2, ... b5.
     *  |chainRoots(br, store)| == 6, chainRoots(br, store)[i] == bi
     *  store.blocks[chainRoots(br, store)[5]].slot ==  store.blocks[b5].slot == 0
     *  store.blocks[b5].slot == 0
     *  store.blocks[brk].slot >  store.blocks[brk - 1].slot for k >=1 
     *          |............|............|............|............|............|...
     *  block   b5----------->b4---------->b3---->b2------>b1------->b0 == br     
     *  slot    0             32           63     95       109       134
     */
    function chainRoots(br: Root, store: Store): seq<Root>
        /** The block root must in the store.  */
        requires br in store.blocks.Keys
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        ensures |chainRoots(br, store)| >= 1  

        ensures br in chainRoots(br, store)

        /** Result is a slot-decreasing chain of linked roots the last one is slot 0..  */
        ensures isChain(chainRoots(br, store), store)

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
     *  Transitivity property of chainRoots.
     *  If:
     *      1. br2 in an ancestor of br1
     *      2. br3 is an ancestor of br2
     *  then br3 is an ancestor of br1. 
     *  
     *  @param  br1      A hash root of a block that is in the `store`.
     *  @param  br2      A hash root of a block that is in the `store`.
     *  @param  br3      A hash root of a block that is in the `store`.
     *  @param  store    A store (similar to the view of the validator).
     *
     */
    lemma chainRootsMonotonic(br1: Root, br2: Root, br3: Root, store: Store) 
        /** The block root must in the store.  */
        requires br1 in store.blocks.Keys
        requires br2 in store.blocks.Keys
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        requires br2 in chainRoots(br1, store)
        requires br3 in  chainRoots(br2, store)

        ensures br3 in chainRoots(br1, store)

        decreases height(br1, store)
    {
        var v1 := chainRoots(br1, store);
        if br2 == v1[0] {
            assert(br1 == br2);
        } else {
            var pr1 := store.blocks[br1].parent_root;
            assert(chainRoots(pr1, store) == v1[1..]);
            chainRootsMonotonic(pr1, br2, br3, store);
            assert(br3 in chainRoots(pr1, store));
        }
    }

    /**
     *  The height of a block in the store.
     *
     *  @param  br      A block root.
     *  @param  store   A store.
     *  @returns        The height of the block br.
     */
    function height(br: Root, store: Store): nat 
        /** The block root must in the store.  */
        requires br in store.blocks.Keys
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

         decreases store.blocks[br].slot
    {
        if ( store.blocks[br].slot == 0 ) then
            //  Should be the genesis block.
            0
        else 
            1 + height(store.blocks[br].parent_root, store)
    }
}
