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

// include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "../utils/SetHelpers.dfy"
// include "../utils/Helpers.dfy"
include "../ssz/Constants.dfy"
include "ForkChoiceTypes.dfy"
include "ForkChoiceHelpers.dfy"
// include "Validators.dfy"
include "Attestations.dfy"
include "Helpers.dfy"

/**
 *  Proofs for the ForkChoice properties.  
 */
module ForckChoiceProofs {
    
    //  Import some constants, types and beacon chain helpers.
    // import opened NativeTypes
    import opened Eth2Types
    import opened SetHelpers
    import opened Constants
    import opened ForkChoiceTypes
    import opened ForkChoiceHelpers
    // import opened Validators
    import opened Attestations
    import opened BeaconHelpers

    /**
     *  RuleI for slashing. 
     *  A validator cannot vote more than once for a given epoch.
     */
    // predicate ruleI(xa : seq<PendingAttestation>) 
    // {
    //     forall a1, a2 :: a1 in xa && a2 in xa ==>

    // }

    /**
     *  
     */
    // function collectAttestationsForEpoch(xa: seq<PendingAttestation>, e : Epoch) : nat 
    //     ensures collectAttestationsForEpoch(xa, e) <= |xa|
    // {
    //     if |xa| == 0 then 
    //         0
    //     else 
    //         if compute_epoch_at_slot(xa[0].data.slot) == e then 
    //             1 + collectAttestationsForEpoch(xa[1..], e)
    //         else 
    //             collectAttestationsForEpoch(xa[1..], e)                  
    // }


    /**
     *  No two justified checkpoints at the same epoch.
     */
    lemma lemma4_11(br1: Root, br2: Root, store: Store, j: nat)
        /** The block root must be from an accepted block, i.e. in the store. */
        requires br1 in store.blocks.Keys
        requires br2 in store.blocks.Keys

        // requires 0 <= j < 

        // re
        // requires b1 != br2 
        /** The store is well-formed, each block with slot !=0 has a parent
            which is itself in the store. */
        requires forall k :: k in store.blocks.Keys && store.blocks[k].slot > 0 ==>
            store.blocks[k].parent_root in store.blocks.Keys
            && store.blocks[store.blocks[k].parent_root].slot < store.blocks[k].slot 
        ensures true
        ensures     var roots1 := chainRoots(br1, store); //  chain(br1)
                    var roots2 := chainRoots(br2, store); //  chain(br2)
                    var sl1 := store.blocks[roots1[0]].slot;  //  slot of br1 as a block
                    var sl2 := store.blocks[roots2[0]].slot;  //  slot of br2 as a block
                    //  compute the indices of EBBs in roots.
                    var ebbsIndices1 := computeAllEBBs(roots1, compute_epoch_at_slot(sl1), store);
                    var ebbsIndices2 := computeAllEBBs(roots2, compute_epoch_at_slot(sl2), store);
                    //  given 0 <= j < compute_epoch_at_slot(sl), (roots[j],j) is the EBB at
                    //  epoch(B) - j
                    true

    {
        // assert();
    }

    /**
     *  Assume two chains
     */
    lemma lemma4_11_a(br1: Root, br2: Root, store: Store, j: Epoch, links : seq<PendingAttestation>)
         /** The block roots must be from accepted blocks, i.e. in the store. */
        requires br1 in store.blocks.Keys
        requires br2 in store.blocks.Keys

        /** Epoch is not zero. */
        requires j > 0 

        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)

        // requires br1 == br2 

        requires 
            var chbr1 := chainRoots(br1, store);
            var chbr2 := chainRoots(br2 , store);
            //  EBB(br1, j) is k1[0]
            var k1 := computeAllEBBs(chbr1, j, store);
            //  EBB(br1, j) is k1[0]
            var k2 := computeAllEBBs(chbr2, j, store);
            isJustified(0, chbr1, k1, links) && isJustified(0, chbr2, k2, links)

        ensures 
            var chbr1 := chainRoots(br1, store);
            var chbr2 := chainRoots(br2 , store);
            //  EBB(br1, j) is k1[0]
            var k1 := computeAllEBBs(chbr1, j, store);
            //  EBB(br1, j) is k1[0]
            var k2 := computeAllEBBs(chbr2, j, store);
            var tgt1 := CheckPoint(0 as Epoch, chbr1[k1[0]]);
            var tgt2 := CheckPoint(0 as Epoch, chbr2[k2[0]]);
            |collectAttestationsForTarget(links, tgt1) * collectAttestationsForTarget(links, tgt2)|
            >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1
    {
        var chbr1 : seq<Root> := chainRoots(br1, store); //  chain(br1)
        var chbr2 : seq<Root> := chainRoots(br2, store); //  chain(br2)

        //  compute the indices of EBBs in roots. Because j > 0, |k1| == j + 1 > 1.
        var k1 := computeAllEBBs(chbr1, j, store);
        //  EBB(br1, j) is k1[0]
        var k2 := computeAllEBBs(chbr2, j, store);
        //  EBB(br2, j) is k2[0]

        if (isJustified(0, chbr1, k1, links) && isJustified(0, chbr2, k2, links)) {
            justifiedMustHaveTwoThirdIncoming(0, chbr1, k1, links);
            var tgt1 :=  CheckPoint(0 as Epoch, chbr1[k1[0]]);
            var attForTgt1 := collectAttestationsForTarget(links, tgt1);
            assert(|attForTgt1| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);
            justifiedMustHaveTwoThirdIncoming(0, chbr2, k2, links);
            var tgt2 := CheckPoint(0 as Epoch, chbr2[k2[0]]);
            var attForTgt2 := collectAttestationsForTarget(links, tgt2);
            assert(|attForTgt2| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);

            foo107(links, tgt1, tgt2);
            //  If the two blocks are the same, more than 2/3 threshold is 
            //  reached.
            if (br1 == br2) {
                assert((attForTgt1 <= attForTgt2) && (attForTgt2 <= attForTgt1));
                assert(attForTgt1 * attForTgt2 == attForTgt1);
                assert(|attForTgt1 * attForTgt2| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);
            }
            assert(|attForTgt1 * attForTgt2| >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1);
        }
        

        //  what we want
        // assert(cp1 != cp2);
    }

    lemma {:induction k} foo102(x : set<nat>, k : nat) 
        requires x == set x: nat | 0 <= x < k :: x
        ensures |x| == k
    {
        if k == 0 {
            //  Thanks Dafny
        } else {
            foo102(x - {k - 1}, k - 1);
        }
    }

    /**
     *  If two aggregation bits have nore than 2/3 of  MAX_VALIDATORS_PER_COMMITTEE
     *  set to true, then the bitwise intersection of `xa` and `xb` has more than 
     *  1/3 values et to true.
     *
     *  @param  xa  A vector of bools.
     *  @param  xb  A vector of bools.
     */
    lemma foo101(xa : AggregationBits, xb: AggregationBits) 
        // requires |xa| == |xb|
        requires |trueBitsCount(xa)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1  
        requires |trueBitsCount(xb)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1 
        ensures |trueBitsCount(xa) * trueBitsCount(xb)| >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1
    {
        var k := set x: nat | 0 <= x < MAX_VALIDATORS_PER_COMMITTEE :: x;
        foo102(k, MAX_VALIDATORS_PER_COMMITTEE);
        assert(|k| == MAX_VALIDATORS_PER_COMMITTEE);
        pigeonHolePrinciple(trueBitsCount(xa), trueBitsCount(xb), k);
    }

    lemma foo107(xa : seq<PendingAttestation>, tgt1: CheckPoint, tgt2: CheckPoint) 
        requires tgt1.epoch == tgt2.epoch 
        requires |collectAttestationsForTarget(xa, tgt1)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1  
        requires |collectAttestationsForTarget(xa, tgt2)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1  
        ensures |collectAttestationsForTarget(xa, tgt1) * collectAttestationsForTarget(xa, tgt2)| >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1
    {
        var k := set x: nat | 0 <= x < MAX_VALIDATORS_PER_COMMITTEE :: x;
        foo102(k, MAX_VALIDATORS_PER_COMMITTEE);
        assert(|k| == MAX_VALIDATORS_PER_COMMITTEE);
        pigeonHolePrinciple(collectAttestationsForTarget(xa, tgt1), collectAttestationsForTarget(xa, tgt2), k);
    }

    // lemma pigeonHolePrincipleForSeq(x: seq<int>, y : seq<int>, z : seq<int>) 
    //     requires forall i, j :: 0 <= i < j < |z| ==> z[i] != z[j]
    //     requires forall i, j :: 0 <= i < j < |x| ==> x[i] != x[j]
    //     requires forall i, j :: 0 <= i < j < |y| ==> y[i] != y[j]
    //     requires |x| >= 2 * |z| / 3 + 1   //    or equivalently 2 * |z| < 3 * |x| 
    //     requires |y| >= 2 * |z| / 3 + 1   //    or equivalently 2 * |z| < 3 * |y|
    //     ensures |x * y| >= |z| / 3 + 1    //    or equivalently 3 * |x * y| < |z| 

    // {
    //     pigeonHolePrinciple(x, y, z);   
    // }

   /**
    *  If two finite sets x and y are included in another one z and
    *  have more than 2/3(|z|) elements, then their intersection has more
    *  then |z|/3 elements.
    */
    lemma pigeonHolePrinciple(x: set<int>, y : set<int>, z : set<int>)
        requires  x <= z 
        requires y <= z
        requires |x| >= 2 * |z| / 3 + 1   //    or equivalently 2 * |z| < 3 * |x| 
        requires |y| >= 2 * |z| / 3 + 1   //    or equivalently 2 * |z| < 3 * |y|
        ensures |x * y| >= |z| / 3 + 1    //    or equivalently 3 * |x * y| < |z| 
    {
        //  Proof of alternative assumption
        // assert(|x| >= 2 * |z| / 3 + 1 <==> 2 * |z| < 3 * |x|);
        // assert(|y| >= 2 * |z| / 3 + 1 <==> 2 * |z| < 3 * |y|);
        //  Proof by contradiction
        if |x * y| < |z| / 3 + 1 {
            //  size of union is sum of sizes minus size of intersection.
            calc == {
                |x + y|;
                |x| + |y| - |x * y|;
            }
            cardIsMonotonic(x + y, z);
        } 
        //  proof of alternative conclusion
        // assert(3 * |x * y| > |z| <==> |x * y| >= |z| / 3 + 1 );
    } 

   /**
    *  If a finite set x is included in a finite set y, then
    *  card(x) <= card(y).
    *
    *  @param  T   A type.
    *  @param  x   A finite set.
    *  @param  y   A finite set.
    *  @returns    A proof that x <= y implies card(x) <= card(y)
    *              in other terms, card(_) is monotonic.
    */
    // lemma cardIsMonotonic<T>(x : set<T>, y : set<T>) 
    //     requires x <= y 
    //     ensures |x| <= |y|
    //     decreases y 
    // {
    //     if |y| == 0 {
    //         //  Thanks Dafny
    //     } else {
    //         //  |y| >= 1, get an element in y
    //         var e :| e in y;
    //         var y' := y - { e };
    //         //  Split recursion according to whether e in x or not
    //         cardIsMonotonic(if e in x then x - {e} else x, y');
    //     }
    // }
}