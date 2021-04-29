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

include "../../utils/Eth2Types.dfy"
include "../../utils/SetHelpers.dfy"
include "../../ssz/Constants.dfy"
include "../forkchoice/ForkChoiceTypes.dfy"
include "../forkchoice/ForkChoiceHelpers.dfy"
include "../forkchoice/ForkChoiceHelpers.p.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../Helpers.dfy"
include "../BeaconChainTypes.dfy"
 
/**
 *  Proofs for the ForkChoice properties.  
 */
module GasperProofs {
    
    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened SetHelpers
    import opened Constants
    import opened ForkChoiceTypes
    import opened ForkChoiceHelpers
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened BeaconHelpers
    import opened BeaconChainTypes
    import opened ForkChoiceHelpersProofs

    /**
     *  Assume two chains from br1 and br2.
     *  There cannot be two justified checkpoints in the two chains
     *  at the same epoch without breaking 1/3-slashability.
     *
     *  @param  br1     A block root.
     *  @param  br2     A block root.
     *  @param  store   A store.
     *  @param  j       An epoch.
     *  @param  
     */
    lemma {:induction false} lemma4_11_a(br1: Root, br2: Root, store: Store, j: Epoch)
        /** The block roots must be from accepted blocks, i.e. in the store. */
        requires br1 in store.blocks.Keys
        requires br2 in store.blocks.Keys
        /** Epoch is not zero. */
        requires j > 0 
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        /** both checkpoints at epoch j are justified. */
        requires 
            var chbr1 := chainRoots(br1, store);
            var chbr2 := chainRoots(br2 , store);
            //  EBB(br1, j) is k1[0]
            var k1 := computeAllEBBsIndices(chbr1, j, store);
            //  EBB(br1, j) is k1[0]
            var k2 := computeAllEBBsIndices(chbr2, j, store);
            isJustified(0, chbr1, k1, store.rcvdAttestations) && isJustified(0, chbr2, k2, store.rcvdAttestations)

        ensures 
            var chbr1 := chainRoots(br1, store);
            var chbr2 := chainRoots(br2 , store);
            //  EBB(br1, j) is k1[0]
            var k1 := computeAllEBBsIndices(chbr1, j, store);
            //  EBB(br1, j) is k1[0]
            var k2 := computeAllEBBsIndices(chbr2, j, store);
            var tgt1 := CheckPoint(0 as Epoch, chbr1[k1[0]]);
            var tgt2 := CheckPoint(0 as Epoch, chbr2[k2[0]]);
            |collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt1) * collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt2)|
            >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1
    {
        var chbr1 : seq<Root> := chainRoots(br1, store); //  chain(br1)
        var chbr2 : seq<Root> := chainRoots(br2, store); //  chain(br2)

        //  compute the indices of EBBs in roots. Because j > 0, |k1| == j + 1 > 1.
        var k1 := computeAllEBBsIndices(chbr1, j, store);
        //  EBB(br1, j) is k1[0]
        var k2 := computeAllEBBsIndices(chbr2, j, store);
        //  EBB(br2, j) is k2[0]

        if (isJustified(0, chbr1, k1, store.rcvdAttestations) && isJustified(0, chbr2, k2, store.rcvdAttestations)) {
            justifiedMustHaveTwoThirdIncoming(0, chbr1, k1, store.rcvdAttestations);
            var tgt1 :=  CheckPoint(0 as Epoch, chbr1[k1[0]]);
            var attForTgt1 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt1);
            assert(|attForTgt1| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);
            justifiedMustHaveTwoThirdIncoming(0, chbr2, k2, store.rcvdAttestations);
            var tgt2 := CheckPoint(0 as Epoch, chbr2[k2[0]]);
            var attForTgt2 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt2);
            assert(|attForTgt2| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);

            superMajorityForSameEpoch(store.rcvdAttestations, tgt1, tgt2);
            //  If the two blocks are the same, more than 2/3 threshold is 
            //  reached.
            if (br1 == br2) {
                assert((attForTgt1 <= attForTgt2) && (attForTgt2 <= attForTgt1));
                interSmallest(attForTgt1, attForTgt2);
                assert(attForTgt1 * attForTgt2 == attForTgt1 == attForTgt2);
                assert(|attForTgt1 * attForTgt2| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);
            } else {
                assert(|attForTgt1 * attForTgt2| >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1);
            }
        }
    }

    /**
     *  Two checkpoints with the same epoch.
     *  Assume they both have A1 and A2 attestations more than 2/3 of total incoming attestations. 
     *  Then the set of validators attesting for both of them has more than 1/3 total.
     *
     *  @param  xa      A list of attestations.
     *  @param  tgt1    A checkpoint.
     *  @param  tgt2    A checkpoint.
     */
    lemma {:induction false} superMajorityForSameEpoch(xa : seq<PendingAttestation>, tgt1: CheckPoint, tgt2: CheckPoint) 
        requires tgt1.epoch == tgt2.epoch 
        requires |collectValidatorsIndicesAttestatingForTarget(xa, tgt1)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1  
        requires |collectValidatorsIndicesAttestatingForTarget(xa, tgt2)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1  

        ensures |collectValidatorsIndicesAttestatingForTarget(xa, tgt1) * collectValidatorsIndicesAttestatingForTarget(xa, tgt2)| >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1
    {
        var k := set x: nat | 0 <= x < MAX_VALIDATORS_PER_COMMITTEE :: x;
        successiveNatSetCardBound(k, MAX_VALIDATORS_PER_COMMITTEE);
        assert(|k| == MAX_VALIDATORS_PER_COMMITTEE);
        pigeonHolePrinciple(collectValidatorsIndicesAttestatingForTarget(xa, tgt1), collectValidatorsIndicesAttestatingForTarget(xa, tgt2), k);
    }

    /**
     *  Canonical chain property.
     *  Assume fixed set of validators.
     *  
     *  If two blocks are finalized and neither is an ancestor of the other, 
     *  then validators having at least 1/3 of the total stake must have violated 
     *  one of the the slashing conditions: 
     *  
     */
    // lemma atMostOneCanonicalChain(store: Store) 
    //     ensures forall r :: r in store.blocks.Keys && 

    // {
    //     assume(forall r :: r in store.blocks.Keys ==> true);
    // }

    /**
     *  In a view G, if (BF, f) in F(G) and (BJ, j) in J(G) with j > f, then BF
     *  must be an ancestor of BJ , or the blockchain is (1/3)-slashable – 
     *  specifically, there must exist 2 subsets V1, V2 of V, each with total stake at 
     *  least 2N/3, such that their intersection all violate slashing condition (S1) 
     *  or all violate slashing condition (S2).
     *
     *  Proof for 1-finalisation.
     *
     *  Assume (bf,f) 1-finalised and (bj, j) justified and not a descendant of (bf)
     *  
     *  epoch   0                         f              f+1                             
     *          |............        .....|...................|   
     *  blocks                        bf --- ..... ------> b1 ------- .... --> bh1
     *  V1                              (bf,f) ====J====> (b1, f + 1) 
     *  epoch                 l                                    j        
     *                        |.....                           ....|............
     *  blocks             bl --- ..... ------ .... ----> bj --- ..... -----> bh2
     *  V2                  (bl,l) =========== J ============>  (bj,j) 
     *  
     *  
     *  Assume (bj, j) is such that j is the smallest epoch after f such (bj, j) in J(G).
     *  Note that if j == f, lemma4_11 applies.
     *  The same reasoning applies to l: l < f or l > f as otherwise lemma4_11 applies to
     *  l, f.
     *  As we assume that j is the first/smallest epoch after f such that (bj,j) in J(G), 
     *  l cannot be > f. So l < f.
     *  Also j > f + 1 as otherwise lemma4_11 applies.
     *  Overall: l < f < f + 1 < j. (Fact1)
     *
     *  Every attestation a by a validator in V2 is well-formed and such that: 
     *  - aep(LJ(a)) == l and a.ep == j  (Fact2)
     *  Every attestation b by a validator in V1 is well-formed and such that:
     *  - aep(LJ(b)) == f and b.ep == f + 1 (Fact3)
     *
     *  Overall combining facts 1, 2, 3: for any validator in V1 /\ V2 that made two 
     *  attestation a (to b1) and b (to bj), we have
     *      l          <       f    <     f + 1  <   j
     *      aep(LJ(a)) < aep(LJ(b)) <     b.ep   <   a.ep 
     *  which violates S2 (no validator can make nested attestations).
     *  
     *   
     */
    lemma {:induction false} lemma5_1(bh1: Root, bh2: Root, store: Store, j: Epoch, f: Epoch)
        /** The block roots must be from accepted blocks, i.e. in the store. */
        requires bh1 in store.blocks.Keys
        requires bh2 in store.blocks.Keys

        /** The epochs j and f are before the heads slots. */
        requires f as nat + 1 < 0x10000000000000000
        requires compute_epoch_at_slot(store.blocks[bh1].slot) >= f + 1
        requires compute_epoch_at_slot(store.blocks[bh2].slot) >= j 

        // requires 0 <= j < compute_epoch_at_slot(store.blocks[br].slot)   


        /** Epoch is not zero ? */
        requires j > f >= 0 
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

        /** Checkpoint at epoch f is 1-finalised. */
        requires 
            var chbh1 := chainRoots(bh1, store);
            //  Compute the EBBs indices from epoch f + 1
            var k1 := computeAllEBBsIndices(chbh1, f + 1, store);
            //  EBB(bh1, f + 1) is k1[0], EBB(bh1, f) is k1[1]
            isOneFinalised(1, chbh1, k1, store.rcvdAttestations) 

        /** Checkpoint at epoch j is justified. */
        requires isJustifiedInStore(bh2, store, j)
            // var chbh2 := chainRoots(bh2 , store);
            // //  Compute the EBBs indices from epoch j
            // var k2 := computeAllEBBsIndices(chbh2, j, store);
            // //  The EBB at j, EBB(chbh2, j) is (k2[0], j)
            // //  It must be justified, and there is a previous justified checkpoint l 
            // //  that justifies it.
            // isJustified(0, chbh2, k2, store.rcvdAttestations) && 
            //     exists l :: 0 < l < |k2| && isJustified(l, chbh2, k2, store.rcvdAttestations)

        ensures 
            // var chbh1 := chainRoots(bh1, store);
            // var chbh2 := chainRoots(bh2 , store);
            // //  EBB(bh1, j) is k1[0]
            // var k1 := computeAllEBBsIndices(chbh1, j, store);
            // //  EBB(bh1, j) is k1[0]
            // var k2 := computeAllEBBsIndices(chbh2, j, store);
            // var tgt1 := CheckPoint(0 as Epoch, chbh1[k1[0]]);
            // var tgt2 := CheckPoint(0 as Epoch, chbh2[k2[0]]);
            // |collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt1) * collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt2)|
            // >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1
            true
    {
        var chbh1 := chainRoots(bh1, store);
        //  Compute the EBBs indices from epoch f + 1
        var k1 := computeAllEBBsIndices(chbh1, f + 1, store);
        //  EBB(bh1, f + 1) is k1[0], EBB(bh1, f) is k1[1]
        // assert(isOneFinalised(1, chbh1, k1, store.rcvdAttestations));
        // assert(isJustified(0, chbh1, k1, store.rcvdAttestations));

        // var chbh2 := chainRoots(bh2 , store);
        // //  Compute the EBBs indices from epoch j
        // var k2 := computeAllEBBsIndices(chbh2, j, store);
        // //  The EBB at j, EBB(chbh2, j) is (k2[0], j)
        // assert(isJustified(0, chbh2, k2, store.rcvdAttestations));
        // assert(exists l :: 0 < l < |k2| && isJustified(l, chbh2, k2, store.rcvdAttestations));
        // var l :| 0 < l < |k2| && isJustified(l, chbh2, k2, store.rcvdAttestations);

        //  proof that j == f not OK
        // if j == f {
        //     lemma4_11_a(chbh1[k1[0]], chbh2[k2[0]], store, j);
        // } else {

        // }
    }

    /**
     *
     *  @param  br      A block root (head of the chain).
     *  @param  store   A store.
     *  @param  j       An epoch.
     *  @returns        Whether checkpoint at epoch j is justified in store.
     */
    predicate isJustifiedInStore(br: Root, store: Store, j: Epoch)
        requires br in store.blocks.Keys
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

        /** Epoch is smaller than epoch of head block root. */
        requires 0 <= j <= compute_epoch_at_slot(store.blocks[br].slot)   
    {   
        //  compute the anscestors of br
        var chRoots := chainRoots(br , store);
        //  Compute the EBBs indices (backwards) from epoch j
        var k2 := computeAllEBBsIndices(chRoots, j, store);
        //  The EBB at epoch j is (k2[0], j). Check whether epoch j - 0 is justified in store.
        isJustified(0, chRoots, k2, store.rcvdAttestations)
    }

    /**
     *
     *  @param  br      A block root (head of the chain).
     *  @param  store   A store.
     *  @param  j       An epoch.
     *  @returns        Whether checkpoint at epoch j is one-finalised in store.
     */
    predicate isOneFinalisedInStore(br: Root, store: Store, j: Epoch)
        requires br in store.blocks.Keys
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)    //     /** Epoch is smaller than epoch of head block root. */
        requires 0 <= j as nat + 1 < compute_epoch_at_slot(store.blocks[br].slot) as nat 
    {
        var chRoots := chainRoots(br, store);
        //  Compute the EBBs indices from epoch j + 1
        var k1 := computeAllEBBsIndices(chRoots, j + 1, store);
        //  EBB(br, j + 1) is k1[0] and EBB(br, j) is k1[1]
        isOneFinalised(1, chRoots, k1, store.rcvdAttestations) 
    }


    /**
     *  Rule I (Gasper slashing conditions).
     */
    predicate ruleI(s: Store, links: ListOfAttestations) 
    {
        true
    }

    /**
     *  Rule II (Gasper slashing conditions).
     */
    predicate ruleII(s: Store, links: ListOfAttestations) 
    {
        true
    }


    /**
     *  A list of links is valid if all the attestations in links
     *  are valid.
     *  
     *  @param  store   A store.
     *  @param  links   The list of attestations received, from most recent
     *                  first. 
     */
    predicate isValidListOfAttestations(store: Store, links: ListOfAttestations) 
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)
        /** The head block in `a` is in the store. */
        requires forall k :: k in links ==> k.data.beacon_block_root in store.blocks.Keys
        requires forall k :: k in links ==> k.data.beacon_block_root in store.block_states.Keys

        decreases links
    {
        if |links| == 0 then
            true
        else  
            isValidPendingAttestation(links[0], store, links[1..]) 
            &&
            isValidListOfAttestations(store, links[1..])
    }

    /**
     *  All the attestations in the store received so far are valid.
     *  @param  store   A store.
     */
    predicate allAttestationsValidInStore(store: Store) 
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)
        
        /** The head block in each `a` is in the store. */
        requires forall k :: k in store.rcvdAttestations ==> k.data.beacon_block_root in store.blocks.Keys
        requires forall k :: k in store.rcvdAttestations ==> k.data.beacon_block_root in store.block_states.Keys
    {
        isValidListOfAttestations(store, store.rcvdAttestations)
    }

}