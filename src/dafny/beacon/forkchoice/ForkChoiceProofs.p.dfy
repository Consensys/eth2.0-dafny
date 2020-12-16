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
include "ForkChoiceTypes.dfy"
include "ForkChoiceHelpers.dfy"
include "ForkChoiceHelpers.p.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../Helpers.dfy"
include "../BeaconChainTypes.dfy"

/**
 *  Proofs for the ForkChoice properties.  
 */
module ForckChoiceProofs {
    
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
     *  RuleI for slashing. 
     *  A validator cannot vote more than once for a given epoch.
     */
    // predicate ruleI(xa : seq<PendingAttestation>) 
    // {
    //     forall a1, a2 :: a1 in xa && a2 in xa ==>

    // }


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
    lemma lemma4_11_a(br1: Root, br2: Root, store: Store, j: Epoch)
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
            isJustified(0, chbr1, k1, store.attestations) && isJustified(0, chbr2, k2, store.attestations)

        ensures 
            var chbr1 := chainRoots(br1, store);
            var chbr2 := chainRoots(br2 , store);
            //  EBB(br1, j) is k1[0]
            var k1 := computeAllEBBsIndices(chbr1, j, store);
            //  EBB(br1, j) is k1[0]
            var k2 := computeAllEBBsIndices(chbr2, j, store);
            var tgt1 := CheckPoint(0 as Epoch, chbr1[k1[0]]);
            var tgt2 := CheckPoint(0 as Epoch, chbr2[k2[0]]);
            |collectValidatorsIndicesAttestatingForTarget(store.attestations, tgt1) * collectValidatorsIndicesAttestatingForTarget(store.attestations, tgt2)|
            >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1
    {
        var chbr1 : seq<Root> := chainRoots(br1, store); //  chain(br1)
        var chbr2 : seq<Root> := chainRoots(br2, store); //  chain(br2)

        //  compute the indices of EBBs in roots. Because j > 0, |k1| == j + 1 > 1.
        var k1 := computeAllEBBsIndices(chbr1, j, store);
        //  EBB(br1, j) is k1[0]
        var k2 := computeAllEBBsIndices(chbr2, j, store);
        //  EBB(br2, j) is k2[0]

        if (isJustified(0, chbr1, k1, store.attestations) && isJustified(0, chbr2, k2, store.attestations)) {
            justifiedMustHaveTwoThirdIncoming(0, chbr1, k1, store.attestations);
            var tgt1 :=  CheckPoint(0 as Epoch, chbr1[k1[0]]);
            var attForTgt1 := collectValidatorsIndicesAttestatingForTarget(store.attestations, tgt1);
            assert(|attForTgt1| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);
            justifiedMustHaveTwoThirdIncoming(0, chbr2, k2, store.attestations);
            var tgt2 := CheckPoint(0 as Epoch, chbr2[k2[0]]);
            var attForTgt2 := collectValidatorsIndicesAttestatingForTarget(store.attestations, tgt2);
            assert(|attForTgt2| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);

            supermajorityForSameEpoch(store.attestations, tgt1, tgt2);
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
    lemma supermajorityForSameEpoch(xa : seq<PendingAttestation>, tgt1: CheckPoint, tgt2: CheckPoint) 
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

}