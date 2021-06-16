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
include "../../utils/NativeTypes.dfy"
include "../../utils/SetHelpers.dfy"
include "../../ssz/Constants.dfy"
include "../forkchoice/ForkChoiceTypes.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../Helpers.dfy"
include "../BeaconChainTypes.dfy"
include "./GasperHelpers.dfy"
 
/**
 *  Proofs for the ForkChoice properties.  
 */
module GasperProofs {
    
    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened NativeTypes
    import opened SetHelpers
    import opened Constants
    import opened ForkChoiceTypes
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened BeaconHelpers
    import opened BeaconChainTypes
    import opened GasperHelpers

    /**
     *  Assume two chains from br1 and br2.
     *  There cannot be two justified checkpoints in the two chains
     *  at the same epoch without breaking 1/3-slashability.
     *
     *  @param  br1     A block root.
     *  @param  br2     A block root.
     *  @param  store   A store.
     *  @param  j       An epoch.
     *  @note           Change the MAX_VALIDATORS_PER_COMMITTEE to another constant
     *                  which is the size of the set of validators. uint64 for validator
     *                  indices. should be the VALIDATOR_SET.
     *                  Define the validator set size. 
     */
    lemma {:induction false} lemma4_11_a(br1: Root, br2: Root, store: Store, j: Epoch)
        /** The block roots must be from accepted blocks, i.e. in the store. */
        requires br1 in store.blocks.Keys
        requires br2 in store.blocks.Keys
        /** Two distinct block roots.  */
        // requires br1 != br2 
        /** Epoch is not zero. */
        requires j > 0 
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        /** In br1/2 ancestors, checkpoints at epoch j are both justified. */
        requires 
            isJustifiedEpochFromRoot(br1, j, store, store.rcvdAttestations) 
            && isJustifiedEpochFromRoot(br2, j, store, store.rcvdAttestations)

        ensures     //  PostC 1
            var k1 := computeAllEBBsFromRoot(br1, j, store);
            //  EBB(br1, j) is k1[0]
            var k2 := computeAllEBBsFromRoot(br2, j, store);
            //  EBB(br2, j) is k2[0]
            var tgt1 := CheckPoint(j as Epoch, k1[0]);
            var tgt2 := CheckPoint(j as Epoch, k2[0]); 
            //  Set of indices of validators attesting for tgt1 and tgt2 is bounded
            //  from below
            |collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt1) * collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt2)|
            >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1

        //  every validator in the intersection violates ruleI
        ensures     //  PostC 2
            var k1 := computeAllEBBsFromRoot(br1, j, store);
            //  EBB(br1, j) is k1[0]
            var k2 := computeAllEBBsFromRoot(br2, j, store);
            //  EBB(br2, j) is k2[0]
            var tgt1 := CheckPoint(j as Epoch, k1[0]);
            var tgt2 := CheckPoint(j as Epoch, k2[0]); 
            //  Every validator in i1 * i2 violates ruleI
            var i1 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt1); 
            var i2 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt2); 
            tgt1 != tgt2 ==> 
                forall i :: i in i1 * i2 ==> validatorViolatesRuleI(store.rcvdAttestations, i as ValidatorIndex)
    {
        //  chain of roots from br1 and br2
        var cr1 := computeAllEBBsFromRoot(br1, j, store);
        var cr2 := computeAllEBBsFromRoot(br2, j, store);

        //  Checkpoints at epoch j
        var tgt1 :=  CheckPoint(j, cr1[0]);
        var tgt2 := CheckPoint(j, cr2[0]);

        //  Attestations for tgt1 ands tgt2
        var attForTgt1 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt1);
        var attForTgt2 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt2);

        //  PostC 1: Lower bound for attestations to a justified checkpoint
        justifiedMustHaveTwoThirdIncoming(br1, j, store, store.rcvdAttestations);
        justifiedMustHaveTwoThirdIncoming(br2, j, store, store.rcvdAttestations);
        assert(|attForTgt1| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);
        assert(|attForTgt2| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1);

        //  Lower bound for intersection of set of attesters
        superMajorityForSameEpoch(store.rcvdAttestations, tgt1, tgt2);

        //  PostC 2
        if tgt1 != tgt2 {
            forall (i | i in attForTgt1 * attForTgt2) 
                ensures validatorViolatesRuleI(store.rcvdAttestations, i as ValidatorIndex)
                {
                    var a1 : PendingAttestation :| a1.data.target == tgt1 && a1.aggregation_bits[i];
                    var a2 : PendingAttestation :| a2.data.target == tgt2 && a2.aggregation_bits[i];
                    // assert(a1 in store.rcvdAttestations && a2 in store.rcvdAttestations);
                    // assert(validatorViolatesRuleIv2(a1, a2, store.rcvdAttestations, i as ValidatorIndex));
                    assert(validatorViolatesRuleI(store.rcvdAttestations, i as ValidatorIndex));
                }
        }
    }

    lemma lemma4_11v2(bh1: Root, bh2: Root, cp1: CheckPoint, cp2: CheckPoint, store: Store) 
        /** The block roots must be from accepted blocks, i.e. in the store. */
        requires bh1 in store.blocks.Keys
        requires bh2 in store.blocks.Keys

        /** The block roots of the checkpoints must be from accepted blocks, i.e. in the store. */
        requires cp1.root in store.blocks.Keys
        requires cp2.root in store.blocks.Keys
        
        /** The checkpoints are distinct but have same epoch. */
        requires cp1.epoch == cp2.epoch 
        requires cp1.root != cp2.root 

        /** The store is well-formed. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        /** The checkpoints are both justified. */
        requires 
            && isJustifiedCheckPointFromRoot(bh1, cp1, store, store.rcvdAttestations)
            && isJustifiedCheckPointFromRoot(bh2, cp2, store, store.rcvdAttestations)
    
        /** Each validator that attested for cp1 and cp2 violates rule I. */
        ensures 
            var i1 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp1); 
            var i2 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp2); 
            forall i :: i in i1 * i2 ==> validatorViolatesRuleI(store.rcvdAttestations, i as ValidatorIndex)
    {
        //  Attestations for tgt1 ands tgt2
        var attForTgt1 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp1);
        var attForTgt2 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp2);

        //  Proof that each validator that attested for cp1 and cp2 violates rule I
        forall (i | i in attForTgt1 * attForTgt2) 
            ensures validatorViolatesRuleI(store.rcvdAttestations, i as ValidatorIndex)
        {
            //  Thanks Dafny
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
     *  In a view G, if (Bf, f) in F(G) and (Bj, j) in J(G) with j > f, then Bf
     *  must be an ancestor of Bj , or the blockchain is (1/3)-slashable – 
     *  specifically, there must exist 2 subsets V1, V2 of V, each with total stake at 
     *  least 2N/3, such that their intersection all violate slashing condition (S1) 
     *  or all violate slashing condition (S2).
     *
     *  Proof for 1-finalisation.
     *
     *  Assume (bf,f) 1-finalised and (bj, j) justified and bf not a descendant of bf.
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
     *      aep(LJ(a)) < aep(LJ(b)) <     b.epoch   <   a.epoch 
     *  which violates S2 (no validator can make nested attestations).
     *  
     *   
     */
    lemma {:induction false} lemma5_1(bh1: Root, bh2: Root, store: Store, j: Epoch, f: Epoch)
        /** The block roots must be from accepted blocks, i.e. blocks in the store. */
        requires bh1 in store.blocks.Keys
        requires bh2 in store.blocks.Keys

        /** The epochs j and f are before the heads' slots. */
        requires f as nat + 1 <= MAX_UINT64
        requires compute_epoch_at_slot(store.blocks[bh1].slot) >= f + 1
        requires compute_epoch_at_slot(store.blocks[bh2].slot) >= j 

        // requires 0 <= j < compute_epoch_at_slot(store.blocks[br].slot)   

        //  The two blocks are not equal.
        requires bh1 != bh2 

        /** Epoch is not zero */
        requires j >= f > 0 
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

        /** Checkpoint at epoch f is 1-finalised. */
        requires 
            // var chbh1 := chainRoots(bh1, store);
            //  Compute the EBBs indices from epoch f + 1
            // var k1 := computeAllEBBsIndices(chbh1, f + 1, store);
            //  EBB(bh1, f + 1) is k1[0], EBB(bh1, f) is k1[1]
            isOneFinalisedFromRoot(bh1, f, store, store.rcvdAttestations) 

        /** Checkpoint at epoch j is justified. */
        requires isJustifiedEpochFromRoot(bh2, j, store, store.rcvdAttestations)

        ensures 
            // should be: !RuleI or !ruleII

        //     // var chbh1 := chainRoots(bh1, store);
        //     // var chbh2 := chainRoots(bh2 , store);
        //     //  EBB(bh1, j) is k1[0]
        //     var k1 := computeAllEBBsFromRoot(bh1, f, store);
        //     //  EBB(bh1, j) is k1[0]
        //     var k2 := computeAllEBBsFromRoot(bh2, j, store);
        //     var tgt1 := CheckPoint(f as Epoch, k1[0]);
        //     var tgt2 := CheckPoint(j as Epoch, k2[0]);
        //     // true
        //     |collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt1) * collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt2)|
        //     >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1
            true

        //  Case 1: j == f, covered by lemma 4.
        ensures j == f ==> 
            var k1 := computeAllEBBsFromRoot(bh1, j, store);
            //  EBB(br1, j) is k1[0]
            var k2 := computeAllEBBsFromRoot(bh2, j, store);
            //  EBB(br2, j) is k2[0]
            var tgt1 := CheckPoint(j as Epoch, k1[0]);
            var tgt2 := CheckPoint(j as Epoch, k2[0]); 
            //  Collect indices of validators attestating for tgt1 and tgt2
            var i1 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt1); 
            var i2 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt2); 
            //  Every validator in i1 * i2 violates ruleI
            tgt1 != tgt2 ==> 
                forall i :: i in i1 * i2 ==> validatorViolatesRuleI(store.rcvdAttestations, i as ValidatorIndex)

    {
        oneFinalisedImpliesJustifiedFromRoot(bh1, f, store, store.rcvdAttestations);
        //  proof that j == f and bf != bj we have a violation of rule I
        if j == f {
            //  bf != bj and we can apply lemma_4_11
            var k1 := computeAllEBBsFromRoot(bh1, f, store);
            //  EBB(bh1, j) is k1[0]
            var k2 := computeAllEBBsFromRoot(bh2, j, store);
            var tgt1 := CheckPoint(f as Epoch, k1[0]);
            var tgt2 := CheckPoint(j as Epoch, k2[0]);

            //  Collect validators for tgt1 and tgt2
            var i1 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt1); 
            var i2 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt2); 

            //  Apply lemma 4.
            lemma4_11_a(bh1, bh2, store, j);
            assert(|i1 * i2| >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1);
        } else {
            //  j > f 
            oneFinalisedImpliesJustifiedFromRoot(bh1, f, store, store.rcvdAttestations);
            assert(isJustifiedEpochFromRoot(bh1, f, store, store.rcvdAttestations));
            //  let l be the EBB that justifies epoch j 
            assert(isJustifiedEpochFromRoot(bh2, j, store, store.rcvdAttestations));
            // var l :| 
            //  for this case, the reasoning is more involved,
            var k1 := computeAllEBBsFromRoot(bh1, f, store);
            //  EBB(bh1, j) is k1[0]
            var k2 := computeAllEBBsFromRoot(bh2, j, store);
            // assert(isJustifiedEpoch(k2, j, store, store.rcvdAttestations));

            var tgt1 := CheckPoint(f as Epoch, k1[0]);
            var tgt2 := CheckPoint(j as Epoch, k2[0]);

            // var tgtl := CheckPoint(l as Epoch, k2[j - l]);
            var l :| l < j && isJustifiedEpoch(k2, l, store, store.rcvdAttestations); 
            // assume(isJustifiedEpochFromRoot(bh2, l, store, store.rcvdAttestations));
            // calc {
            //     isJustifiedEpoch(k2, l, store, store.rcvdAttestations);
            //     ==>
            //     isJustifiedEpochFromRoot(bh2, l, store, store.rcvdAttestations);
            // }

            //  later assume that j is the smallest epoch after f that is justified and remove
            //  this assume(l <= f);
            assume(0 < l <= f);

            if (l == f) {
                // assert(isJustifiedEpochFromRoot(bh1, f, store, store.rcvdAttestations));
                //  get the checkpoijnt at epoch l 
                var kl := computeAllEBBsFromRoot(bh2, l, store);
                var tgtl := CheckPoint(l as Epoch, kl[0]);
                liftFromRoot(bh2, j, l, store, store.rcvdAttestations);
                assert(isJustifiedEpochFromRoot(bh2, l, store, store.rcvdAttestations));
                //  Apply lemma 4
                lemma4_11_a(bh1, bh2, store, l);
                assert(|collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt1) * collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgtl)|
                >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1);

            } else {
                //  l < f 
                assert(l < f);
                //  In this case, we can show that the validators in V1 /\ V2 
                //  violated rule II
                // var c1: collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt1);
                //  collect indices that attest l == J ==> j 
                var kl := computeAllEBBsFromRoot(bh2, l, store);
                var srcl := CheckPoint(l as Epoch, kl[0]);
                var i1 := collectValidatorsAttestatingForLink(store.rcvdAttestations, srcl, tgt2);
                //  collect indices that attest f == J ==> f + 1
                var k2 := computeAllEBBsFromRoot(bh1, f + 1, store);
                var srcf := CheckPoint(f + 1 as Epoch, k2[0]);
                var tgtfPlusOne := CheckPoint(f as Epoch, k2[1]);
                var i2 := collectValidatorsAttestatingForLink(store.rcvdAttestations, srcf, tgtfPlusOne);

                //  Take a validator in i1 /\ i2, it has made a nested attestation that 
                //  violates ruleII.
                if i1 * i2 != {} {
                    var v :| v in i1 * i2 ;
                    //  Get two attestations made by validator v in i1 /\ i2
                    //  Must exist by post-conditions of collectValidatorsAttestatingForLink(...)
                    var a1 : PendingAttestation :| a1 in store.rcvdAttestations && a1.data.source == srcl && a1.data.target == tgt2 && a1.aggregation_bits[v];
                    var a2 : PendingAttestation :| a2 in store.rcvdAttestations && a2.data.source == srcf && a2.data.target == tgtfPlusOne && a2.aggregation_bits[v];
                    //  Validator v violates rule II
                    //  Attestations must be well-formed in store so they must be from LJ to LE
                    //  a1.tgt must be LJ from a1.data.beacon_block_root
                    assume(a1.data.beacon_block_root in store.blocks.Keys);
                    assume(a1.data.beacon_block_root in store.block_states.Keys);
                    assume(isValidPendingAttestation(a1, store, store.rcvdAttestations));
                    // assert(isValidAttestationData(a1.data, store, store.rcvdAttestations));
                    // var c1 :=  lastJustified(a1.data.beacon_block_root, l, store, store.rcvdAttestations);
                    // assert(srcl.epoch == c1.epoch);
                    // assert(srcl.root == c1.root);
                    // assume(a1.data.beacon_block_root);
                    // assert(validatorViolatesRuleII(a1, a2, store, store.rcvdAttestations, v as ValidatorIndex));

                }
            
                // assume(|collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt1) * collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, tgt2)|
            // >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1);
            }
        }
    }

 /**
     *  In a view G, if (Bf, f) in F(G) and (Bj, j) in J(G) with j > f, then Bf
     *  must be an ancestor of Bj , or the blockchain is (1/3)-slashable – 
     *  specifically, there must exist 2 subsets V1, V2 of V, each with total stake at 
     *  least 2N/3, such that their intersection all violate slashing condition (S1) 
     *  or all violate slashing condition (S2).
     *
     *  Proof for 1-finalisation.
     *
     *  Assume (bf,f) 1-finalised and (bj, j) justified and bf not a descendant of bf.
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
     *      aep(LJ(a)) < aep(LJ(b)) <     b.epoch   <   a.epoch 
     *  which violates S2 (no validator can make nested attestations).
     *  
     *   
     */
    lemma {:induction false} lemma5v2(cp1: CheckPoint, cp2: CheckPoint, store: Store)
        /** The block roots must be from accepted blocks, i.e. blocks in the store. */
        requires cp1.root in store.blocks.Keys
        requires cp2.root in store.blocks.Keys

        /** The epochs j and f are before the heads' slots. */
        requires cp2.epoch as nat + 1 <= MAX_UINT64

        //  The two blocks are not equal.
        requires cp1.root != cp2.root 

        /** Epoch is not zero */
        requires cp2.epoch >= cp1.epoch > 0 

        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

        /** Checkpoint at epoch f is 1-finalised. */
        requires isOneFinalised(cp1, store) 

        /** Checkpoint at epoch j is justified. */
        requires isJustified(cp2, store)

        //  Case 1: j == f, covered by lemma 4.
        ensures cp1.epoch == cp2.epoch ==> 
            var i1 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp1); 
            var i2 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp2); 
            //  Every validator in i1 * i2 violates ruleI
            forall i :: i in i1 * i2 ==> 
                validatorViolatesRuleI(store.rcvdAttestations, i as ValidatorIndex)
    {
        var bh1 :| bh1 in store.blocks.Keys && isOneFinalisedFromRoot(bh1, cp1.epoch, store, store.rcvdAttestations);
        var bh2 :| bh2 in store.blocks.Keys && isJustifiedEpochFromRoot(bh2, cp2.epoch, store, store.rcvdAttestations);

        if (cp1.epoch == cp2.epoch) {
            //  Show that lemma 4 applies
            //  bf != bj and we can apply lemma_4_11
            var k1 := computeAllEBBsFromRoot(bh1, cp1.epoch, store);
            //  EBB(bh1, j) is k1[0]
            var k2 := computeAllEBBsFromRoot(bh2, cp2.epoch, store);
            var tgt1 := CheckPoint(cp1.epoch as Epoch, k1[0]);
            var tgt2 := CheckPoint(cp2.epoch as Epoch, k2[0]);
            assert(tgt1.epoch == cp1.epoch);
            assume(tgt1.root == cp1.root);
            assert(tgt2.epoch == cp2.epoch);
            assume(tgt2.root == cp2.root);
            //  Collect validators for tgt1 and tgt2
            var i1 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp1); 
            var i2 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp2); 
            assert(cp1 != cp2);
            //  cp1 is one-finalised and hence justified
            // oneFinalisedImpliesJustified(cp1, store);
            oneFinalisedImpliesJustifiedFromRoot(bh1, cp1.epoch, store, store.rcvdAttestations);
            //  Apply lemma 4.
            // assume(isJustifiedEpochFromRoot(bh1, cp1.epoch, store, store.rcvdAttestations));
            // assume(isJustifiedEpochFromRoot(bh2, cp2.epoch, store, store.rcvdAttestations));
            // assume(bh1 != bh2);
            lemma4_11_a(bh1, bh2, store, cp1.epoch);
            // assert(|i1 * i2| >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1);            
        } else {

        }

    }

    /**
     *
     *  @param  br      A block root (head of the chain).
     *  @param  store   A store.
     *  @param  j       An epoch.
     *  @returns        Whether checkpoint at epoch j is justified in store.
     */
    // predicate isJustifiedInStore(br: Root, store: Store, j: Epoch)
    //     requires br in store.blocks.Keys
    //     /** The store is well-formed, each block with slot != 0 has a parent
    //         which is itself in the store. */
    //     requires isClosedUnderParent(store)
    //     requires isSlotDecreasing(store)

    //     /** Epoch is smaller than epoch of head block root. */
    //     requires 0 <= j <= compute_epoch_at_slot(store.blocks[br].slot)   
    // {   
    //     //  compute the anscestors of br
    //     var chRoots := chainRoots(br , store);
    //     //  Compute the EBBs indices (backwards) from epoch j
    //     var k2 := computeAllEBBsIndices(chRoots, j, store);
    //     //  The EBB at epoch j is (k2[0], j). Check whether epoch j - 0 is justified in store.
    //     isJustified(0, chRoots, k2, store.rcvdAttestations)
    // }

    /**
     *
     *  @param  br      A block root (head of the chain).
     *  @param  store   A store.
     *  @param  j       An epoch.
     *  @returns        Whether checkpoint at epoch j is one-finalised in store.
     */
    // predicate isOneFinalisedInStore(br: Root, store: Store, j: Epoch)
    //     requires br in store.blocks.Keys
    //     /** The store is well-formed, each block with slot != 0 has a parent
    //         which is itself in the store. */
    //     requires isClosedUnderParent(store)
    //     requires isSlotDecreasing(store)    //     /** Epoch is smaller than epoch of head block root. */
    //     requires 0 <= j as nat + 1 < compute_epoch_at_slot(store.blocks[br].slot) as nat 
    // {
    //     var chRoots := chainRoots(br, store);
    //     //  Compute the EBBs indices from epoch j + 1
    //     var k1 := computeAllEBBsIndices(chRoots, j + 1, store);
    //     //  EBB(br, j + 1) is k1[0] and EBB(br, j) is k1[1]
    //     isOneFinalised(1, chRoots, k1, store.rcvdAttestations) 
    // }


    /**
     *  Violation of Rule I (Gasper slashing conditions).
     *
     *  (S1) No validator makes two distinct attestations a1 a2 
     *  with ep(a1) == ep(a2). Note this
     *  condition is equivalent to aep(LE(a1)) = aep(LE(a2)).
     *  and LE(a) is the last epoch boundary pair (checkpoint) 
     *  of a i.e. (B, ep(slot(a))).
     */
    predicate validatorViolatesRuleI(links: ListOfAttestations, v: ValidatorIndex) 
    {
        // true
        exists a1, a2 : PendingAttestation ::
            a1 in links && a2 in links &&
            a1.data.target.root != a2.data.target.root 
            && a1.data.target.epoch == a2.data.target.epoch
            && a1.aggregation_bits[v] && a2.aggregation_bits[v]
        // forall a1, a2 :: PendingAttestation ==> 
        //     aep(LE(a1)) != aep(LE(a2))
    }

    predicate validatorViolatesRuleIv2(a1: PendingAttestation, a2: PendingAttestation, links: ListOfAttestations, v: ValidatorIndex) 
    {
        // true
        // exists a1, a2 : PendingAttestation ::
            a1 in links && a2 in links &&
            a1.data.target.root != a2.data.target.root 
            && a1.data.target.epoch == a2.data.target.epoch
            && a1.aggregation_bits[v] && a2.aggregation_bits[v]
        // forall a1, a2 :: PendingAttestation ==> 
        //     aep(LE(a1)) != aep(LE(a2))
    }

    predicate validatorViolatesRuleII(a1: PendingAttestation, a2: PendingAttestation, store: Store, links: ListOfAttestations, v: ValidatorIndex) 
    {
        //  Last justified (LJ) in a1.block head
        //  Using the epoch of the source should be OK as a valid attestation must 
        //  originate from LJ
        var lj1 := lastJustified(a1.data.beacon_block_root, a1.data.source.epoch, store, links);
        //  Last justified in a2.block head
        var lj2 := lastJustified(a2.data.beacon_block_root, a2.data.source.epoch, store, links);

        //  last EBB (LE)
        //  Using the target epoch should be OK as a valid attestation must target the
        //  most recent EBB.
        var ebbs1 := computeAllEBBsFromRoot(a1.data.beacon_block_root, a1.data.target.epoch, store);
        var le1 := CheckPoint(a1.data.target.epoch, ebbs1[0]);
        var ebbs2 := computeAllEBBsFromRoot(a2.data.beacon_block_root, a2.data.target.epoch, store);
        var le2 := CheckPoint(a2.data.target.epoch, ebbs2[0]);

        //  Validator v has made nested votes.
        lj1.epoch < lj2.epoch < le2.epoch < le1.epoch 
    }

    /**
     *  Rule II (Gasper slashing conditions).
     */
    predicate ruleII(s: Store, links: ListOfAttestations) 
    {
        true
    }


    /**
     *  Whether an attestation is well-formed.
     *
     *  @param  a       An attestattion.
     *  @param  store   A store.
     *  @param  links   A sequence of votes.
     *
     *  @returns        Whether an attestation data is valid.
     *                  The attestation has a Beacon block root as entry point
     *                  that defines its view of the block tree head.
     *                  It has a slot a.slot which in which the validator (ref by index) 
     *                  is making the attestation.
     *                  
     *                  An attestation is valid if:
     *                  1. its target is the last epoch boundary block (relative to 
     *                      the epoch that corresponds to a.slot)
     *                  2. its source is the last justified pair in the view of a. 
     */
    predicate isValidAttestationData(a : AttestationData, store: Store, links: seq<PendingAttestation>) 
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)
        /** The head block in `a` is in the store. */
        requires a.beacon_block_root in store.blocks.Keys
    {
        //  The chain from the block a.beacon_block_root pointed to by a.
        var xc := chainRoots(a.beacon_block_root, store);
        var br := a.beacon_block_root;
        //  The epoch of a, ep(a)
        var ep :=  compute_epoch_at_slot(a.slot);
        //  Compute the EBBs before ep
        var cr := computeAllEBBsFromRoot(br, ep, store);
        assert(|cr| == ep as nat + 1);
        //  EBBS
        // var ebbs := computeAllEBBsIndices(xc, ep, store);
        //  Index of Last justified checkpoint in ebbs, LJ(a). in [0..ep]
        var epochOfLJ := lastJustified(br, ep, store, links).epoch;
        // assert(0 <= indexOfLJ <= ep); 
        // true

        //  The target root must be the last epoch boundary pair in chain(a.beacon_block_root)
        //  xc[indexOfLEBB] is the block root for epoch ep in chain(a.beacon_block_root)
        a.target == CheckPoint(ep, cr[0])
        &&
        //  The source must be the last justified pair in chain(a.beacon_block_root)
        a.source == CheckPoint(epochOfLJ, cr[|cr| - 1 - epochOfLJ as nat])
        // &&
        // //  the index of the validator who made the atteatation must be
        // //  in the validstors state of the state pointed to.
        // a.proposer_index in store.blocks.Keys[a.beacon_block_root].validators
    }

    /**
     *  A valid pending attestation. 
     *
     *  @param  a       A pending attestation.
     *
     *  @param  store   A store.
     *  @param  links   A sequence of votes.  
     */
    predicate isValidPendingAttestation(a : PendingAttestation, store: Store, links: seq<PendingAttestation>) 
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)
        /** The head block in `a` is in the store. */
        requires a.data.beacon_block_root in store.blocks.Keys
        requires a.data.beacon_block_root in store.block_states.Keys
    {
        isValidAttestationData(a.data, store, links)
        &&
        //  The index of the validator who made the attestation must be
        //  in the validators' set of the state that corresponds
        //  to the block root in a.
        var s := a.data.beacon_block_root;
        a.proposer_index as nat < |store.block_states[s].validators|
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