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

 // @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /trace /noCheating:1 /vcsMaxKeepGoingSplits:10 /vcsCores:12 /vcsMaxCost:1000  /vcsKeepGoingTimeout:30  /vcsFinalAssertTimeout:90  /verifySeparately


include "../../utils/Eth2Types.dfy"
include "../../utils/NativeTypes.dfy"
include "../../utils/SetHelpers.dfy"
include "../../ssz/Constants.dfy"
include "../forkchoice/ForkChoiceTypes.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../Helpers.dfy"
include "../BeaconChainTypes.dfy"
include "./GasperEBBs.dfy"
include "./GasperJustification.dfy"
include "./GasperFinalisation.dfy"
include "../validators/Validators.dfy"
 
/**
 *  Proofs for the safety properties of Gasper.  
 */
module GasperProofs {

    //  Equivalent of #define
    const FIXED_VAL_SET := true
    
    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened NativeTypes
    import opened SetHelpers
    import opened Constants
    import opened ForkChoiceTypes
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened BeaconHelpers
    import opened Validators
    import opened BeaconChainTypes
    import opened GasperEBBs
    import opened GasperJustification
    import opened GasperFinalisation

    /**
     *  Lemma 4.11. In a view G, for every epoch j, there is at most 1 pair (B, j) in J(G), 
     *  or the blockchain is (1/3)-slashable. In particular, the latter case means there 
     *  must exist 2 subsets V1, V2 of V, each with total weight at least 2N/3, such that 
     *  their intersection violates slashing condition (S1).
     *
     *  @param  cp1     A check point.
     *  @param  cp2     A check point.
     *  @param  store   A store.
     *  @param  v1      A set of validators.
     *  @param  v2      A set of validators.
     *  @returns        If the two checkpoints are justified at the same epoch and
     *                  are different, then there are two large sets v1 and v2 voting for them
     *                  such that each validator in the intersection violates rule I (slashing
     *                  condition 1)).
     *
     *  @note           Change the MAX_VALIDATORS_PER_COMMITTEE to another constant
     *                  which is the size of the set of validators. uint64 for validator
     *                  indices. should be the VALIDATOR_SET.
     *                  Define the validator set size. 
     */
    lemma {:induction false} lemma4_11(
        cp1: CheckPoint, 
        cp2: CheckPoint, 
        store: Store, 
        v1: set<ValidatorInCommitteeIndex>, 
        v2: set<ValidatorInCommitteeIndex>) 

        /** The block roots of the checkpoints must be from accepted blocks, i.e. in the store. */
        requires cp1.root in store.blocks.Keys
        requires cp2.root in store.blocks.Keys
        
        /** The checkpoints are distinct but have same epoch. */
        requires cp1.epoch == cp2.epoch > 0 
        requires cp1.root != cp2.root 

        /** The store is well-formed. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        /** The checkpoints are justified. */
        requires isJustified(cp1, store)
        requires isJustified(cp2, store)

        /** the validators in v1 and v2 voted for cp1 and cp2. */
        requires v1 == collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp1)
        requires v2 == collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp2)

        /**  v1 /\ v2 violates slashing condition 1. */
        ensures validatorSetsViolateRuleI(v1, v2, store.rcvdAttestations)
        ensures FIXED_VAL_SET ==> 
            |v1 * v2| >=  MAX_VALIDATORS_PER_COMMITTEE / 3 + 1

    {
        // If set of validators is fixed, v1 /\ v2 has more than 1/3
        if (FIXED_VAL_SET) {
            //  cp1 is justified and must have a super majority
            calc ==> {
                true;
                { justifiedMustHaveTwoThirdIncoming(cp1, store); }
                |v1| >=  (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;
            }
            //  cp2 same.
            calc ==> {
                true;
                { justifiedMustHaveTwoThirdIncoming(cp2, store); }
                |v2| >=  (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;
            }
            //  By the pigeon principle v1 /\ v2 has more than 1/3 elements
            pigeonHolePrincipleNat(v1, v2, MAX_VALIDATORS_PER_COMMITTEE);
        }

        //  Proof that each validator that attested for cp1 and cp2 violates rule I
        forall (i | i in v1 * v2) 
            ensures validatorViolatesRuleI(store.rcvdAttestations, i)
        {   //  Thanks Dafny
        }
    }

    /**
     *  There is only one block with slot == 0.
     *
     *  @param  store   A store.
     */
    predicate uniqueBlockAtSlotZero(store: Store) 
    {
        //  If two blocks have slot == 0 then they are identical
        forall  b1, b2 {:triggers store.blocks[b1].slot} :: 
            && b1 in store.blocks.Keys 
            && b2 in store.blocks.Keys 
            && store.blocks[b1].slot == 0 
            && store.blocks[b2].slot == 0
                ==> b1 == b2 
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
    lemma {:induction false} lemma5(cp1: CheckPoint, cp2: CheckPoint, store: Store)

        /** The store is well-formed, each block with slot != 0 
        has a parent which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

        /** There is unique block with slot zero in the store. */
        requires uniqueBlockAtSlotZero(store)

        /** The attestations received are valid.  */
        requires allAttestationsValidInStore(store) 

        /** Checkpoint 1. Finalised */
        /** The root must be a block in the store. */
        requires cp1.root in store.blocks.Keys
        /** cp1 is one-finalised so its epoch + 1 is less than MAX int 64. */
        requires cp1.epoch as nat + 1 <= MAX_UINT64
        requires isOneFinalised(cp1, store)

        /** Checkpoint 2. Justified. */
        requires cp2.root in store.blocks.Keys
        /** cp2 is justified. */
        requires isJustified(cp2, store) 

        //  Lemma 5 other assumptions.

        /** Epoch of cp2 is larger than epoch of cp1.*/
        requires cp2.epoch >= cp1.epoch 

        /** cp2.epoch is the first epoch >= cp1.epoch that is justified in 
            the ancestors of cp2.root. */
        requires forall c : CheckPoint :: 
            (c.root in chainRoots(cp2.root, store) && c.epoch < cp2.epoch) ==> 
                c.epoch < cp1.epoch

        /** cp1.root is not an ancestor of cp2.root */
        requires cp1.root !in chainRoots(cp2.root, store)

        /** There are two large enough validator sets such that
            their intersection is slashable. */
        ensures exists v1, v2: set<ValidatorInCommitteeIndex> :: 
            &&  |v1| >=  (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
            &&  |v2| >=  (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
            &&  (FIXED_VAL_SET ==> |v1 * v2| >= MAX_VALIDATORS_PER_COMMITTEE / 3 + 1)
            &&  (
                validatorSetsViolateRuleI(v1, v2, store.rcvdAttestations)
                ||
                validatorSetsViolateRuleII(v1, v2, store)
            )
    {
        reveal_validPrevAttestations();
        reveal_validCurrentAttestations();
        // reveal_isJustified();
        if (cp1.epoch == cp2.epoch == 0) {
            // oneFinalisedImpliesJustified(cp1, store); 
            assert(store.blocks[cp1.root].slot == 0);
            assert(store.blocks[cp2.root].slot == 0);
            assert(cp1.root == cp2.root);
            //  Contradiction
            assert(cp1.root in chainRoots(cp2.root, store));
        } else if (cp1.epoch == cp2.epoch > 0 ) {
            //  Collect the votes for cp1 and cp2.
            var v1 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp1); 
            var v2 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp2);
        
            assert(v1 == collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp1));

            assert(v2 == collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp2));

            //  As cp1 and cp2 are justified they have a minimum number of votes.
            calc ==> {
                true;
                { justifiedMustHaveTwoThirdIncoming(cp1, store); }
                |v1| >=  (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;
            }
            calc ==> {
                true;
                { justifiedMustHaveTwoThirdIncoming(cp2, store); }
                |v2| >=  (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;
            }
            //  If fixed set of validators
            if (FIXED_VAL_SET) {
                //  By the pigeon principle v1 /\ v2 has more than 1/3 elements
                pigeonHolePrincipleNat(v1, v2, MAX_VALIDATORS_PER_COMMITTEE);
            }
            //  Apply lemma 4.
            calc ==> {
                true;
                { lemma4_11(cp1, cp2, store, v1, v2); }
                validatorSetsViolateRuleI(v1, v2, store.rcvdAttestations);
            }
        } else if cp2.epoch == cp1.epoch + 1 {
                // reveal_isJustified();
                //  Get the next checkpoint justified by cp1
                var cp1PlusOne : CheckPoint :|
                    cp1PlusOne.epoch == cp1.epoch + 1 
                    && cp1PlusOne.root in store.blocks.Keys
                    && cp1.root in chainRoots(cp1PlusOne.root, store)
                    && |collectValidatorsAttestatingForLink(store.rcvdAttestations, cp1, cp1PlusOne)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;

                assert(cp2.epoch > 0);
                assert(isJustified(cp1PlusOne, store));
                assume(cp1PlusOne.root != cp2.root);
                var v1 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp1PlusOne); 
                assert(v1 == collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp1PlusOne));
                
                var v2 := collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp2);
                assert(v2 == collectValidatorsIndicesAttestatingForTarget(store.rcvdAttestations, cp2));
                //  cp1PlusOne root cannot be cp2.root (need to apply lemma 4).
                assert(cp1PlusOne.root != cp2.root);
                // cp1PlusOne is justified
                assert(isJustified(cp1PlusOne,store));
                //  Cardinal of sets v1 and v2
                calc ==> {
                    true;
                    { justifiedMustHaveTwoThirdIncoming(cp1PlusOne, store); }
                    |v1| >=  (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;
                }
                calc ==> {
                    true;
                    { justifiedMustHaveTwoThirdIncoming(cp2, store); }
                    |v2| >=  (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;
                }
                //  If fixed set of validators
                if (FIXED_VAL_SET) {
                    //  By the pigeon principle v1 /\ v2 has more than 1/3 elements
                    pigeonHolePrincipleNat(v1, v2, MAX_VALIDATORS_PER_COMMITTEE);
                }
                calc ==> {
                    true;
                    { lemma4_11(cp1PlusOne, cp2, store, v1, v2); }
                    validatorSetsViolateRuleI(v1, v2, store.rcvdAttestations);
                }
        } else {
            assert(cp2.epoch > cp1.epoch + 1);
            // reveal_isJustified();
            //  Get a checkpoint cp2_l that is justified and justifies cp2
            var cp2_l : CheckPoint :|
                && cp2_l.epoch < cp2.epoch 
                && cp2_l.root in chainRoots(cp2.root, store)
                && isJustified(cp2_l, store)
                && |collectValidatorsAttestatingForLink(store.rcvdAttestations, cp2_l, cp2)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;

            //  cp2.epoch is the first justified checkpoint after cp1.epoch 
            assert(cp2_l.epoch < cp1.epoch);

            //  Get the checkpoint at cp1.epoch + 1 that is justified
            var cp1PlusOne : CheckPoint :|
                cp1PlusOne.epoch == cp1.epoch + 1 
                && cp1PlusOne.root in store.blocks.Keys
                && cp1.root in chainRoots(cp1PlusOne.root, store)
                && |collectValidatorsAttestatingForLink(store.rcvdAttestations, cp1, cp1PlusOne)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;

            //  Collect validators attesting for cp1PlusOne 
            var v1 := collectValidatorsAttestatingForLink(store.rcvdAttestations, cp1, cp1PlusOne); 
            var v2 := collectValidatorsAttestatingForLink(store.rcvdAttestations, cp2_l, cp2);

            assert(v1 <= collectValidatorsAttestatingForLink(store.rcvdAttestations, cp1, cp1PlusOne));
            assert(v1 >= collectValidatorsAttestatingForLink(store.rcvdAttestations, cp1, cp1PlusOne));
            assert(v1 == collectValidatorsAttestatingForLink(store.rcvdAttestations, cp1, cp1PlusOne));
            assert(v2 <= collectValidatorsAttestatingForLink(store.rcvdAttestations, cp2_l, cp2));
            assert(v2 >= collectValidatorsAttestatingForLink(store.rcvdAttestations, cp2_l, cp2));
            assert(v2 == collectValidatorsAttestatingForLink(store.rcvdAttestations, cp2_l, cp2));
            //  Cardinal of sets v1 and v2
            calc ==> {
                true;
                { justifiedMustHaveTwoThirdIncoming(cp1PlusOne, store); }
                |v1| >=  (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;
            }
            calc ==> {
                true;
                { justifiedMustHaveTwoThirdIncoming(cp2, store); }
                |v2| >=  (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1;
            }
            //  If fixed set of validators
            if (FIXED_VAL_SET) {
                //  By the pigeon principle v1 /\ v2 has more than 1/3 elements
                pigeonHolePrincipleNat(v1, v2, MAX_VALIDATORS_PER_COMMITTEE);
            }
            //  The epochs of the checkpoints are nested like so:
            assert(cp2_l.epoch < cp1.epoch < cp1PlusOne.epoch  < cp2.epoch);
            //  And as a consequence every v in v1 /\ v2 violates rule II
            assert(validatorSetsViolateRuleII(v1, v2, store));
            
        }
    }


    /**
     *  Violation of Rule I (Gasper slashing conditions).
     *
     *  @param  links   A list of attestations.
     *  @param  v       A validator index.   
     *
     *  (S1) No validator makes two distinct attestations a1 a2 
     *  with ep(a1) == ep(a2). Note this
     *  condition is equivalent to aep(LE(a1)) = aep(LE(a2)).
     *  and LE(a) is the last epoch boundary pair (checkpoint) 
     *  of a i.e. (B, ep(slot(a))).
     */
    predicate validatorViolatesRuleI(links: ListOfAttestations, v: ValidatorInCommitteeIndex) 
    {
        // true
        exists a1, a2 ::
            a1 in links && a2 in links &&
            a1.data.target.root != a2.data.target.root 
            && a1.data.target.epoch == a2.data.target.epoch
            && a1.aggregation_bits[v] && a2.aggregation_bits[v]
            // && (a1.aggregation_validators[v1] == a2.aggregation_validators[v2] == v)
    }

    /**
     *  Whether two validator sets violate rule I.
     *  
     *  @param  v1      A set of validtor indices.
     *  @param  v2      A set of validtor indices.
     *  @param  links   A list of attestations.
     */
    predicate validatorSetsViolateRuleI(
        v1: set<ValidatorInCommitteeIndex>, 
        v2: set<ValidatorInCommitteeIndex>, 
        links: ListOfAttestations) 
    {
        forall v :: v in v1 * v2 ==>
            validatorViolatesRuleI(links, v as ValidatorInCommitteeIndex)
    }

    /**
     *  Whether a validator violates slashing condition 2.
     *  
     *  @param  a1      An attestation.
     *  @param  a2      An attestation.
     *  @param  store   A store,
     *  @param  v       A validator index.
     */
    predicate validatorViolatesRuleII(
        a1: PendingAttestation, 
        a2: PendingAttestation, 
        store: Store, 
        v: ValidatorInCommitteeIndex) 

        requires a1.data.beacon_block_root in store.blocks.Keys
        requires a2.data.beacon_block_root in store.blocks.Keys

        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)    
    {
        a1 in store.rcvdAttestations
        && a2 in store.rcvdAttestations
        && isValidPendingAttestation(a1, store)
        && isValidPendingAttestation(a2, store) 
        //  a1 and a2 are made by same validator
        && a1.aggregation_bits[v] && a2.aggregation_bits[v]

        //     exists v1 : ValidatorInCommitteeIndex, v2 : ValidatorInCommitteeIndex :: 
        //     (a1.aggregation_bits[v1] && a2.aggregation_bits[v2]
        //     && (a1.aggregation_validators[v1] == a2.aggregation_validators[v2] == v)
        // )
        //  Validator v has made nested votes.
        && a1.data.source.epoch < a2.data.source.epoch < a2.data.target.epoch < a1.data.target.epoch 
    }

    /**
     *  Whether the intersection of 
     *   two sets of validastor violate slashing condition 2.
     *  
     *  @param  v1      A set of validators..
     *  @param  v2      A set of validators..
     *  @param  store   A store,
     *  @param  links   A list of attestations.
     */
    predicate validatorSetsViolateRuleII(
        v1: set<ValidatorInCommitteeIndex>, 
        v2: set<ValidatorInCommitteeIndex>, 
        store: Store
        )  
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)    
    {
         forall v :: v in v1 * v2 ==>
            exists a1: PendingAttestation,  a2: PendingAttestation :: 
            a1.data.beacon_block_root in store.blocks.Keys &&
            a2.data.beacon_block_root in store.blocks.Keys &&
            validatorViolatesRuleII(a1, a2, store, v as ValidatorInCommitteeIndex)
    }

    /**
     *  Whether an attestation is well-formed.
     *
     *  @param  a       An attestation.
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
    predicate isValidAttestationData(a: AttestationData, store: Store) 
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)
    {
        a.beacon_block_root in store.blocks.Keys
        && a.beacon_block_root in store.block_states.Keys
        //  Target is the LEBB
        && var ep :=  compute_epoch_at_slot(a.slot);
           a.target == lastEBB(a.beacon_block_root, ep, store)
        //  The source must be the last justified pair in chain(a.beacon_block_root)
        && a.source == lastJustified(a.beacon_block_root, ep, store)
    }

    /**
     *  Whether a pending attestation is valid. 
     *
     *  @param  a       A pending attestation.
     *
     *  @param  store   A store.
     *  @param  links   A sequence of votes.  
     */
    predicate isValidPendingAttestation(a: PendingAttestation, store: Store) 
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)
    {
        isValidAttestationData(a.data, store)
        &&
        //  The index of the validator who made the attestation must be
        //  in the validators' set of the state that corresponds
        //  to the block root in a.
        var s := a.data.beacon_block_root;
        a.proposer_index as nat < |store.block_states[s].validators|
    }

    /**
     *  All the attestations in the store received so far are valid.
     *  @param  store   A store.
     */
    predicate allAttestationsValidInStore(store: Store) 
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)
    {
        forall a {:triggers a in store.rcvdAttestations} :: 
        a in store.rcvdAttestations ==> 
            isValidPendingAttestation(a, store)
    }

}