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
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../Helpers.dfy"
include "../BeaconChainTypes.dfy"
include "../statetransition/EpochProcessing.s.dfy"
include "EpochProcessingHelpers.dfy"

/**
 *  Proofs for the ForkChoice properties.  
 */
module EpochProcessingProofs {
    
    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened Constants
    import opened ForkChoiceTypes
    import opened ForkChoiceHelpers
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened BeaconHelpers
    import opened BeaconChainTypes
    import opened EpochProcessingSpec
    import opened EpochProcessingHelpers

    /**
     *  RuleI for slashing. 
     *  A validator cannot vote more than once for a given epoch.
     */
    // predicate ruleI(xa : seq<PendingAttestation>) 
    // {
    //     forall a1, a2 :: a1 in xa && a2 in xa ==>

    // }
    /**
     *  The last justified checkpoint in view(s).
     */

    // function lastJustifiedCheckPoint(s: BeaconState, store: Store) : CheckPoint 
    //     requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
    //     requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
    //     requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
    //     requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
    //     requires isClosedUnderParent(store)
    // {
    //     var r := get_block_root(s, get_current_epoch(s));
    //     var roots := chainRoots(r, store); 
    //     //  |ebbsIndices| ==  get_current_epoch(s) + 1
    //     var ebbsIndices := computeAllEBBsIndices(roots, get_current_epoch(s), store);
    //     var lastJustified := lastJustified(roots, ebbsIndices, store.attestations);
    //     CheckPoint((|ebbsIndices| - 1 - lastJustified) as Epoch, roots[ebbsIndices[lastJustified]])
    // }


    /**
     *  Whether a checkpoint is justified in the view that corresponds to a state.
     */
    // predicate isJustifiedCheckPoint(cp : CheckPoint, s: BeaconState, store: Store) 
    //     requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
    //     requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
    //     requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
    //     requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
    //     requires isClosedUnderParent(store)

    // {
    //     var r := get_block_root(s, get_current_epoch(s));
    //     var roots := chainRoots(r, store); 
    //     var ebbsIndices := computeAllEBBsIndices(roots, get_current_epoch(s), store);
    //     exists i :: 0 <= i < |ebbsIndices| && isJustified(i, roots, ebbsIndices, store.attestations)
    //         && cp == CheckPoint((|ebbsIndices| - i) as Epoch, roots[ebbsIndices[i]])
    // }

    /**
     *  If a checkpoint is justified and there is a supermajority link from it to 
     *  a more recent one, the more recent one is justified too.
     */
    lemma addJustified(cp1 : CheckPoint, cp2: CheckPoint, s: BeaconState, store: Store, links: seq<PendingAttestation>) 
        requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
        requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
        requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires isClosedUnderParent(store)

        requires isJustifiedCheckPoint(cp1, s, store)
        //  cp2 is a checkpoint in view(s)
        // requires exists 
        requires |collectAttestationsForLink(
                    links, 
                    cp1, 
                    cp2)| 
                        >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1
        // requires  
    {

    }


    /**
     *  Whether a checkpoint is the most recent justified in the view from s.
     */
    // predicate isMostRecentJustifiedCheckPoint(cp : CheckPoint, s: BeaconState, store: Store) 
    //     requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
    //     requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
    //     requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
    //     requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
    //     requires isClosedUnderParent(store)

    // {
    //     var r := get_block_root(s, get_current_epoch(s));
    //     var roots := chainRoots(r, store); 
    //     var ebbsIndices := computeAllEBBsIndices(roots, get_current_epoch(s), store);
    //     // exists i :: 0 <= i < |ebbsIndices| && isJustified(i, roots, ebbsIndices, store.
    //     var lastJustified := lastJustified(roots, ebbsIndices, store.attestations);
    //     cp == CheckPoint((|ebbsIndices| - lastJustified) as Epoch, roots[ebbsIndices[lastJustified]])
    // }

    /**
     *  Given a state `s`, and the attestations in s.current_epoch_attestations,
     *  if they are all valid they must originate from LJ(s).
     *
     *  @param  s       A state.
     *  @param  store   A store with all the received attestations.
     *  
     *  @note           This lemma is not trivial and assumed for now.
     */
    lemma validAttestationsHaveSourceLJ(s : BeaconState, store:  Store)
        requires s.slot % SLOTS_PER_EPOCH != 0
        requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
        requires get_current_epoch(s) > GENESIS_EPOCH + 1
        requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
        requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)


        /** All the attestations in the state are valid.  */
        requires forall a :: a in get_matching_target_attestations(s, get_current_epoch(s)) ==>    
            a.data.beacon_block_root in store.blocks.Keys && isValidAttestation(a.data, store, store.attestations)       
    
        ensures 
            forall a :: a in get_matching_target_attestations(s, get_current_epoch(s)) ==>
            a.data.source == lastJustifiedCheckPoint(s, store)
    {
        
        forall (a : PendingAttestation | a in get_matching_target_attestations(s, get_current_epoch(s)) )
            ensures a.data.source == lastJustifiedCheckPoint(s, store)
        {
            // assume(isValidAttestation(a.data, store, store.attestations));
            // //  The chain from a.beacon_block_root
            // var xc := chainRoots(a.data.beacon_block_root, store);
            // //  ep(a)
            // var ep :=  compute_epoch_at_slot(a.data.slot);
            // //  LEBB(a), LE(a) in the attestation
            // var indexOfLEBB := computeEBB(xc, ep, store);
            // //  EBBS
            // var ebbs := computeAllEBBsIndices(xc, ep, store);
            // //  Index of Last justified checkpoint in ebbs, LJ(a). in [0..ep]
            // var indexOfLJ := lastJustified(xc, ebbs, store.attestations) as Epoch;
            // // assert(a.data.target);

            // assert(a.data.source ==  CheckPoint(ep - indexOfLJ, xc[ebbs[indexOfLJ]]));
            // assert(|ebbs| == ep as nat + 1);
            // assert(lastJustifiedCheckPoint(s, store).epoch == |ebbs| as Epoch - 1 - indexOfLJ);
            // CheckPoint((|ebbs| as Epoch - indexOfLJ) as Epoch, xc[ebbs[indexOfLJ]]));

            assume(a.data.source == lastJustifiedCheckPoint(s, store));
        }
    }


    /**
     *  Attestations for current epoch have source the current justified checkpoint.
     *  @note   ASSUMED
     */
    lemma attestationsCurrentEpoch(s : BeaconState, store:  Store)
        requires s.slot % SLOTS_PER_EPOCH != 0
        requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
        requires get_current_epoch(s) > GENESIS_EPOCH + 1
        requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
        requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

        /** All the attestations in the state are valid.  */
        requires forall a :: a in get_matching_target_attestations(s, get_current_epoch(s)) ==>    
            a.data.beacon_block_root in store.blocks.Keys && isValidAttestation(a.data, store, store.attestations)       
    
        ensures 
            forall a :: a in get_matching_target_attestations(s, get_current_epoch(s)) ==>
            a.data.source == lastJustifiedCheckPoint(s, store)
    {
        
        forall (a : PendingAttestation | a in get_matching_target_attestations(s, get_current_epoch(s)) )
            ensures a.data.source == lastJustifiedCheckPoint(s, store)
        {
            // assume(isValidAttestation(a.data, store, store.attestations));
            // //  The chain from a.beacon_block_root
            // var xc := chainRoots(a.data.beacon_block_root, store);
            // //  ep(a)
            // var ep :=  compute_epoch_at_slot(a.data.slot);
            // //  LEBB(a), LE(a) in the attestation
            // var indexOfLEBB := computeEBB(xc, ep, store);
            // //  EBBS
            // var ebbs := computeAllEBBsIndices(xc, ep, store);
            // //  Index of Last justified checkpoint in ebbs, LJ(a). in [0..ep]
            // var indexOfLJ := lastJustified(xc, ebbs, store.attestations) as Epoch;
            // // assert(a.data.target);

            // assert(a.data.source ==  CheckPoint(ep - indexOfLJ, xc[ebbs[indexOfLJ]]));
            // assert(|ebbs| == ep as nat + 1);
            // assert(lastJustifiedCheckPoint(s, store).epoch == |ebbs| as Epoch - 1 - indexOfLJ);
            // CheckPoint((|ebbs| as Epoch - indexOfLJ) as Epoch, xc[ebbs[indexOfLJ]]));

            assume(a.data.source == lastJustifiedCheckPoint(s, store));
        }
    }

    /**
     *  Attestations for previous epoch have source the previous justified checkpoint.
     *  @note   ASSUMED
     */
    lemma attestationsPrevEpoch(s : BeaconState, store:  Store)
        requires s.slot % SLOTS_PER_EPOCH != 0
        requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
        requires get_current_epoch(s) > GENESIS_EPOCH + 1
        requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
        requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

        /** All the attestations in the state are valid.  */
        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==>    
            a.data.beacon_block_root in store.blocks.Keys && isValidAttestation(a.data, store, store.attestations)       
    
        ensures 
            forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==>
            a.data.source == s.previous_justified_checkpoint
            && a.data.target == CheckPoint(get_previous_epoch(s),
                                        get_block_root(s, get_previous_epoch(s)))
    {
        
        forall (a : PendingAttestation | a in get_matching_target_attestations(s, get_previous_epoch(s)) )
            ensures a.data.source == s.previous_justified_checkpoint 
            && a.data.target == CheckPoint(get_previous_epoch(s),
                                        get_block_root(s, get_previous_epoch(s)))
        {
    
            assume(a.data.source == s.previous_justified_checkpoint
                && a.data.target == CheckPoint(get_previous_epoch(s),
                                        get_block_root(s, get_previous_epoch(s)))
                                        );
        }
    }

    //  matching target attestations for previous are from previous justified cp
    //  matching target attestations for current epoch are from last justified.

    //  invariant in the state:
    //  s.current_epoch_attestations are from s.current_justified_cp (LJ, epoch) to LEBB(epoch)
    //  s.previous_epoch_attestations are from s.previous_justfified_cp (LJ epoch - 1) to LEBB(epoch  - 1)

    /**
     *  The checkpoints' status after the process_justification are
     *  correctly set.
     */
    lemma updateJustificationIsCorrect(s : BeaconState, store:  Store) 
        requires s.slot % SLOTS_PER_EPOCH != 0
        requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
        requires get_current_epoch(s) > GENESIS_EPOCH + 1
        requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
        requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

        requires isMostRecentJustifiedCheckPoint(s.current_justified_checkpoint, s, store)

        requires isJustifiedCheckPoint(s.previous_justified_checkpoint, s, store)
        requires isJustifiedCheckPoint(s.current_justified_checkpoint, s, store)

        /** New previous checkpoint in next state is justified. P1 */
        ensures var s' := updateJustification(s);
            isJustifiedCheckPoint(s'.previous_justified_checkpoint, s', store)
        /**  New current checkpoint in next state is justified. P2 */
        ensures var s' := updateJustificationPrevEpoch(s);
            isJustifiedCheckPoint(s'.current_justified_checkpoint, s', store)
    {
        var s':= updateJustification(s);
        //  P1 follows from definition 
        assert(s'.previous_justified_checkpoint == s.current_justified_checkpoint);

        //  Proof of second ensures
        var s'' :=  updateJustificationPrevEpoch(s);
        //  get attestations in state for previous epoch.
        var matching_target_attestations_prev_epoch := 
                get_matching_target_attestations(s, get_previous_epoch(s));
        var b1 := get_attesting_balance(s, matching_target_attestations_prev_epoch) as nat * 3 
                        >= get_total_active_balance(s) as nat * 2;
        if b1 {
            //  there is a supermajority for the checkpoint at previous epoch.
            //  because of the constraints on attestations in the state, this must
            //  be from the prev_justified_checkpoint which is justified.
            //  Proof that supermajority in 
            //  get_matching_target_attestations(s, get_previous_epoch(s)) must have 
            //  source s.current_justified_checkpoint
            assert(isJustifiedCheckPoint(s.previous_justified_checkpoint, s, store));
            // assert( isJustifiedCheckPoint());
            //  Hence this checkpoint is justified
            assume( isJustifiedCheckPoint(s''.current_justified_checkpoint, s', store));
        } else {
            assert(s''.current_justified_checkpoint ==  s.current_justified_checkpoint);
        }
        
    }

    lemma justificationFromPreviousAndSuper(s : BeaconState, store:  Store) 
        requires s.slot % SLOTS_PER_EPOCH != 0
        requires get_current_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  0x10000000000000000 
        requires get_current_epoch(s) > GENESIS_EPOCH + 1
        requires get_current_epoch(s) *  SLOTS_PER_EPOCH   < s.slot  
        requires s.slot  - get_current_epoch(s)  *  SLOTS_PER_EPOCH <= SLOTS_PER_HISTORICAL_ROOT 
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys

        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)

        requires isMostRecentJustifiedCheckPoint(s.current_justified_checkpoint, s, store)

        requires isJustifiedCheckPoint(s.previous_justified_checkpoint, s, store)
        requires isJustifiedCheckPoint(s.current_justified_checkpoint, s, store)

        /** All the attestations in the state are valid.  */
        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==>    
            a.data.beacon_block_root in store.blocks.Keys && isValidAttestation(a.data, store, store.attestations)   

        requires 
            var matching_target_attestations_prev_epoch := 
                get_matching_target_attestations(s, get_previous_epoch(s));
            get_attesting_balance(s, matching_target_attestations_prev_epoch) as nat * 3 
                        >= get_total_active_balance(s) as nat * 2
        
        // ensures 
        //     var previous_epoch := get_previous_epoch(s);
        //     isJustifiedCheckPoint(CheckPoint(previous_epoch,
        //                                 get_block_root(s, previous_epoch)), s, store)
    {
        var r := get_block_root(s, get_current_epoch(s));
        var roots := chainRoots(r, store); 
        var ebbsIndices := computeAllEBBsIndices(roots, get_current_epoch(s), store);
        assert(exists i :: 0 <= i < |ebbsIndices| && isJustified(i, roots, ebbsIndices, store.attestations)
            && s.previous_justified_checkpoint == CheckPoint((|ebbsIndices| - i) as Epoch, roots[ebbsIndices[i]]));
        
        //  1. attestations in prev_epoch are from s.previous_justified_checkpoint  to 
        //  CheckPoint(previous_epoch, get_block_root(s, previous_epoch))
        //  2. apply inductive def of isJustified
        attestationsPrevEpoch(s, store);
        //  attestations are from s.previous_justified_checkpoint to LEBB(prev_epoch)
        assert(forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==>
            a.data.source == s.previous_justified_checkpoint
            && a.data.target == CheckPoint(get_previous_epoch(s),
                                        get_block_root(s, get_previous_epoch(s))));
        //  because s.previous_justified_checkpoint is justified and supermajority to 
        //  cp == CheckPoint(get_previous_epoch(s),get_block_root(s, get_previous_epoch(s))))
        //  it follows that cp is justified.
    }
  
}