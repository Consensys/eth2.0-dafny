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

include "../../utils/NonNativeTypes.dfy"
include "../../ssz/Constants.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../Helpers.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../forkchoice/ForkChoiceTypes.dfy"
include "EpochProcessing.s.dfy"
include "../gasper/GasperJustification.dfy"

/**
 * State transition function for the Beacon Chain.
 */
module EpochProcessing {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NonNativeTypes
    import opened Constants
    import opened BeaconChainTypes
    import opened AttestationsTypes
    import opened BeaconHelpers
    import opened AttestationsHelpers
    import opened EpochProcessingSpec
    import opened ForkChoiceTypes
    import opened GasperJustification


// # Attestations
//     previous_epoch_attestations: List[PendingAttestation, MAX_ATTESTATIONS * SLOTS_PER_EPOCH]
//     current_epoch_attestations: List[PendingAttestation, MAX_ATTESTATIONS * SLOTS_PER_EPOCH]
//     # Finality
//     justification_bits: Bitvector[JUSTIFICATION_BITS_LENGTH]  # Bit set for every recent justified epoch
//     previous_justified_checkpoint: Checkpoint  # Previous epoch snapshot
//     current_justified_checkpoint: Checkpoint
//     finalized_checkpoint: Checkpoint

    /**
     *  At epoch boundaries, update justifications, rewards, penalities,
     *  registry, slashing, and final updates.
     *
     *  @param  s   A beacon state.
     *  @returns    
     */
    method process_epoch(s: BeaconState, store: Store) returns (s' : BeaconState) 
        //  Make sure s.slot does not overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        //  And we should only execute this method when:
        requires (s.slot + 1) % SLOTS_PER_EPOCH == 0
        // requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0

        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

         /** Slot of s is larger than slot at previous epoch. */
        requires get_current_epoch(s) * SLOTS_PER_EPOCH < s.slot  
        requires get_previous_epoch(s) * SLOTS_PER_EPOCH < s.slot  

        // requires foo606(s, store)
        
        requires blockRootsValidWeak(s, store)

        /** Block root at current epoc is in store. */
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys

        /** Current justified checkpoint is justified and root in store. */ 
        requires s.current_justified_checkpoint.root in store.blocks.Keys 
        requires s.current_justified_checkpoint.epoch < get_current_epoch(s)
        requires s.current_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store)
        requires isJustified(s.current_justified_checkpoint, store)
       
        /** The block root at previous epoch is in the store. */
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys

        requires s.previous_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store) 
        requires s.previous_justified_checkpoint.epoch < get_previous_epoch(s)
        /** The attestations at previous epoch are valid. */
        requires validPrevAttestations(s, store)

        /** The justified checkpoints in s are indeed justified ands the root is in store. */
        requires s.previous_justified_checkpoint.root in store.blocks.Keys 
        requires s.current_justified_checkpoint.root in store.blocks.Keys 
        
        requires isJustified(s.previous_justified_checkpoint, store)
        requires isJustified(s.current_justified_checkpoint, store)

        //  /** Attestations to current epoch are valid. */
        requires validCurrentAttestations(updateJustificationPrevEpoch(s, store), store)

        requires |s.validators| == |s.balances|


        // requires |s.validators| == |s.balances|

        /** Update justification and finalisation accodring to functional spec. */
        ensures s' == finalUpdates(updateFinalisedCheckpoint(updateJustification(s, store), s, store), store)

        /** Leaves some fields unchanged. */
        ensures s'.slot == s.slot
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
    {
        assert(s.slot as nat + 1 < 0x10000000000000000 as nat);
        s' := process_justification_and_finalization(s, store);
        // process_rewards_and_penalties(state)
        // process_registry_updates(state)
        // process_slashings(state)
        s' := process_final_updates(s', store);
        // assert(s' == finalUpdates(s2));
        // assume(s' == forwardStateToSlot(s, s.slot));
        // assume(s' == resolveStateRoot(s));
        return s';
    }

    /**
     *  Rotate the attestations.
     *  @param  s   A state.
     *  @returns    `s` with attestations rotated.
     *
     *  @todo       This is a partial implementation capturing only
     *              the attestations updates.
     */
    method process_final_updates(s: BeaconState, ghost store: Store)  returns (s' : BeaconState)
        // requires blockRootsValidWeak(s, store)
        ensures s' == finalUpdates(s, store)
    {
        s' := s.(
            previous_epoch_attestations := s.current_epoch_attestations,
            current_epoch_attestations := []
        );
    }

    /**
     *  Update justification and finalisation status.
     *  
     *  @param  s   A beacon state.
     *  @returns    The state obtained after updating the justification/finalisation
     *              variables of `s`.
     *
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#justification-and-finalization}
     */
    method process_justification_and_finalization(s : BeaconState, store: Store) returns (s' : BeaconState) 
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0

        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        requires blockRootsValidWeak(s, store)

         /** Slot of s is larger than slot at previous epoch. */
        requires get_current_epoch(s) * SLOTS_PER_EPOCH < s.slot  
        requires get_previous_epoch(s) * SLOTS_PER_EPOCH < s.slot  

        /** Block root at current epoc is in store. */
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys

        /** Current justified checkpoint is justified and root in store. */ 
        requires s.current_justified_checkpoint.root in store.blocks.Keys 
        requires s.current_justified_checkpoint.epoch < get_current_epoch(s)
        requires s.current_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store)
        requires isJustified(s.current_justified_checkpoint, store)
       
        /** The block root at previous epoch is in the store. */
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys

        requires s.previous_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store) 
        requires s.previous_justified_checkpoint.epoch < get_previous_epoch(s)
        /** The attestations at previous epoch are valid. */
        requires validPrevAttestations(s, store)

        /** The justified checkpoints in s are indeed justified ands the root is in store. */
        requires s.previous_justified_checkpoint.root in store.blocks.Keys 
        requires s.current_justified_checkpoint.root in store.blocks.Keys 
        
        requires isJustified(s.previous_justified_checkpoint, store)
        requires isJustified(s.current_justified_checkpoint, store)

        //  /** Attestations to current epoch are valid. */
        requires validCurrentAttestations(updateJustificationPrevEpoch(s, store), store)

        requires |s.validators| == |s.balances|

        /** Computes the next state according to the functional specification. */
        ensures s' == updateFinalisedCheckpoint(updateJustification(s, store), s, store)
        
        /** Some components of the state are left unchanged. */
        ensures s'.slot == s.slot
        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
    {
        //  epoch in state s is given by s.slot

        if get_current_epoch(s) <= GENESIS_EPOCH + 1 {
            //  Initial FFG checkpoint values have a `0x00` stub for `root`.
            //  Skip FFG updates in the first two epochs to avoid corner cases 
            //  that might result in modifying this stub.
            return s;   
        } else {
            assert(get_current_epoch(s) >= 2);
            //  Process justifications and finalisations
            var previous_epoch := get_previous_epoch(s);
            var current_epoch := get_current_epoch(s);
            assert(previous_epoch == current_epoch - 1);
            assert(previous_epoch as int * SLOTS_PER_EPOCH as int  < s.slot as int);
            assert(s.slot as int - (previous_epoch as int *  SLOTS_PER_EPOCH as int) 
                        <=  SLOTS_PER_HISTORICAL_ROOT as int );

            //  Process justifications and update justification bits
            // state.previous_justified_checkpoint = state.current_justified_checkpoint
            s' := s.(previous_justified_checkpoint := s.current_justified_checkpoint);

            //  Right-Shift of justification bits and initialise first to false
            s' := s'.(justification_bits := 
                [false] + (s.justification_bits)[..JUSTIFICATION_BITS_LENGTH - 1]); 
            //  Determine whether ??
            assert(get_previous_epoch(s') <= previous_epoch <= get_current_epoch(s'));
            assert(s'.slot == s.slot);
            assert(previous_epoch as int * SLOTS_PER_EPOCH as int  < s'.slot as int);
            //  slot of previous epoch is not too far in the past
            assert(s'.slot as int - (previous_epoch as int *  SLOTS_PER_EPOCH as int) 
                        <=  SLOTS_PER_HISTORICAL_ROOT as int );
            assert(s'.block_roots == s.block_roots);
            assert(get_block_root(s', previous_epoch) == get_block_root(s, previous_epoch));
            assert(|s'.validators| == |s.validators|);
            //  Compute the attestations in s.previous_epoch_attestations that 
            //  vote for get_block_root(state, previous_epoch) i.e. the block root at the beginning
            //  of the previous epoch. (retrieve in the historical roots).
            //  @note We use s to collect the target attestations instead of s' 
            //  in the orginal specs as we need to ensure that validPrevAttestations holds.
            var matching_target_attestations_prev := get_matching_target_attestations(s, previous_epoch, store) ;  
            //  @note should be the same as get_matching_target_attestations(s, previous_epoch) ; 

            // Previous epoch
            if get_attesting_balance(s', matching_target_attestations_prev) as nat * 3 >      
                                get_total_active_balance(s') as nat * 2 {
                //  shift the justified checkpoint
                s' := s'.(current_justified_checkpoint := 
                            CheckPoint(previous_epoch,
                                        get_block_root(s', previous_epoch)));
                s' := s'.(justification_bits := s'.justification_bits[1 := true]);
            }
            assert(s'.slot == updateJustificationPrevEpoch(s, store).slot);
            assert(s'.current_justified_checkpoint == updateJustificationPrevEpoch(s, store).current_justified_checkpoint);
            assert(s'.previous_justified_checkpoint == updateJustificationPrevEpoch(s, store).previous_justified_checkpoint);
            assert(s' == updateJustificationPrevEpoch(s, store)); 

            ghost var s2 := s';
            //  Current epoch
            var matching_target_attestations_cur := get_matching_target_attestations(s', current_epoch, store) ;
            if get_attesting_balance(s', matching_target_attestations_cur) as nat * 3 >       
                                    get_total_active_balance(s') as nat * 2 {
                //  shift the justified checkpoint
                s' := s'.(
                        justification_bits := s'.justification_bits[0 := true],
                        current_justified_checkpoint := 
                            CheckPoint(current_epoch,
                                        get_block_root(s', current_epoch)));
            }
            assert(s' == updateJustificationCurrentEpoch(s2, store));

            //  Process finalizations
            /*
             *  Epochs layout
             *
             *  | ............ | ........... | .......... | ........ |
             *  | ............ | ........... | .......... | ........ |
             *  e1             e2            e3           e4
             *  bit[3]        bit[2]        bit[1]        bit[0]
             *  
             *
             *  Python slice a[k:l] means: a[k] ... a[l - 1]
             */
            ghost var s3 := s';

            var bits : seq<bool> := s'.justification_bits;
            assume(s.previous_justified_checkpoint.epoch as nat + 3 < 0x10000000000000000 );
            //  if current_epoch == 2, s.previous_justified_checkpoint.epoch + 3 >= 3 so the 
            //  following condition is false. As a result we do not need to compute 
            //  s.previous_justified_checkpoint.epoch + 3 and can avoid a possible overflow.
            //  We assume here that the target language is such that AND conditions are evaluated ///   short-circuit i.e. unfolded as nested ifs
            //  
            //  The 2nd/3rd/4th most recent epochs are justified, the 2nd using the 4th as source
            if (all(bits[1..4]) && current_epoch >= 3 && s.previous_justified_checkpoint.epoch  == current_epoch - 3) {
                s' := s'.(finalised_checkpoint := s.previous_justified_checkpoint) ;
            }
            //  The 2nd/3rd most recent epochs are justified, the 2nd using the 3rd as source
            if (all(bits[1..3]) && s.previous_justified_checkpoint.epoch == current_epoch - 2) {
                s' := s'.(finalised_checkpoint := s.previous_justified_checkpoint) ;
            }
            //  The 1st/2nd/3rd most recent epochs are justified, the 1st using the 3rd as source
            if (all(bits[0..3]) && s.current_justified_checkpoint.epoch == current_epoch - 2) {
                s' := s'.(finalised_checkpoint := s.current_justified_checkpoint) ;
            }
            //  The 1st/2nd most recent epochs are justified, the 1st using the 2nd as source
            if (all(bits[0..2]) && s.current_justified_checkpoint.epoch == current_epoch - 1) {
                s' := s'.(finalised_checkpoint := s.current_justified_checkpoint) ;
            }
            assert(s' == updateFinalisedCheckpoint(s3, s, store));
            return s';
        }
    }

}