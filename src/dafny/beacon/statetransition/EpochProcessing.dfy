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

include "../../utils/NativeTypes.dfy"
include "../../utils/NonNativeTypes.dfy"
include "../../utils/Eth2Types.dfy"
include "../forkchoice/ForkChoiceTypes.dfy"
include "../../utils/Helpers.dfy"
include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../validators/Validators.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../Helpers.dfy"
include "StateTransition.s.dfy"
include "../attestations/AttestationsHelpers.dfy"
/**
 * State transition function for the Beacon Chain.
 */
module EpochProcessing {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NativeTypes
    import opened NonNativeTypes
    import opened Eth2Types
    import opened ForkChoiceTypes
    import opened Constants
    import opened BeaconChainTypes
    import opened Validators
    import opened AttestationsTypes
    import opened Helpers
    import opened BeaconHelpers
    import opened StateTransitionSpec
    import opened AttestationsHelpers

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
     *  resgistry, slashing, and final updates.
     *
     *  @param  s   A beacon state.
     *  @returns    
     *  @todo       To be specified and implemented. currently returns s.
     */
    method process_epoch(s: BeaconState) returns (s' : BeaconState) 
        //  Make sure s.slot does not overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        //  And we should only execute this method when:
        requires (s.slot + 1) % SLOTS_PER_EPOCH == 0
        // ensures s' == updateFinalisedCheckpoint(updateJustification(s))
        ensures s' == finalUpdates(updateFinalisedCheckpoint(updateJustification(s)))
        requires |s.validators| == |s.balances|

        // ensures s' == updateFinalisedCheckpoint(updateJustification(s))

        ensures s'.eth1_deposit_index == s.eth1_deposit_index
        ensures s'.validators == s.validators
        ensures s'.balances == s.balances
        ensures |s'.validators| == |s'.balances|
    {
        assert(s.slot % SLOTS_PER_EPOCH != 0);
        s' := process_justification_and_finalization(s);
        // process_rewards_and_penalties(state)
        // process_registry_updates(state)
        // process_slashings(state)
        s' := process_final_updates(s');
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
    method process_final_updates(s: BeaconState)  returns (s' : BeaconState)
        ensures s' == finalUpdates(s)
    {
        s' := s.(
            previous_epoch_attestations := s.current_epoch_attestations,
            current_epoch_attestations := []
        );
    }

    /**
     *  Update justification and finalisation status.
     *
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#justification-and-finalization}
     */
    method process_justification_and_finalization(s : BeaconState) returns (s' : BeaconState) 
        requires s.slot % SLOTS_PER_EPOCH != 0
        requires |s.validators| == |s.balances|

        ensures s' == updateFinalisedCheckpoint(updateJustification(s))
        
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
            // old_previous_justified_checkpoint = state.previous_justified_checkpoint
            // old_current_justified_checkpoint = state.current_justified_checkpoint

            //  Process justifications and update justification bits
            // state.previous_justified_checkpoint = state.current_justified_checkpoint
            s' := s.(previous_justified_checkpoint := s.current_justified_checkpoint);

            // state.justification_bits[1:] = state.justification_bits[:JUSTIFICATION_BITS_LENGTH - 1]
            // state.justification_bits[0] = 0b0

            //  Right-Shift of justification bits and initialise first to false
            s' := s'.(justification_bits := [false] + (s.justification_bits)[..JUSTIFICATION_BITS_LENGTH - 1]); 
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
            var matching_target_attestations_prev := get_matching_target_attestations(s', previous_epoch) ;  
            // Previous epoch
            if get_attesting_balance(s', matching_target_attestations_prev) as uint128 * 3 >=       
                                get_total_active_balance(s') as uint128 * 2 {
                //  shift the justified checkpoint
                //  @todo   Why is current_justified_checkpoint field updated and not 
                //          previous?
                s' := s'.(current_justified_checkpoint := 
                            CheckPoint(previous_epoch,
                                        get_block_root(s', previous_epoch)));
                s' := s'.(justification_bits := s'.justification_bits[1 := true]);
            }
            // assert(s'.justification_bits == updateJustificationPrevEpoch(s).justification_bits);
            assert(s'.slot == updateJustificationPrevEpoch(s).slot);
            assert(s'.current_justified_checkpoint == updateJustificationPrevEpoch(s).current_justified_checkpoint);
            assert(s'.previous_justified_checkpoint == updateJustificationPrevEpoch(s).previous_justified_checkpoint);
            assert(s' == updateJustificationPrevEpoch(s)); 

            ghost var s2 := s';
            //  Current epoch
            var matching_target_attestations_cur := get_matching_target_attestations(s', current_epoch) ;
            if get_attesting_balance(s', matching_target_attestations_cur) as nat * 3 >=       
                                    get_total_active_balance(s') as nat * 2 {
                //  shift the justified checkpoint
                // s' := s'.(current_justified_checkpoint := 
                //             CheckPoint( current_epoch,
                //                         get_block_root(s', previous_epoch)));
                s' := s'.(
                        justification_bits := s'.justification_bits[0 := true],
                        current_justified_checkpoint := 
                            CheckPoint(current_epoch,
                                        get_block_root(s', current_epoch)));
            }
            assert(s' == updateJustificationCurrentEpoch(s2));
            // if get_attesting_balance(state, matching_target_attestations) * 3 >= get_total_active_balance(state) * 2:
    //     state.current_justified_checkpoint = Checkpoint(epoch=current_epoch,
    //                                                     root=get_block_root(state, current_epoch))
    //     state.justification_bits[0] = 0b1

            // assume(s' == updateJustification(s1));
            //  Process finalizations
            /*
             *  Epochs layout
             *
             *  | ............ | ........... | .......... | 
             *  | ............ | ........... | .......... | 
             *  e1             e2            e3           e4
             *  bit[0]        bit[1]        bit[2]        bit[3]
             *  current       previous
             *
             *  Python slice a[k:l] means: a[k] ... a[l -1]
             */
            ghost var s3 := s';

            var bits : seq<bool> := s'.justification_bits;
            //  The 2nd/3rd/4th most recent epochs are justified, the 2nd using the 4th as source
            // assume(s.previous_justified_checkpoint.epoch as nat + 3 < 0x10000000000000000 );
            //  if current_epoch == 2, s.previous_justified_checkpoint.epoch + 3 >= 3 so the 
            //  following condition is false. As a result we do not need to compute 
            //  s.previous_justified_checkpoint.epoch + 3 and can avoid a possible overflow.
            //  We assume here that the target language is such that AND conditions are evaluated ///   short-circuit i.e. unfolded as nested ifs
            //  
            if (all(bits[1..4]) && current_epoch >= 3 && s'.previous_justified_checkpoint.epoch  == current_epoch - 3) {
                s' := s'.(finalised_checkpoint := s'.previous_justified_checkpoint) ;
            }
            //  The 2nd/3rd most recent epochs are justified, the 2nd using the 3rd as source
            if (all(bits[1..3]) && s'.previous_justified_checkpoint.epoch == current_epoch - 2) {
                s' := s'.(finalised_checkpoint := s'.previous_justified_checkpoint) ;
            }
            //  The 1st/2nd/3rd most recent epochs are justified, the 1st using the 3rd as source
            if (all(bits[0..3]) && s'.current_justified_checkpoint.epoch == current_epoch - 2) {
                s' := s'.(finalised_checkpoint := s'.current_justified_checkpoint) ;
            }
            //  The 1st/2nd most recent epochs are justified, the 1st using the 2nd as source
            if (false && all(bits[0..2]) && s'.current_justified_checkpoint.epoch == current_epoch - 1) {
                s' := s'.(finalised_checkpoint := s'.current_justified_checkpoint) ;
            }
            assert(s' == updateFinalisedCheckpoint(s3));
            return s';
        }

    //  previous_epoch = get_previous_epoch(state)
    // current_epoch = get_current_epoch(state)
    // old_previous_justified_checkpoint = state.previous_justified_checkpoint
    // old_current_justified_checkpoint = state.current_justified_checkpoint
    //  Process justifications
    // state.previous_justified_checkpoint = state.current_justified_checkpoint
    // state.justification_bits[1:] = state.justification_bits[:JUSTIFICATION_BITS_LENGTH - 1]
    // state.justification_bits[0] = 0b0
    // matching_target_attestations = get_matching_target_attestations(state, previous_epoch)  # Previous epoch
    // if get_attesting_balance(state, matching_target_attestations) * 3 >= get_total_active_balance(state) * 2:
    //     state.current_justified_checkpoint = Checkpoint(epoch=previous_epoch,
    //                                                     root=get_block_root(state, previous_epoch))
    //     state.justification_bits[1] = 0b1
    // matching_target_attestations = get_matching_target_attestations(state, current_epoch)  # Current epoch
    // if get_attesting_balance(state, matching_target_attestations) * 3 >= get_total_active_balance(state) * 2:
    //     state.current_justified_checkpoint = Checkpoint(epoch=current_epoch,
    //                                                     root=get_block_root(state, current_epoch))
    //     state.justification_bits[0] = 0b1

    //  Process finalizations
    // bits = state.justification_bits
    //  The 2nd/3rd/4th most recent epochs are justified, the 2nd using the 4th as source
    // if all(bits[1:4]) and old_previous_justified_checkpoint.epoch + 3 == current_epoch:
    //     state.finalized_checkpoint = old_previous_justified_checkpoint
    //  The 2nd/3rd most recent epochs are justified, the 2nd using the 3rd as source
    // if all(bits[1:3]) and old_previous_justified_checkpoint.epoch + 2 == current_epoch:
    //     state.finalized_checkpoint = old_previous_justified_checkpoint
    //  The 1st/2nd/3rd most recent epochs are justified, the 1st using the 3rd as source
    // if all(bits[0:3]) and old_current_justified_checkpoint.epoch + 2 == current_epoch:
    //     state.finalized_checkpoint = old_current_justified_checkpoint
    //  The 1st/2nd most recent epochs are justified, the 1st using the 2nd as source
    // if all(bits[0:2]) and old_current_justified_checkpoint.epoch + 1 == current_epoch:
    //     state.finalized_checkpoint = old_current_justified_checkpoint


        return s;
    }

    
    
}