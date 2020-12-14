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

include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../Helpers.dfy"

/**
 * State transition functional specification for the Beacon Chain.
 */
module EpochProcessingSpec {
    
    //  Import some constants, types and beacon chain helpers.
    import opened Constants
    import opened BeaconChainTypes
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened BeaconHelpers

    //  Specifications of finalisation of a state and forward to future slot.

    /**
     *  Simplified first-cut specification of process_justification_and_finalization.
     *
     *  @param  s   A beacon state the slot of which is not an Epoch boundary. 
     *  @returns    The new state with justification checkpoints updated.
     *  
     */
    function updateJustificationPrevEpoch(s: BeaconState) : BeaconState 
        /** State's slot is not an Epoch boundary. */
        requires s.slot % SLOTS_PER_EPOCH != 0
        /** Justification bit are right-shifted and last two are not modified.
            Bit0 (new checkpoint) and Bit1 (previous checkpoint) may be modified.
         */
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            updateJustificationPrevEpoch(s).justification_bits[2..] == 
                (s.justification_bits)[1..|s.justification_bits| - 1]
    {
        if  get_current_epoch(s) <= GENESIS_EPOCH + 1 then 
            s 
        else 
            //  Right shift  justification_bits and prepend false
            var newJustBits:= [false] + (s.justification_bits)[..JUSTIFICATION_BITS_LENGTH - 1];
            //  Previous epoch checkpoint
            //  Get attestations 
            var matching_target_attestations := 
                get_matching_target_attestations(s, get_previous_epoch(s));
            var b1 := get_attesting_balance(s, matching_target_attestations) as nat * 3 
                        >= get_total_active_balance(s) as nat * 2;
            var c := CheckPoint(get_previous_epoch(s),
                                        get_block_root(s, get_previous_epoch(s)));
            s.(
                current_justified_checkpoint := if b1 then c else s.current_justified_checkpoint,
                previous_justified_checkpoint := s.current_justified_checkpoint,
                justification_bits := if b1 then newJustBits[1 := true] else newJustBits
            )
    }

    function updateJustification(s: BeaconState) : BeaconState
        requires s.slot % SLOTS_PER_EPOCH != 0
        // ensures updateJustification(s) == 
        //     updateJustificationCurrentEpoch(updateJustificationPrevEpoch(s))
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            updateJustificationCurrentEpoch(s).justification_bits[1..] == 
                (s.justification_bits)[1..|s.justification_bits|]
    {
        updateJustificationCurrentEpoch(updateJustificationPrevEpoch(s))
    }

    function updateJustificationAndFinalisation(s: BeaconState) : BeaconState
        requires s.slot % SLOTS_PER_EPOCH != 0
    {
        updateFinalisedCheckpoint(updateJustification(s), s)
    }

    /**
     *  Update related to the processing of current epoch.
     */
    function updateJustificationCurrentEpoch(s: BeaconState) : BeaconState 
        /** State's slot is not an Epoch boundary. */
        requires s.slot % SLOTS_PER_EPOCH != 0
        /** Justification bit are right-shifted and last two are not modified.
            Bit0 (new checkpoint) and Bit1 (previous checkpoint) may be modified.
         */
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            updateJustificationCurrentEpoch(s).justification_bits[1..] == 
                (s.justification_bits)[1..|s.justification_bits|]
    {
        if  get_current_epoch(s) <= GENESIS_EPOCH + 1 then 
            s 
        else 
            //  Get attestations for current epoch
            var matching_target_attestations := 
                get_matching_target_attestations(s, get_current_epoch(s));
            var b1 := get_attesting_balance(s, matching_target_attestations) as nat * 3 
                        >= get_total_active_balance(s) as nat * 2;
            var c := CheckPoint(get_current_epoch(s),
                                        get_block_root(s, get_current_epoch(s)));
            s.(
                current_justified_checkpoint := if b1 then c else s.current_justified_checkpoint,
                // previous_justified_checkpoint := s.current_justified_checkpoint,
                justification_bits := if b1 then s.justification_bits[0 := true] else s.justification_bits
            )
    }

    /**
     *  Update a state finalised checkpoint.
     *  @param  s   A state.
     *  @returns    The new state after updating the status of finalised_checkpoint.
     *  Epochs layout
     *
     *  | ............ | ........... | .......... | 
     *  | ............ | ........... | .......... | 
     *  e1             e2            e3           e4
     *  bit[0]        bit[1]        bit[2]        bit[3]
     *  current       previous
     *
    //  *  Python slice a[k:l] means: a[k] ... a[l -1]
     */
    function updateFinalisedCheckpoint(s: BeaconState, prevs: BeaconState) : BeaconState
        ensures s.slot == updateFinalisedCheckpoint(s, prevs).slot
    {
        if get_current_epoch(s) <= GENESIS_EPOCH + 1 then 
            s 
        else 
            var bits : seq<bool> := s.justification_bits;
            var current_epoch := get_current_epoch(s);
            if (all(bits[1..4]) && current_epoch >= 3 && prevs.previous_justified_checkpoint.epoch  == current_epoch - 3) then 
                //  The 2nd/3rd/4th most recent epochs are justified, the 2nd using the 4th as source
                s.(finalised_checkpoint := prevs.previous_justified_checkpoint) 
            else if (all(bits[1..3]) && prevs.previous_justified_checkpoint.epoch == current_epoch - 2) then 
                // The 2nd/3rd most recent epochs are justified, the 2nd using the 3rd as source
                s.(finalised_checkpoint := prevs.previous_justified_checkpoint) 
            else if (false && all(bits[0..3]) && prevs.current_justified_checkpoint.epoch == current_epoch - 2) then 
                // The 1st/2nd/3rd most recent epochs are justified, the 1st using the 3rd as source
                s.(finalised_checkpoint := prevs.current_justified_checkpoint) 
            else if (false && all(bits[0..2]) && prevs.current_justified_checkpoint.epoch == current_epoch - 1) then 
                // The 1st/2nd most recent epochs are justified, the 1st using the 2nd as source
                s.(finalised_checkpoint := prevs.current_justified_checkpoint) 
            else
                s 
    } 

    /**
     *  Final section of process_final_updates where attestations are rotated.
     *  @param  s   A beacon state.
     *  @returns    `s` with the attestations rotated.
     */
    function finalUpdates(s: BeaconState) : BeaconState
    {
        s.(
            previous_epoch_attestations := s.current_epoch_attestations,
            current_epoch_attestations := []
        )
    }

}