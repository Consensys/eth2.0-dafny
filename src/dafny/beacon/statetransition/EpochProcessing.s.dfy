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

    //  Specifications of justification and finalisation of a state and forward to future slot.

    /**
     *  Archive justification results on current epoch in previous epoch.
     *
     *  @param  s   A beacon state the slot of which is just before an Epoch boundary. 
     *  @returns    The new state with justification of CP before LEBB updated.
     *
     *  Example.
     *  epoch   0            1            2            3            4            5  
     *  CP      (b5,0)      (b5,1)        (b5,2)       (b2,3)       (b1,4)
     *          |............|............|............|............|..........s|....
     *          |............|............|............|............|..........s|s'...
     *  block   b5----------->b4---------->b3---->b2------>b1------->b0      
     *  slot    0             64           129    191      213       264
     *  bits(s) b3=1          b2=1         b1=1       b0=0                        s
     *  bits(s')              b3'0         b2'=1      b1'            b0'            s'
     *                        =======prevAttest=======>
     *
     *  assume current state is such that s.current_justified_checkpoint == (b5, 2)
     *  where epoch(s) == 4.
     *  The next state s' is the first one at the next epoch and 
     *  will have a slot that corresponds to epoch 5.
     *  Then s'.previous_justified_checkpoint is the CP justified at the previous 
     *  epoch for s' (5 - 1) and is defined by s.current_justified_checkpoint i.e.(b5, 2).
     *  The previous attestations (prevAttest) must attest from the previous checkpoint to 
     *  the LEBB(s). In the example assuming the previous checkpoint is (b5,1), 
     *  the attestations must have as target the checkpoint at previous epoch i.e. (b2, 3).
     *
     *  @note   It is assumed that the LEBB(s) cannot be justified yet.
     *
     *  If the link prevAttest is a supermajority link, then (b2,3) becomes justified.
     *  In the code below, prevAttest is get_matching_target_attestations(s, get_previous_epoch(s))
     *  and there is a supermajority if b1 is true.
     *  As for the justification bits, there are shifted in s'.
     *  The first (right to left) bit b0' is not know yet and set to default false value.
     *  The second (from the right) b1' is set to reflect the new status of the CP at 
     *  the previous epoch (3): if it becomes justified, the bit is set to 1 otherwise
     *  left to its previous value.
     *  
     */
    function updateJustificationPrevEpoch(s: BeaconState) : BeaconState 
        /** State's slot is not an Epoch boundary. */
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0
        /** Justification bit are right-shifted and last two are not modified.
            Bit0 (new checkpoint) and Bit1 (previous checkpoint) may be modified.
         */
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            updateJustificationPrevEpoch(s).justification_bits[2..] == 
                (s.justification_bits)[1..|s.justification_bits| - 1]
            &&
            updateJustificationPrevEpoch(s).justification_bits[0] == false
    {
        if  get_current_epoch(s) <= GENESIS_EPOCH + 1 then 
            s 
        else 
            //  Right shift justification_bits and prepend false
            var newJustBits:= [false] + (s.justification_bits)[..JUSTIFICATION_BITS_LENGTH - 1];
            //  Previous epoch checkpoint status update
            //  get attestations from previous justified to previous epoch CP
            var matching_target_attestations := 
                get_matching_target_attestations(s, get_previous_epoch(s));
            //  Supermajority status
            var b1 := get_attesting_balance(s, matching_target_attestations) as nat * 3 
                        >= get_total_active_balance(s) as nat * 2;
            s.(
                current_justified_checkpoint := 
                    if b1 then 
                        //  supermajority link to previous_epoch CP: use as current_justified
                        //  in next state.
                        CheckPoint(get_previous_epoch(s), get_block_root(s, get_previous_epoch(s)))
                    else 
                        s.current_justified_checkpoint,
                previous_justified_checkpoint := s.current_justified_checkpoint,
                justification_bits := if b1 then newJustBits[1 := true] else newJustBits
            )
    }

   /**
     *  Determine justification for current epoch in next state.
     *
     *  @param  s   A beacon state the slot of which is just before an Epoch boundary. 
     *  @returns    The new state with justification of LEBB checkpoint updated.
     *
     *  Example.
     *  epoch   0            1            2            3            4            5  
     *  CP      (b5,0)      (b5,1)        (b5,2)       (b2,3)       (b1,4)
     *          |............|............|............|............|..........s|....
     *          |............|............|............|............|..........s|s'...
     *  block   b5----------->b4---------->b3---->b2------>b1------->b0      
     *  slot    0             64           129    191      213       264
     *  bits(s) b3=1          b2=1         b1=1       b0=0                        s
     *  bits(s')              b3'0         b2'=1      b1'            b0'            s'
     *                        =======prevAttest=======>
     *                                      =====currentAttest=======>
     *
     *  assume current state is such that s.current_justified_checkpoint == (b5, 2)
     *  where epoch(s) == 4.
     *  The next state s' is the first one at the next epoch and 
     *  will have a slot that corresponds to epoch 5.
     *  Then s'.previous_justified_checkpoint is the CP justified at the previous 
     *  epoch for s' (5 - 1) and is defined by s.current_justified_checkpoint i.e.(b5, 2).
     *  The previous attestations (prevAttest) must attest from the previous checkpoint to 
     *  the LEBB(s). In the example assuming the previous checkpoint is (b5,1), 
     *  the attestations must have as target the checkpoint at previous epoch i.e. (b2, 3).
     *
     *  @note   It is assumed that the LEBB(s) cannot be justified yet.
     *
     *  If the link prevAttest is a supermajority link, then (b2,3) becomes justified
     *  and this is processed in `updateJustificationPrevEpoch`.
     *  In the code below, we check the LEBB(s) is justified, and if yes
     *  advance the current_justified_checkpoint for the next state to that
     *  checkpoint, overriding the update previously made in `updateJustificationPrevEpoch`
     *  (except the justification bit at that epoch).
     *  currentAttest is get_matching_target_attestations(s, get_current_epoch(s))
     *  and there is a supermajority if b1 is true.
     *  As for the justification bits, there are shifted in s'.
     *  The first (right to left) bit b0' is set to reflect the new status of the CP at 
     *  the current epoch (4): if it becomes justified, the bit is set to 1 otherwise
     *  left to its previous value (default 0).
     *  
     */
    function updateJustificationCurrentEpoch(s: BeaconState) : BeaconState 
        /** State's slot is just before an Epoch boundary. */
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0

        requires s.justification_bits[0] == false 

        /** Only bit 0 can be modified, and it should be false initially.
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
            s.(
                current_justified_checkpoint := 
                    if b1 then 
                        CheckPoint(get_current_epoch(s),get_block_root(s, get_current_epoch(s)))
                    else 
                        s.current_justified_checkpoint,
                justification_bits := if b1 then s.justification_bits[0 := true] else s.justification_bits
            )
    }

    /**
     *  Update justification is the result of the composition of 
     *  updating previous epoch justification status and current epoch justification status.
     *
     *  @param  s   A beacon state.
     *  @returns    The state s with the checkpoints statuses updated and justification
     *              bits set accordingly. 
     */

    function updateJustification(s: BeaconState) : BeaconState
        // requires s.slot % SLOTS_PER_EPOCH != 0
                requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0

        // ensures updateJustification(s) == 
        //     updateJustificationCurrentEpoch(updateJustificationPrevEpoch(s))
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            updateJustificationCurrentEpoch(s).justification_bits[1..] == 
                (s.justification_bits)[1..|s.justification_bits|]
        // ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==>  updateJustification(s).previous_justified_checkpoint == s.current_justified_checkpoint
    {
        updateJustificationCurrentEpoch(updateJustificationPrevEpoch(s))
    }

    function updateJustificationAndFinalisation(s: BeaconState) : BeaconState
        // requires s.slot % SLOTS_PER_EPOCH != 0
                requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0

    {
        updateFinalisedCheckpoint(updateJustification(s), s)
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