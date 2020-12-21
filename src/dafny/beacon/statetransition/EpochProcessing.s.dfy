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
 * Epoch processing functional specification.
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
            && updateJustificationPrevEpoch(s).justification_bits[0] == false
        // ensures get_current_epoch(s) == get_current_epoch(updateJustificationPrevEpoch(s))
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
                justification_bits := 
                    if b1 then newJustBits[1 := true] 
                    else newJustBits
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
     *  @note   The previous discussion shows that s.current_justified_checkpoint and
     *          s.previous_justified_checkpoint are not necessarily the two latest justified CPs.
     *          s.current_justified_checkpoint is the LJ, but there could be another CP (eg. at epcoh 3)
     *          that is determined justified between s.current_justified_checkpoint and
     *          s.previous_justified_checkpoint.
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
            //  Current epoch checkpoint status update
            //  get attestations from current justified to LEBB
            var matching_target_attestations := 
                get_matching_target_attestations(s, get_current_epoch(s));
            //  Supermajority status
            var b1 := get_attesting_balance(s, matching_target_attestations) as nat * 3 
                        >= get_total_active_balance(s) as nat * 2;
            s.(
                current_justified_checkpoint := 
                    if b1 then 
                        CheckPoint(get_current_epoch(s),get_block_root(s, get_current_epoch(s)))
                    else 
                        s.current_justified_checkpoint,
                justification_bits := 
                    if b1 then s.justification_bits[0 := true] 
                    else s.justification_bits
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
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0

        //  The last two bits are copied from the two middle bits of s.justification_bits
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            updateJustification(s).justification_bits[2..] == 
                (s.justification_bits)[1..|s.justification_bits| - 1]
    {
        if get_current_epoch(s) > GENESIS_EPOCH + 1 then 
            var k := updateJustificationPrevEpoch(s);
            updateJustificationCurrentEpoch(k)
        else 
            s
    }

    /**
     *  Compute the finalised checkpoint of the first state at a new epoch.
     *
     *  @param  s       A state s.
     *  @param  s'      A state that s' == updateJustification(s)
     *  @returns        The new state after updating the status of finalised_checkpoint.
     *
     *  Example.
     *                                                           LEBB(s)                         
     *  epoch   0            1            2            3            4            5  
     *  CP      (B5,0)      (B5,1)        (B5,2)       (B2,3)       (B1,4)
     *          |............|............|............|............|..........s|....
     *          |............|............|............|............|..........s|s'...
     *  block   B5----------->B4---------->B3---->B2------>B1------->B0      
     *  slot    0             64           129    191      213       264
     *  bits(s) b3=1          b2=1         b1=1       b0=0                        s
     *  bits(s')              b3'0         b2'=1      b1'            b0'            s'
     *                        =======prevAttest=======>
     *                                      LJ(s)===currentAttest===>LEBB(s)
     *
     *  @note   In the diagram above, s' is depicted as the first state in epoch 5,
     *          but in the updates, the slot (and hence epoch) of s' has njot been 
     *          incremented yet.
     *  @todo   Fix the diagram and use s'' = s'(slot := s.slot) 
     *
     *  assume current state is such that s.current_justified_checkpoint == (B5, 2)
     *  where epoch(s) == 4.
     *  After the justification updates, the justification bits have been updated.
     *  In this example we assume: 
     *  - LJ(s) == (B5,2)
     *  - LEBB(s) = (B1,4)
     *  It follows that:
     *  - s'.previous_justified_checkpoint == s.current_justified_checkpoint
     *  - s'.current_justified_checkpoint is:
     *      a) s.current_justified_checkpoint if neither prevAttest or currentAttest
     *      are supermajorities
     *      b) (B1, 4) (LEBB(s)) if currentAttest is a supermajority 
     *      c) (B2, 3) (LEBB(prevEpoch(s))) if prevAttest is a supermajority and currentAttest is not
     *
     *  The justification bits are as as follows:
     *      b' = [isSuper(currentAttest), isSuper(PrevAttest) or b0, b1, b2].
     *
     *  @note   If b0 was already true (a supermajority from some CP), then it remains true (justified).
     *          and in that case it must have been the LJ(s).
     *
     *  To update the status of a CP from justified to finalised, Gasper relies on 
     *  k-finalisation, with k = 1, 2.
     *  The k-finalisation definition is as follow:
     *  A checkpoint (B0, ep0) is k-finalised, k >= 1  iff:
     *  - it is the genesis block/epoch
     *  - or
     *      c1 (B0, ep0) --> (B1, ep0 + 1) --> ... -> (Bk, ep0 + k) is a chain from (B0, ep0)
     *      c2 (B0,ep0), (B1, ep0 + 1)...(Bk-1, ep0 + k - 1) are justified
     *      c3 (B0,ep0) ===Supermajority===> (Bk, ep0 + k).
     *  For k = 1, A checkpoint (B0, ep0) is 1-finalised, k >= 1:
     *      c1 (B0, ep0) --> (B1, ep0 + 1) is a chain from (B0, ep0)
     *      c2 (B0,ep0) is justified
     *      c3 (B0,ep0) ===Supermajority===> (B2, ep0 + 2).
     *      
     *  For k = 2, which is what is used in the Eth2.0 specs:
     *      c1 (B0, ep0) --> (B1, ep0 + 1) --> (Bk, ep0 + 2) is a chain from (B0, ep0)
     *      c2 (B0,ep0), (B1, ep0 + 1) are justified
     *      c3 (B0,ep0) ===Supermajority===> (Bk, ep0 + 2)
     *
     *  To determine the next and most recent finalised checkpoint, we check in order the 
     *  following conditions:
     *      H4.  s.current_justified_checkpoint is at epoch - 1 and is 1-finalised
     *      H3.  s.current_justified_checkpoint is at epoch - 2 and is 2-finalised 
     *      H2.  s.previous_justified_checkpoint is at epoch - 2 and is 1-finalised 
     *      H1.  s.previous_justified_checkpoint is at epoch - 3 and is 2-finalised
     *
     *  For k = 2 and considering the last four epochs justification bits in b', this yields:
     *
     *      H1: s.previous_justified_checkpoint is at epoch 1 (epoch(s) - 3), say (B5,1) is 2-finalised iff:
     *       c1 (B5,1) --> (B5,2) --> (B2,3) is a chain [OK]
     *       c2 (B5,1), (B5,2) are justified
     *       c3 (B5,1)  ===Supermajority===> (B2,3).
     *      c1 is satisfied by construction of the chain, c2 can be determined by bits b2, b1 i.e.
     *      b3', b2'. 
     *      There is a supermajority link L from s.previous_justified_checkpoint at epoch - 3 <==> 
     *          { attestations are well formed }
     *      L = s.previous_justified_checkpoint ===Supermajority===> previous LEBB <==>
     *      (B2,3) is justified <==>
     *      b0 is true <==>
     *      b1' is true.
     *      Overall, s.previous_justified_checkpoint at epoch - 3 is 2-finalised iff b3'=b2'=b1'=true.
     *
     *      H2: s.previous_justified_checkpoint is at epoch 2 (epoch(s) - 2) is 1-finalised iff:
     *       c1 (B5,2) --> (B2,3)is a chain [OK]
     *       c2 (B5,2) is justified
     *       c3 (B5,2) ===Supermajority===> (B2,3).
     *      c2 is satisfied iff b2'=true.
     *      For c3:
     *      There is a supermajority link L from  s.previous_justified_checkpoint at epoch - 2 <==>
     *           {attestations are well-formed }
     *      L = s.previous_justified_checkpoint ===Supermajority===> previous LEBB <==>
     *      previous LEBB is (B2,3) is justified <==>
     *      b1'=true
     *      Overall, s.previous_justified_checkpoint at epoch - 2 is 1-finalised iff b2'=b1'=true.
     *      
     *  Now we check whether the current justified checkpoint can be finalised (it is at an epoch >= 
     *  previous justified.)
     *      H3: s.current_justified_checkpoint is at epoch - 2 (2) is finalised iff:
     *       c1 (B5,2) --> (B2,3) --> (B1,4) is a chain [OK]
     *       c2 (B5,2), (B2,3) are justified
     *       c3 (B5,2)  ===Supermajority===> (B1,4).
     *      c2 is equivalent to b2'=b1'=true. 
     *      There is a supermajority link L from s.current_justified_checkpoint at epoch - 2 <==>
     *           {attestations are well-formed }
     *      L = s.current_justified_checkpoint ===Supermajority===> LEBB(s) <==>
     *      LEBB(s) is (B1,4) <==>
     *      (B1,4) is justified <==>
     *      b0'=true
     *  Overall, s.current_justified_checkpoint at epoch - 2 is finalised iff b2'=b1'=b0'=true.
     *
     *      H4: s.current_justified_checkpoint is at epoch - 1 (3) is 1-finalised iff:
     *       c1 (B2,3) --> (B1,4)  is a chain [OK]
     *       c2 (B2,3) is justified
     *       c3 (B2,3)  ===Supermajority===> (B1,4).
     *      c2 is equivalent to b1'==true
     *      For c3:
     *      There is a supermajority link L from  s.current_justified_checkpoint at epoch - 1 <==>
     *           {attestations are well-formed }
     *      L = s.current_justified_checkpoint ===Supermajority===> previous LEBB <==>
     *      previous LEBB is (B1,4) is justified <==>
     *      b0'=true
     *      Overall, s.current_justified_checkpoint at epoch - 1 is 1-finalised iff b0'=b1'=true.
     *      
     *  
     *  epoch   0            1            2            3            4            5  
     *  CP      (B5,0)      (B5,1)        (B5,2)       (B2,3)       (B1,4)
     *          |............|............|............|............|..........s|....
     *          |............|............|............|............|..........s|s'...
     *  block   B5----------->B4---------->B3---->B2------>B1------->B0      
     *  slot    0             64           129    191      213       264
     *  bits(s) b3=1          b2=1         b1=1       b0=0                        s
     *  bits(s')              b3'0         b2'=1      b1'            b0'            s'
     *                        =======prevAttest=======>
     *                                      LJ(s)===currentAttest===>LEBB(s)
     *
     *
     *  @note   Python array slice a[k:l] means elements from k to l - 1 [a[k] ... a[l -1]]
     */
    function updateFinalisedCheckpoint(s': BeaconState, s: BeaconState) : BeaconState
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0
        requires s' == updateJustification(s)

        ensures updateFinalisedCheckpoint(s', s).slot == s.slot == s'.slot
    {
        if get_current_epoch(s) <= GENESIS_EPOCH + 1 then 
            s
        else 
            //  The finalisation bits have been updated 
            var bits : seq<bool> := s'.justification_bits;
            var current_epoch := get_current_epoch(s');
            assert(get_current_epoch(s') == get_current_epoch(s));

            if (all(bits[1..4]) && current_epoch >= 3 && s.previous_justified_checkpoint.epoch  == current_epoch - 3) then 
                //  H1
                //  The 2nd/3rd/4th most recent epochs are justified, the 2nd using the 4th as source
                s'.(finalised_checkpoint := s.previous_justified_checkpoint) 
            else if (all(bits[1..3]) && s.previous_justified_checkpoint.epoch == current_epoch - 2) then 
                //  H2
                // The 2nd/3rd most recent epochs are justified, the 2nd using the 3rd as source
                s'.(finalised_checkpoint := s.previous_justified_checkpoint) 
            else if (false && all(bits[0..3]) && s.current_justified_checkpoint.epoch == current_epoch - 2) then 
                //  H3
                // The 1st/2nd/3rd most recent epochs are justified, the 1st using the 3rd as source
                s'.(finalised_checkpoint := s.current_justified_checkpoint) 
            else if (false && all(bits[0..2]) && s.current_justified_checkpoint.epoch == current_epoch - 1) then 
                //  H4
                // The 1st/2nd most recent epochs are justified, the 1st using the 2nd as source
                s'.(finalised_checkpoint := s.current_justified_checkpoint) 
            else
                s' 
    } 

    function updateJustificationAndFinalisation(s: BeaconState) : BeaconState
            requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0
        {
            updateFinalisedCheckpoint(updateJustification(s), s)
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