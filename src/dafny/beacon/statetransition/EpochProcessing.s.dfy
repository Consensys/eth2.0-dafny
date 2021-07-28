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

//  @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /timeLimit:100 /noCheating:0

include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../Helpers.dfy"
include "../../utils/Eth2Types.dfy"
include "../helpers/helper_lemmas/MathHelper.dfy"
include "../../utils/NativeTypes.dfy"
include "../../libraries/integers/power.i.dfy"
include "../statetransition/ProcessOperations.s.dfy"
include "../../utils/Helpers.dfy"
include "../../utils/MathHelpers.dfy"

/**
 *  Provide a functional specification of epoch processing components.
 */
module EpochProcessingSpec {
    
    //  Import some constants, types and beacon chain helpers.
    import opened Constants
    import opened BeaconChainTypes
    import opened AttestationsTypes
    import opened BeaconHelpers
    import opened Eth2Types
    import opened MathHelperLemmas
    import opened NativeTypes
    import opened Math__power_i
    import opened Math__power_s
    import opened ProcessOperationsSpec
    import opened Helpers
    import opened MathHelpers

    //  Specifications of functions related to the process epoch methods.
    //  e.g. process_rewards_and_penalties, process_slashings, etc
    //  For each process epoch method there is a corresponding functional equivalent.
    //  e.g. process_rewards_and_penalties --> updateRAndP,
    //  and in some cases there are associated helper functions
    //  e.g. updateRewardsAndPenalties is a helper to updateRAndP.
    
    /**
     *  The functional equivalent of process_epoch.
     *  
     *  @param  s       A beacon state.
     *  @returns        A new state obtained from processing the epoch updates.        
     */
    function updateEpoch(s: BeaconState): BeaconState
        //  Make sure s.slot does not overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        //  And we should only execute this method when:
        requires (s.slot + 1) % SLOTS_PER_EPOCH == 0

        requires |s.validators| == |s.balances|

        requires forall a :: a in s.previous_epoch_attestations 
                    ==> a.data.index 
                        < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) 
                        <= TWO_UP_6 
        requires forall a :: a in s.previous_epoch_attestations 
                    ==> TWO_UP_5 as nat 
                        <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| 
                        <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in s.previous_epoch_attestations 
                    ==> 0 
                        < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| 
                        <= MAX_VALIDATORS_PER_COMMITTEE as nat 
        
        ensures 
            var s1 := updateFinalisedCheckpoint(updateJustification(s), s);
            assert forall a :: a in s1.previous_epoch_attestations 
                    ==> a.data.index 
                        < get_committee_count_per_slot(s1, compute_epoch_at_slot(a.data.slot)) 
                        <= TWO_UP_6;
            assert forall a :: a in s1.previous_epoch_attestations 
                    ==> TWO_UP_5 as nat 
                        <= |get_active_validator_indices(s1.validators, compute_epoch_at_slot(a.data.slot))| 
                        <= TWO_UP_11 as nat * TWO_UP_11 as nat ;
            assert forall a :: a in s1.previous_epoch_attestations 
                    ==> 0 
                        < |get_beacon_committee(s1, a.data.slot, a.data.index)| == |a.aggregation_bits| 
                        <= MAX_VALIDATORS_PER_COMMITTEE as nat ;
            assert s1 == updateJustificationAndFinalisation(s);
            updateEpoch(s) == updateParticipationRecords(
                                updateHistoricalRoots(
                                    updateRandaoMixes(
                                        updateSlashingsReset(
                                            updateEffectiveBalance(
                                                updateEth1DataReset(
                                                    updateSlashings(
                                                        updateRAndP(
                                                            updateJustificationAndFinalisation(s)
                                                        )
                                                    )
                                                )
                                            )
                                        )
                                    )
                                )
                            )
        ensures updateEpoch(s).latest_block_header == s.latest_block_header
    {
        var s1 := updateFinalisedCheckpoint(updateJustification(s), s);
        assert s1 == updateJustificationAndFinalisation(s);
        assert s1 == updateJustification(s).(finalised_checkpoint 
                            := updateFinalisedCheckpoint(updateJustification(s), s).finalised_checkpoint);
        assert s1.previous_epoch_attestations == s.previous_epoch_attestations;
        assert s1.validators == s.validators;

        assert s.slot == s1.slot;
        assert s.balances == s1.balances;
        assert |s1.validators| == |s1.balances|;

        assert get_current_epoch(s1) == get_current_epoch(s1);
        assert forall a :: a in s1.previous_epoch_attestations 
                ==> a.data.index 
                    < get_committee_count_per_slot(s1, compute_epoch_at_slot(a.data.slot)) 
                    <= TWO_UP_6;
        assert forall a :: a in s1.previous_epoch_attestations 
                ==> TWO_UP_5 as nat 
                    <= |get_active_validator_indices(s1.validators, compute_epoch_at_slot(a.data.slot))| 
                    <= TWO_UP_11 as nat * TWO_UP_11 as nat ;
        assert forall a :: a in s1.previous_epoch_attestations 
                ==> 0 
                    < |get_beacon_committee(s1, a.data.slot, a.data.index)| == |a.aggregation_bits| 
                    <= MAX_VALIDATORS_PER_COMMITTEE as nat ;

        var s2 := updateRAndP(s1);
        assert s2 == updateRAndP(updateJustificationAndFinalisation(s));

        var s3 := s2;
        assert |s3.validators| == |s3.balances| == |s.validators|;
        var s4 := updateSlashings(s3);
        assert s4 == updateSlashings(
                        updateRAndP(
                            updateJustificationAndFinalisation(s)
                        )
                    );

        var s5 := updateEth1DataReset(s4);
        assert s5 == updateEth1DataReset(
                        updateSlashings(
                            updateRAndP(
                                updateJustificationAndFinalisation(s)
                            )
                        )
                    );

        assert |s5.validators| == |s5.balances| == |s.validators|;
        var s6 := updateEffectiveBalance(s5);
        assert s6 == updateEffectiveBalance(
                        updateEth1DataReset(
                            updateSlashings(
                                updateRAndP(
                                    updateJustificationAndFinalisation(s)
                                )
                            )
                        )
                    );

        var s7 := updateSlashingsReset(s6);
        assert s7 == updateSlashingsReset(
                        updateEffectiveBalance(
                            updateEth1DataReset(
                                updateSlashings(
                                    updateRAndP(
                                        updateJustificationAndFinalisation(s)
                                    )
                                )
                            )
                        )
                    );

        var s8 := updateRandaoMixes(s7);
        assert s8 == updateRandaoMixes(
                        updateSlashingsReset(
                            updateEffectiveBalance(
                                updateEth1DataReset(
                                    updateSlashings(
                                        updateRAndP(
                                            updateJustificationAndFinalisation(s)
                                        )
                                    )
                                )
                            )
                        )
                    );

        var s9 := updateHistoricalRoots(s8);
        assert s9 == updateHistoricalRoots(
                        updateRandaoMixes(
                            updateSlashingsReset(
                                updateEffectiveBalance(
                                    updateEth1DataReset(
                                        updateSlashings(
                                            updateRAndP(
                                                updateJustificationAndFinalisation(s)
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    );

        var s10 := updateParticipationRecords(s9);
        assert s10 == updateParticipationRecords(
                        updateHistoricalRoots(
                            updateRandaoMixes(
                                updateSlashingsReset(
                                    updateEffectiveBalance(
                                        updateEth1DataReset(
                                            updateSlashings(
                                                updateRAndP(
                                                    updateJustificationAndFinalisation(s)
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    );
        
        s10
    }

    //  Specifications of justification and finalisation of a state and forward to future slot.

    /**
     *  Archive justification results on current epoch in previous epoch's record.
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
        requires |s.validators| == |s.balances|
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0

        //  The last two bits are copied from the two middle bits of s.justification_bits
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            updateJustification(s).justification_bits[2..] == 
                (s.justification_bits)[1..|s.justification_bits| - 1]

        ensures updateJustification(s).slot == s.slot
        ensures updateJustification(s).eth1_deposit_index == s.eth1_deposit_index
        ensures updateJustification(s).validators == s.validators
        ensures updateJustification(s).balances == s.balances
        ensures |updateJustification(s).validators| == |updateJustification(s).balances|
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
     *      c) (B2, 3) (LEBB(prevEpoch(s))) if prevAttest is a supermajority and 
     *      currentAttest is not
     *
     *  The justification bits are as as follows:
     *      b' = [isSuper(currentAttest), isSuper(PrevAttest) or b0, b1, b2].
     *
     *  @note   If b0 was already true (a supermajority from some CP), then it 
     *          remains true (justified) and in that case it must have been the LJ(s).
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
     *
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
     *      H3: s.current_justified_checkpoint is at epoch - 2 (2) is 2-finalised iff:
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
     *  @note   Python array slice a[k:l] means elements from k to l - 1 [a[k] ... a[l -1]]
     */
    function updateFinalisedCheckpoint(s': BeaconState, s: BeaconState) : BeaconState
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0
        requires |s.validators| == |s.balances|
        requires s' == updateJustification(s)

        ensures updateFinalisedCheckpoint(s', s).slot == s.slot == s'.slot
        //ensures updateFinalisedCheckpoint(s', s).slot == s.slot
        ensures updateFinalisedCheckpoint(s', s).eth1_deposit_index == s.eth1_deposit_index
        ensures updateFinalisedCheckpoint(s', s).validators == s.validators == s'.validators
        ensures updateFinalisedCheckpoint(s', s).balances == s.balances == s'.balances
        ensures |updateFinalisedCheckpoint(s', s).validators| == |updateFinalisedCheckpoint(s', s).balances|
        ensures updateFinalisedCheckpoint(s', s).previous_epoch_attestations == s.previous_epoch_attestations == s'.previous_epoch_attestations
        //ensures get_previous_epoch(updateFinalisedCheckpoint(s', s)) == get_previous_epoch(s)
        ensures updateFinalisedCheckpoint(s', s) == s'.(finalised_checkpoint := updateFinalisedCheckpoint(s', s).finalised_checkpoint)
    {
        if get_current_epoch(s) <= GENESIS_EPOCH + 1 then 
            s
        else 
            //  The finalisation bits have been updated 
            var bits : seq<bool> := s'.justification_bits;
            var current_epoch := get_current_epoch(s');
            assert(get_current_epoch(s') == get_current_epoch(s));

            //  Determine next finalised checkpoint
            if (all(bits[0..2]) && s.current_justified_checkpoint.epoch == current_epoch - 1) then 
                //  H4
                // The 1st/2nd most recent epochs are justified, the 1st using the 2nd as source
                s'.(finalised_checkpoint := s.current_justified_checkpoint) 
            else if (all(bits[0..3]) && s.current_justified_checkpoint.epoch == current_epoch - 2) then 
                //  H3
                // The 1st/2nd/3rd most recent epochs are justified, the 1st using the 3rd as source
                s'.(finalised_checkpoint := s.current_justified_checkpoint) 
            else if (all(bits[1..3]) && s.previous_justified_checkpoint.epoch == current_epoch - 2) then 
                //  H2
                // The 2nd/3rd most recent epochs are justified, the 2nd using the 3rd as source
                s'.(finalised_checkpoint := s.previous_justified_checkpoint) 
            else if (all(bits[1..4]) && current_epoch >= 3 && s.previous_justified_checkpoint.epoch  == current_epoch - 3) then 
                //  H1
                //  The 2nd/3rd/4th most recent epochs are justified, the 2nd using the 4th as source
                s'.(finalised_checkpoint := s.previous_justified_checkpoint) 
            else
                s' 
    } 

    /**
     *  Combined effect of updating justification and finalisation statuses.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after updating the justification statuses, bits
     *              and finalisation statuses.
     */
    function updateJustificationAndFinalisation(s: BeaconState) : BeaconState
            requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0
            requires |s.validators| == |s.balances|
    {
        updateFinalisedCheckpoint(updateJustification(s), s)
    }

    // Specification of the remaining epoch processing components.

    /**
     *  The functional equivalent of process_rewards_and_penalties.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after applying the epoch slashings.
     *
     *  @note       This function uses assume statement as a simplification to ensure
     *              that get_previous_epoch(s) >= s.finalised_checkpoint.epoch. 
     */
    function updateRAndP(s: BeaconState): BeaconState
        requires |s.validators| == |s.balances|
        requires forall a :: a in s.previous_epoch_attestations 
                    ==> a.data.index 
                        < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) 
                        <= TWO_UP_6 
        requires forall a :: a in s.previous_epoch_attestations 
                    ==> TWO_UP_5 as nat 
                        <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| 
                        <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in s.previous_epoch_attestations 
                    ==> 0 
                        < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| 
                        <= MAX_VALIDATORS_PER_COMMITTEE as nat
        
        ensures  if get_current_epoch(s) <= GENESIS_EPOCH + 1 then updateRAndP(s) == s
                 else 
                    updateRAndP(s) == updateRewardsAndPenalties(s, 
                                                                get_attestation_deltas(s).0, 
                                                                get_attestation_deltas(s).1
                                                               )
    {
        if get_current_epoch(s) <= GENESIS_EPOCH + 1 then s
        else
            assume get_previous_epoch(s) >= s.finalised_checkpoint.epoch;
            assert EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s);
            assert 1 <= get_previous_epoch(s);
            var (rewards, penalties) := get_attestation_deltas(s);
            updateRewardsAndPenalties(s, rewards, penalties)
    }

    /**
     *  A helper function for updateSlashings.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after applying the epoch slashings.
     *
     *  @note       This function uses assume statements as a simplification to ensure
     *              that balance overflows don't occur. To remove these assume 
     *              statements a strategy similar to that applied within the deposit 
     *              processing could be applied.
     */
    function updateRewardsAndPenalties(s: BeaconState, 
                                       rewards: seq<Gwei>, 
                                       penalties: seq<Gwei>
                                      ): BeaconState
        requires |rewards| == |penalties| <= |s.validators| == |s.balances|
        
        ensures |s.balances| == |updateRewardsAndPenalties(s, rewards, penalties).balances|
        ensures |s.validators| == |updateRewardsAndPenalties(s, rewards, penalties).validators|
        ensures forall i :: |rewards| <= i < |s.balances| 
                    ==> updateRewardsAndPenalties(s, rewards, penalties).balances[i] == s.balances[i]
        ensures 
             assume forall i :: 0 <= i < |rewards| 
                    ==> s.balances[i] as nat + rewards[i] as nat < 0x10000000000000000;
             forall i :: 0 <= i < |rewards| 
                    ==> updateRewardsAndPenalties(s, rewards, penalties).balances[i] 
                        == if s.balances[i] + rewards[i] > penalties[i] 
                        then s.balances[i] + rewards[i] - penalties[i]
                        else 0 as Gwei
        ensures forall i :: 0 <= i < |s.validators| 
                    ==> updateRewardsAndPenalties(s, rewards, penalties).validators[i] == s.validators[i]
        ensures updateRewardsAndPenalties(s, rewards, penalties) 
                == s.(balances := updateRewardsAndPenalties(s, rewards, penalties).balances)

        decreases |rewards|, |penalties|
    {
        if |rewards| == 0 then s
        else
            assume forall i :: 0 <= i < |rewards| 
                ==> s.balances[i] as nat + rewards[i] as nat < 0x10000000000000000;
            var index := |rewards| - 1;
            var s1 := increase_balance(s, index as ValidatorIndex, rewards[index]);
            assert s1.balances[index] == s.balances[index] + rewards[index];

            var s2 := decrease_balance(s1, index as ValidatorIndex, penalties[index]);
            assert s2.balances[index] 
                    == if s1.balances[index] 
                    > penalties[index] then s1.balances[index] - penalties[index] else 0 as Gwei;
            assert if s.balances[index] + rewards[index] > penalties[index] 
                    then s2.balances[index] == s.balances[index] + rewards[index] - penalties[index] 
                    else s2.balances[index] == 0 as Gwei;
            updateRewardsAndPenalties(s2, rewards[..index], penalties[..index])
    }

    /**
     *  The functional equivalent of process_slashings.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after applying the epoch slashings.
     *
     *  @note       This function uses assume statements as a simplification to ensure
     *              that balance and epoch overflows don't occur. To remove these assume 
     *              statements a strategy similar to that applied within the deposit 
     *              processing could be applied.
     */
    function updateSlashings(s: BeaconState) : BeaconState
        requires |s.balances| == |s.validators|
        ensures 
            var epoch := get_current_epoch(s);
            var total_balance := get_total_active_balance_full(s);
            var sumSlashings := get_total_slashings(s.slashings);
            var adjusted_total_slashing_balance 
                := min((sumSlashings as nat * PROPORTIONAL_SLASHING_MULTIPLIER as nat) as nat, 
                        total_balance as nat
                      ) as Gwei;
            var increment := EFFECTIVE_BALANCE_INCREMENT; 
            assert total_balance > 0 as Gwei;
            assert increment > 0 as Gwei;
            assume forall v :: 0 <= v < |s.validators| 
                    ==> 0 
                        <= s.validators[v].effective_balance as nat 
                            * adjusted_total_slashing_balance as nat 
                            / total_balance  as nat
                        < 0x10000000000000000;
            assume epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2 < 0x10000000000000000;
            updateSlashings(s) == updateSlashingsHelper(s, 
                                                        |s.validators|, 
                                                        epoch, 
                                                        total_balance, 
                                                        adjusted_total_slashing_balance, 
                                                        increment
                                                       )
    {
        var epoch := get_current_epoch(s);
        var total_balance := get_total_active_balance_full(s);
        var sumSlashings := get_total_slashings(s.slashings);
        var adjusted_total_slashing_balance := min((sumSlashings as nat * PROPORTIONAL_SLASHING_MULTIPLIER as nat) as nat,
                                                    total_balance as nat
                                                  ) as Gwei;
        var increment := EFFECTIVE_BALANCE_INCREMENT; 
        assert total_balance > 0 as Gwei;
        assert increment > 0 as Gwei;
        assume forall v :: 0 <= v < |s.validators| 
                ==> 0 
                    <= s.validators[v].effective_balance as nat 
                        * adjusted_total_slashing_balance as nat 
                        / total_balance  as nat 
                    < 0x10000000000000000;
        assume epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2 < 0x10000000000000000;
        updateSlashingsHelper(s, 
                              |s.validators|, 
                              epoch, 
                              total_balance, 
                              adjusted_total_slashing_balance, 
                              increment
                             )
    }

    /**
     *  A helper function for updateSlashings.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after applying the epoch slashings.
     */
    function updateSlashingsHelper(s: BeaconState, 
                                   len: nat, 
                                   epoch: Epoch, 
                                   total_balance: Gwei, 
                                   adjusted_total_slashing_balance: Gwei, 
                                   increment: Gwei
                                   ) : BeaconState
        requires len <= |s.balances| == |s.validators| 
        requires total_balance > 0 as Gwei
        requires increment > 0 as Gwei
        requires forall v :: 0 <= v < |s.validators| 
                 ==> 0 
                    <= s.validators[v].effective_balance as nat 
                        * adjusted_total_slashing_balance as nat 
                        / total_balance  as nat 
                    < 0x10000000000000000
        requires epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2 < 0x10000000000000000;
            
        ensures |updateSlashingsHelper(s, 
                                       len, 
                                       epoch, 
                                       total_balance, 
                                       adjusted_total_slashing_balance, 
                                       increment
                                      ).validators| == |s.validators| 
        ensures |updateSlashingsHelper(s, 
                                       len, 
                                       epoch, 
                                       total_balance, 
                                       adjusted_total_slashing_balance, 
                                       increment
                                      ).balances| == |s.balances| 
        ensures forall v :: 0 <= v < |s.validators| 
                ==> updateSlashingsHelper(s, 
                                          len, 
                                          epoch, 
                                          total_balance, 
                                          adjusted_total_slashing_balance, 
                                          increment
                                         ).validators[v]  == s.validators[v]
        ensures updateSlashingsHelper(s, 
                                      len, 
                                      epoch, 
                                      total_balance, 
                                      adjusted_total_slashing_balance, 
                                      increment
                                     ) 
                    == s.(balances := updateSlashingsHelper(s, 
                                                            len, 
                                                            epoch, 
                                                            total_balance, 
                                                            adjusted_total_slashing_balance, 
                                                            increment
                                                           ).balances)
        ensures forall v :: len <= v < |s.balances| 
                ==> updateSlashingsHelper(s, 
                                          len, 
                                          epoch, 
                                          total_balance,
                                          adjusted_total_slashing_balance, 
                                          increment
                                         ).balances[v]  == s.balances[v]
        ensures forall v :: 0 <= v < len ==> 
            assert v < |s.balances|;
            var new_bal := if (s.validators[v].slashed && (epoch + EPOCHS_PER_SLASHINGS_VECTOR / 2) 
                                == s.validators[v].withdrawable_epoch)
                            then decrease_balance(s, 
                                                  v as ValidatorIndex, 
                                                  (s.validators[v].effective_balance as nat 
                                                    * adjusted_total_slashing_balance as nat 
                                                    / total_balance  as nat) as Gwei
                                                 ).balances[v]
                            else s.balances[v];
            updateSlashingsHelper(s, 
                                  len, 
                                  epoch, 
                                  total_balance, 
                                  adjusted_total_slashing_balance, 
                                  increment
                                 ).balances[v] == new_bal
       
        decreases len
    {
        if len == 0 then s
        else
            var i := len - 1;
            assert i < |s.balances|;
            var s1 := if (s.validators[i].slashed && (epoch + EPOCHS_PER_SLASHINGS_VECTOR / 2) 
                            == s.validators[i].withdrawable_epoch) 
                        then decrease_balance(s, 
                                              i as ValidatorIndex, 
                                              (s.validators[i].effective_balance as nat 
                                                * adjusted_total_slashing_balance as nat 
                                                / total_balance  as nat) as Gwei
                                             )
                        else s;                         
            assert s1.balances[i] == if (s.validators[i].slashed && (epoch + EPOCHS_PER_SLASHINGS_VECTOR / 2) 
                                        == s.validators[i].withdrawable_epoch)
                                        then decrease_balance(s, 
                                                              i as ValidatorIndex, 
                                                              (s.validators[i].effective_balance as nat 
                                                                * adjusted_total_slashing_balance as nat 
                                                                / total_balance  as nat) as Gwei
                                                             ).balances[i]
                                        else s.balances[i];
            assert forall v :: 0 <= v < i ==> s1.balances[v] == s.balances[v];
            assert forall v :: i < v < |s.balances| 
                    ==> s1.balances[v] == s.balances[v];
            assert forall v :: 0 <= v < |s.validators| 
                    ==> s1.validators[v]  == s.validators[v];
            assert |s1.balances| == |s1.validators|; 
            updateSlashingsHelper(s1, 
                                  len-1, 
                                  epoch, 
                                  total_balance, 
                                  adjusted_total_slashing_balance, 
                                  increment
                                 )
    }
    
    /**
     *  The functional equivalent of process_eth1_data_reset.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after applying the epoch eth1 data reset.
     */
    function updateEth1DataReset(s: BeaconState) : BeaconState
    {
        var next_epoch := get_current_epoch(s) + 1;
        // Reset eth1 data votes
        if (next_epoch % EPOCHS_PER_ETH1_VOTING_PERIOD) == 0 then
            s.(eth1_data_votes := [])
        else s
    }
    
    /**
     *  The functional equivalent of process_effective_balance_updates.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after applying the epoch effective balance updates.
     *  @note       This function matches to the simplified method currently being used 
     *              and should be updated to if  process_effective_balance_updates changes.
     */
    function updateEffectiveBalance(s: BeaconState) : BeaconState
    {
        s
    }
    
    /**
     *  The functional equivalent of process_slashings_reset.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after applying the epoch slashings reset.
     */
    function updateSlashingsReset(s: BeaconState) : BeaconState
    {
        var next_epoch := get_current_epoch(s) + 1;
        // Reset slashings
        s.(
            slashings := s.slashings[(next_epoch % EPOCHS_PER_SLASHINGS_VECTOR) as nat := 0 as Gwei]
        )

    }

    /**
     *  The functional equivalent of process_randao_mixes_reset.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after applying the epoch randao mixes reset.
     */
    function updateRandaoMixes(s: BeaconState) : BeaconState
    {
        var current_epoch := get_current_epoch(s);
        var next_epoch := current_epoch + 1;
        // Set randao mix
        s.(
            randao_mixes := s.randao_mixes[
                            (next_epoch % EPOCHS_PER_HISTORICAL_VECTOR) as nat 
                                := get_randao_mix(s, current_epoch)
                            ]
        )
    }
    
    /**
     *  The functional equivalent of process_historical_roots_update.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after applying the epoch historical roots update.
     */
    function updateHistoricalRoots(s: BeaconState) : BeaconState
    {
       var next_epoch := (get_current_epoch(s) + 1) as Epoch;
       if next_epoch % (SLOTS_PER_HISTORICAL_ROOT / SLOTS_PER_EPOCH) == 0 then
            var historical_batch := HistoricalBatch(s.block_roots, s.state_roots);
            s.(
                historical_roots := s.historical_roots + [hash(historical_batch)]
            )
        
        else s
    }

    /**
     *  The functional equivalent of process_participation_record_updates.
     *
     *  @param  s   A beacon state.
     *  @returns    `s` with the attestations rotated.
     */
    function updateParticipationRecords(s: BeaconState) : BeaconState
    {
        //  rotate the attestations.
        s.(
            previous_epoch_attestations := s.current_epoch_attestations,
            current_epoch_attestations := []
        )
    }

}