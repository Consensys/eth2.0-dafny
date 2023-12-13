/*
 * Copyright 2021 ConsenSys Software Inc.
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

//  @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /timeLimit:100 /noCheating:1

include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../Helpers.dfy"
include "../Helpers.p.dfy"
include "../../utils/Eth2Types.dfy"
include "../../utils/MathHelpers.dfy"
include "../../utils/NativeTypes.dfy"

/**
 *  Provide a functional specification of epoch processing components.
 */
module EpochProcessingSpec {
    
    //  Import some constants, types and beacon chain helpers.
    import opened Constants
    import opened BeaconChainTypes
    import opened AttestationsTypes
    import opened BeaconHelpers
    import opened BeaconHelperProofs
    import opened Eth2Types
    import opened MathHelpers
    import opened NativeTypes

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
        requires is_valid_state_epoch_attestations(s)
        
        ensures 
            var s1 := updateFinalisedCheckpoint(updateJustification(s), s);
            assert is_valid_state_epoch_attestations(s1);
            assert s1 == updateJustificationAndFinalisation(s);
            updateEpoch(s) == updateParticipationRecords(
                                updateHistoricalSummaries(
                                    updateRandaoMixes(
                                        updateSlashingsReset(
                                            updateEffectiveBalance(
                                                updateEth1DataReset(
                                                    updateSlashings(
                                                        updateRegistry(
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
                            )
        ensures updateEpoch(s).latest_block_header == s.latest_block_header

        ensures updateEpoch(s)
                == s.(validators := updateEpoch(s).validators,
                      balances := updateEpoch(s).balances,
                      slashings := updateEpoch(s).slashings,
                      eth1_data_votes := updateEpoch(s).eth1_data_votes,
                      randao_mixes := updateEpoch(s).randao_mixes,
                      historical_roots := updateEpoch(s).historical_roots,
                      previous_epoch_attestations := updateEpoch(s).previous_epoch_attestations,
                      current_epoch_attestations := updateEpoch(s).current_epoch_attestations,
                      current_justified_checkpoint := updateEpoch(s).current_justified_checkpoint,
                      previous_justified_checkpoint := updateEpoch(s).previous_justified_checkpoint,
                      justification_bits := updateEpoch(s).justification_bits,
                      finalised_checkpoint := updateEpoch(s).finalised_checkpoint
                     )
        ensures |updateEpoch(s).validators| == |updateEpoch(s).balances|
        ensures is_valid_state_epoch_attestations(updateEpoch(s))
        ensures |updateEpoch(s).validators| == |s.validators|
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
        assert is_valid_state_epoch_attestations(s1);

        assert get_current_epoch(s1) == get_current_epoch(s1);
        var s2 := updateRAndP(s1);
        assert s2 == updateRAndP(updateJustificationAndFinalisation(s));

        var s3 := updateRegistry(s2);
        assert s3 == updateRegistry(
                        updateRAndP(
                            updateJustificationAndFinalisation(s)
                        )
                    );
        
        assert |s3.validators| == |s3.balances| == |s.validators|;
        var s4 := updateSlashings(s3);
        assert s4 == updateSlashings(
                        updateRegistry(
                            updateRAndP(
                                updateJustificationAndFinalisation(s)
                            )
                        )
                    );

        var s5 := updateEth1DataReset(s4);
        assert s5 == updateEth1DataReset(
                        updateSlashings(
                            updateRegistry(
                                updateRAndP(
                                    updateJustificationAndFinalisation(s)
                                )
                            )
                        )
                    );

        assert |s5.validators| == |s5.balances| == |s.validators|;
        var s6 := updateEffectiveBalance(s5);
        assert s6 == updateEffectiveBalance(
                        updateEth1DataReset(
                            updateSlashings(
                                updateRegistry(
                                    updateRAndP(
                                        updateJustificationAndFinalisation(s)
                                    )
                                )
                            )
                        )
                    );

        var s7 := updateSlashingsReset(s6);
        assert s7 == updateSlashingsReset(
                        updateEffectiveBalance(
                            updateEth1DataReset(
                                updateSlashings(
                                    updateRegistry(
                                        updateRAndP(
                                            updateJustificationAndFinalisation(s)
                                        )
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
                                        updateRegistry(
                                            updateRAndP(
                                                updateJustificationAndFinalisation(s)
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    );

        var s9 := updateHistoricalSummaries(s8);
        assert s9 == updateHistoricalSummaries(
                        updateRandaoMixes(
                            updateSlashingsReset(
                                updateEffectiveBalance(
                                    updateEth1DataReset(
                                        updateSlashings(
                                            updateRegistry(
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

        var s10 := updateParticipationRecords(s9);
        assert s10 == updateParticipationRecords(
                        updateHistoricalSummaries(
                            updateRandaoMixes(
                                updateSlashingsReset(
                                    updateEffectiveBalance(
                                        updateEth1DataReset(
                                            updateSlashings(
                                                updateRegistry(
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
        requires |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)

        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            updateJustificationPrevEpoch(s).justification_bits[2..] == 
                (s.justification_bits)[1..|s.justification_bits| - 1]
            && updateJustificationPrevEpoch(s).justification_bits[0] == false
        
        ensures updateJustificationPrevEpoch(s).slot == s.slot
        ensures updateJustificationPrevEpoch(s).eth1_deposit_index == s.eth1_deposit_index
        ensures updateJustificationPrevEpoch(s).validators == s.validators
        ensures updateJustificationPrevEpoch(s).balances == s.balances
        ensures |updateJustificationPrevEpoch(s).validators| == |updateJustificationPrevEpoch(s).balances|
        ensures updateJustificationPrevEpoch(s).previous_epoch_attestations == s.previous_epoch_attestations 
        ensures updateJustificationPrevEpoch(s).current_epoch_attestations == s.current_epoch_attestations

        ensures updateJustificationPrevEpoch(s)
                == s.(current_justified_checkpoint := updateJustificationPrevEpoch(s).current_justified_checkpoint,
                      previous_justified_checkpoint := updateJustificationPrevEpoch(s).previous_justified_checkpoint,
                      justification_bits := updateJustificationPrevEpoch(s).justification_bits
                )
        ensures is_valid_state_epoch_attestations(updateJustificationPrevEpoch(s))
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
        requires |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)

        /** Only bit 0 can be modified, and it should be false initially.
         */
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            updateJustificationCurrentEpoch(s).justification_bits[1..] == 
                (s.justification_bits)[1..|s.justification_bits|]
        
        ensures updateJustificationCurrentEpoch(s).slot == s.slot
        ensures updateJustificationCurrentEpoch(s).eth1_deposit_index 
                == s.eth1_deposit_index
        ensures updateJustificationCurrentEpoch(s).validators == s.validators
        ensures updateJustificationCurrentEpoch(s).balances == s.balances
        ensures |updateJustificationCurrentEpoch(s).validators| 
                == |updateJustificationCurrentEpoch(s).balances|
        ensures updateJustificationCurrentEpoch(s).previous_epoch_attestations 
                == s.previous_epoch_attestations 
        ensures updateJustificationCurrentEpoch(s).current_epoch_attestations 
                == s.current_epoch_attestations

        ensures updateJustificationCurrentEpoch(s)
                == s.(current_justified_checkpoint := updateJustificationCurrentEpoch(s).current_justified_checkpoint,
                      justification_bits := updateJustificationCurrentEpoch(s).justification_bits
                )
        ensures is_valid_state_epoch_attestations(updateJustificationCurrentEpoch(s))
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
        requires is_valid_state_epoch_attestations(s)

        //  The last two bits are copied from the two middle bits of s.justification_bits
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            updateJustification(s).justification_bits[2..] == 
                (s.justification_bits)[1..|s.justification_bits| - 1]

        ensures updateJustification(s).slot == s.slot
        ensures updateJustification(s).eth1_deposit_index == s.eth1_deposit_index
        ensures updateJustification(s).validators == s.validators
        ensures updateJustification(s).balances == s.balances
        ensures |updateJustification(s).validators| == |updateJustification(s).balances|
        ensures updateJustification(s).previous_epoch_attestations 
                == s.previous_epoch_attestations 
        ensures updateJustification(s).current_epoch_attestations 
                == s.current_epoch_attestations 
        
        ensures updateJustification(s)
                == s.(current_justified_checkpoint := updateJustification(s).current_justified_checkpoint,
                      previous_justified_checkpoint := updateJustification(s).previous_justified_checkpoint,
                      justification_bits := updateJustification(s).justification_bits,
                      finalised_checkpoint := updateJustification(s).finalised_checkpoint
                     )
        ensures is_valid_state_epoch_attestations(updateJustification(s))
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
        requires is_valid_state_epoch_attestations(s)
        requires s' == updateJustification(s)

        ensures updateFinalisedCheckpoint(s', s).slot == s.slot == s'.slot
        ensures updateFinalisedCheckpoint(s', s).eth1_deposit_index == s.eth1_deposit_index
        ensures updateFinalisedCheckpoint(s', s).validators == s.validators == s'.validators
        ensures updateFinalisedCheckpoint(s', s).balances == s.balances == s'.balances
        ensures |updateFinalisedCheckpoint(s', s).validators| 
                == |updateFinalisedCheckpoint(s', s).balances|
        ensures updateFinalisedCheckpoint(s', s).previous_epoch_attestations 
                == s.previous_epoch_attestations 
                == s'.previous_epoch_attestations
        ensures updateFinalisedCheckpoint(s', s).current_epoch_attestations 
                == s.current_epoch_attestations 
                == s'.current_epoch_attestations
        //ensures get_previous_epoch(updateFinalisedCheckpoint(s', s)) == get_previous_epoch(s)
        
        ensures updateFinalisedCheckpoint(s', s) 
                == s'.(finalised_checkpoint := updateFinalisedCheckpoint(s', s).finalised_checkpoint)
        ensures is_valid_state_epoch_attestations(updateFinalisedCheckpoint(s', s))
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
        requires is_valid_state_epoch_attestations(s)

        ensures updateJustificationAndFinalisation(s)
                == s.(current_justified_checkpoint := updateJustificationAndFinalisation(s).current_justified_checkpoint,
                      previous_justified_checkpoint := updateJustificationAndFinalisation(s).previous_justified_checkpoint,
                      justification_bits := updateJustificationAndFinalisation(s).justification_bits,
                      finalised_checkpoint := updateJustificationAndFinalisation(s).finalised_checkpoint
                     )
        ensures is_valid_state_epoch_attestations(updateJustificationAndFinalisation(s))       
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
     *  @note       This function uses axiom AssumeNoGweiOverflowToAddRewards.
     *  @note       This axiom is used as a simplification to ensure that balance 
     *              overflows don't occur. To remove this axiom a strategy similar
     *              to that applied within the deposit processing could be applied.       
     */
    function updateRAndP(s: BeaconState): BeaconState
        requires |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)
         
        ensures updateRAndP(s)
                == s.(validators := updateRAndP(s).validators,
                      balances := updateRAndP(s).balances)
        ensures is_valid_state_epoch_attestations(updateRAndP(s))
    {
        if get_current_epoch(s) <= GENESIS_EPOCH + 1 then s
        else
            var (rewards, penalties) := get_attestation_deltas(s);
            AssumeNoGweiOverflowToAddRewards(s, rewards);
            assert forall i :: 0 <= i < |rewards| 
                     ==> s.balances[i] as nat + rewards[i] as nat < 0x10000000000000000;
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
        requires is_valid_state_epoch_attestations(s)
        requires forall i :: 0 <= i < |rewards| 
                     ==> s.balances[i] as nat + rewards[i] as nat < 0x10000000000000000;
        
        ensures |s.balances| == |updateRewardsAndPenalties(s, rewards, penalties).balances|
        ensures |s.validators| == |updateRewardsAndPenalties(s, rewards, penalties).validators|
        ensures forall i :: |rewards| <= i < |s.balances| 
                    ==> updateRewardsAndPenalties(s, rewards, penalties).balances[i] == s.balances[i]
        ensures 
            forall i :: 0 <= i < |rewards| 
                    ==> 
                        updateRewardsAndPenalties(s, rewards, penalties).balances[i] 
                        == if s.balances[i] + rewards[i] > penalties[i] 
                        then s.balances[i] + rewards[i] - penalties[i]
                        else 0 as Gwei
        ensures forall i :: 0 <= i < |s.validators| 
                    ==> updateRewardsAndPenalties(s, rewards, penalties).validators[i] == s.validators[i]
        ensures updateRewardsAndPenalties(s, rewards, penalties) 
                == s.(balances := updateRewardsAndPenalties(s, rewards, penalties).balances)

        ensures updateRewardsAndPenalties(s, rewards, penalties) 
                == s.(validators := updateRewardsAndPenalties(s, rewards, penalties).validators,
                      balances := updateRewardsAndPenalties(s, rewards, penalties).balances)
        ensures is_valid_state_epoch_attestations(updateRewardsAndPenalties(s, rewards, penalties))

        decreases |rewards|, |penalties|
    {
        if |rewards| == 0 then s
        else
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
     *  The functional equivalent of process_registry_updates.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after applying the epoch registy updates.
     *  @note       This function matches to the simplified method currently being used 
     *              and should be updated to if process_registry_updates changes.
     *              i.e the activation queue within updateQueueValidators is not 
     *              sorted. Please refer to process_queue_validators and updateQueueValidators.
     *  @note       This component uses the axiom AssumeMinimumActiveValidators.
     */
    function updateRegistry(s: BeaconState) : BeaconState
        requires |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)

        ensures is_valid_state_epoch_attestations(updateRegistry(s))   
        ensures updateRegistry(s) 
                == s.(validators := updateRegistry(s).validators)
    {
        var s1 := updateActivationEligibility(s);
        AssumeMinimumActiveValidators(s1);
        var s2 := updateEjections(s1);
        updateQueueValidators(s2)
    }

    /** 
     *  A helper to process the first component of the registry updates.
     *  
     *  @param  s   A state.
     *  @returns    The state obtained after applying the activation eligibility updates
     */
    function updateActivationEligibility(s: BeaconState) : BeaconState
        requires |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)

        ensures updateActivationEligibility(s) 
                == s.(validators := updateActivationEligibility(s).validators)
        ensures is_valid_state_epoch_attestations(updateActivationEligibility(s))
    {
        updateActivationEligibilityHelper(s, |s.validators|)
    }

    /** 
     *  A helper to process the first component of the registry updates recursively.
     *  
     *  @param  s   A state.
     *  @param  len A positive integer.
     *  @returns    The state obtained after applying the activation eligibility updates
     */
    function updateActivationEligibilityHelper(s: BeaconState, len: nat) : BeaconState
        requires len <= |s.balances| == |s.validators| 
        requires is_valid_state_epoch_attestations(s)
            
        ensures |updateActivationEligibilityHelper(s,len).validators| == |s.validators|  
        ensures |updateActivationEligibilityHelper(s, len).balances| == |s.balances| 
        ensures forall v :: len <= v < |s.validators| 
                ==> updateActivationEligibilityHelper(s,len).validators[v]  == s.validators[v]
        ensures forall v :: 0 <= v < len ==> 
            assert v < |s.validators|;
            var new_val := if is_eligible_for_activation_queue(s.validators[v])
                        then 
                            set_activation_eligibility_epoch(s, 
                                                             v as ValidatorIndex, 
                                                             get_current_epoch(s) + 1 as Epoch
                                                            ).validators[v] 
                        else 
                            s.validators[v]; 
            updateActivationEligibilityHelper(s,len).validators[v] == new_val
       
        ensures updateActivationEligibilityHelper(s, len) 
                == s.(validators := updateActivationEligibilityHelper(s, len).validators)
        ensures is_valid_state_epoch_attestations(updateActivationEligibilityHelper(s,len))

        decreases len
    {
        if len == 0 then s

        else
            var i := len - 1;
            assert i < |s.balances|;
            
            var s1 := if is_eligible_for_activation_queue(s.validators[i])
                        then 
                            set_activation_eligibility_epoch(s, 
                                                             i as ValidatorIndex, 
                                                             get_current_epoch(s) + 1 as Epoch
                                                            ) 
                        else 
                            s; 

            AssumeIsValidStateEpoch_Attestations(s1);
            updateActivationEligibilityHelper(s1, len-1)
    }

    /** 
     *  A helper to process the second component of the registry updates.
     *  
     *  @param  s   A state.
     *  @returns    The state obtained after applying the ejection updates
     */
    function updateEjections(s: BeaconState) : BeaconState
        requires |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)
        requires minimumActiveValidators(s)

        ensures updateEjections(s) 
                == s.(validators := updateEjections(s).validators)
        ensures is_valid_state_epoch_attestations(updateEjections(s))
    {
        updateEjectionsHelper(s, |s.validators|)
    }

    /** 
     *  A helper to process the second component of the registry updates recursively.
     *  
     *  @param  s   A state.
     *  @param  len A positive integer.
     *  @returns    The state obtained after applying the ejection updates
     */
    function updateEjectionsHelper(s: BeaconState, len: nat) : BeaconState
        requires len <= |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)
        requires minimumActiveValidators(s)
            
        ensures |updateEjectionsHelper(s,len).validators| == |s.validators|  
        ensures |updateEjectionsHelper(s,len).balances| == |s.balances| 
        ensures forall v :: len <= v < |s.validators| 
                ==> updateEjectionsHelper(s,len).validators[v]  == s.validators[v]
       
        ensures updateEjectionsHelper(s, len) 
                == s.(validators := updateEjectionsHelper(s, len).validators)
        ensures is_valid_state_epoch_attestations(updateEjectionsHelper(s,len))
        ensures minimumActiveValidators(updateEjectionsHelper(s,len))

        decreases len
    {
        if len == 0 then s

        else
            var i := len - 1;
            var s1 := updateEjectionsHelper(s, i); 
            
            assert i < |s.validators|;
        
            var s2 := if ((is_active_validator(s1.validators[i], get_current_epoch(s1)))
                        && (s1.validators[i].effective_balance <= EJECTION_BALANCE))
                            then    
                                initiate_validator_exit(s1, i as ValidatorIndex)
                            else
                                s1;
            AssumeIsValidStateEpoch_Attestations(s2);
            s2
    }

    /** 
     *  A helper to process the final component of the registry updates.
     *  
     *  @param  s   A state.
     *  @returns    The state obtained after applying the dequeue updates
     */
    function updateQueueValidators(s: BeaconState) : BeaconState
        requires |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)

        ensures updateQueueValidators(s) 
                == s.(validators := updateQueueValidators(s).validators)
        ensures is_valid_state_epoch_attestations(updateQueueValidators(s))
    {
        var activation_queue := get_validator_indices_activation_eligible(s.validators, s.finalised_checkpoint.epoch); 
        var churn_limit := get_validator_churn_limit(s) as nat;

        var dequeue := if churn_limit <= |activation_queue| 
                        then activation_queue[..churn_limit]
                        else [];
            
        updateQueueValidatorsHelper(s, dequeue, |s.validators|)
    }

    /** 
     *  A helper to process the final component of the registry updates recursively.
     *  
     *  @param  s           A state.
     *  @param  dequeue     A sequence of indices.
     *  @param  len         A positive integer.
     *  @returns    The state obtained after applying the dequeue updates
     */
    function updateQueueValidatorsHelper(s: BeaconState, dequeue: seq<uint64>, len: nat) : BeaconState
        requires len <= |s.balances| == |s.validators| 
        requires is_valid_state_epoch_attestations(s)
            
        ensures |updateQueueValidatorsHelper(s,dequeue, len).validators| == |s.validators|  
        ensures |updateQueueValidatorsHelper(s,dequeue, len).balances| == |s.balances| 
        ensures forall v :: len <= v < |s.validators| 
                ==> updateQueueValidatorsHelper(s,dequeue, len).validators[v]  == s.validators[v]
        ensures forall v :: 0 <= v < len ==> 
            assert v < |s.validators|;
            var new_val := if v as uint64 in dequeue
                        then 
                            set_activation_epoch(s, 
                                                 v as ValidatorIndex, 
                                                 compute_activation_exit_epoch(get_current_epoch(s))
                                                ).validators[v] 
                        else 
                            s.validators[v]; 
            updateQueueValidatorsHelper(s,dequeue, len).validators[v] == new_val
       
        ensures updateQueueValidatorsHelper(s,dequeue, len)
                == s.(validators := updateQueueValidatorsHelper(s,dequeue, len).validators)
        ensures is_valid_state_epoch_attestations(updateQueueValidatorsHelper(s,dequeue, len))

        decreases len
    {
        if len == 0 then s

        else
            var i := len - 1;
            assert i < |s.balances|;
            
            var s1 := if i as uint64 in dequeue
                        then 
                            set_activation_epoch(s, 
                                                i as ValidatorIndex, 
                                                compute_activation_exit_epoch(get_current_epoch(s))
                                                ) 
                        else 
                            s; 

            AssumeIsValidStateEpoch_Attestations(s1);
            updateQueueValidatorsHelper(s1,dequeue, len-1)
    }

    /**
     *  The functional equivalent of process_slashings.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after applying the epoch slashings.
     *
     *  @note       This function uses axiom AssumeNoEpochOverflow and 
     *              AssumeNoGweiOverflowToUpdateSlashings.
     *  @note       These axioms are used as a simplification to ensure that balance 
     *              overflows don't occur. To remove this axiom a strategy similar
     *              to that applied within the deposit processing could be applied. 
     */
    function updateSlashings(s: BeaconState) : BeaconState
        requires |s.balances| == |s.validators|
        requires is_valid_state_epoch_attestations(s)
        
        ensures updateSlashings(s) == s.(balances := updateSlashings(s).balances)
        ensures is_valid_state_epoch_attestations(updateSlashings(s))
    {
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
        
        AssumeNoGweiOverflowToUpdateSlashings(s.validators, 
                                              adjusted_total_slashing_balance as nat, 
                                              total_balance as nat);
        assert forall v :: 0 <= v < |s.validators| 
                ==> 0 <= s.validators[v].effective_balance as nat 
                        * adjusted_total_slashing_balance as nat 
                        / total_balance  as nat 
                    < 0x10000000000000000;
        AssumeNoEpochOverflow(epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2);
        assert epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2 < 0x10000000000000000;
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
                 ==> 0<= s.validators[v].effective_balance as nat 
                        * adjusted_total_slashing_balance as nat 
                        / total_balance  as nat 
                    < 0x10000000000000000
        requires epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2 < 0x10000000000000000;
        requires is_valid_state_epoch_attestations(s)
            
        ensures 
            var updatedState := updateSlashingsHelper(s, 
                                                    len, 
                                                    epoch, 
                                                    total_balance, 
                                                    adjusted_total_slashing_balance, 
                                                    increment
                                                    );
            |updatedState.validators| == |s.validators| 
            && |updatedState.balances| == |s.balances| 
            && (forall v :: 0 <= v < |s.validators| 
                ==> updatedState.validators[v]  == s.validators[v])
            && updatedState == s.(balances := updatedState.balances)
            && (forall v :: len <= v < |s.balances| 
                ==> updatedState.balances[v]  == s.balances[v])
            && is_valid_state_epoch_attestations(updatedState)
            && updatedState == s.(balances := updatedState.balances)
            
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
        requires is_valid_state_epoch_attestations(s)

        ensures updateEth1DataReset(s) 
                == s.(eth1_data_votes := updateEth1DataReset(s).eth1_data_votes)
        ensures is_valid_state_epoch_attestations(updateEth1DataReset(s))
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
     *
     *  @note       This function uses axiom AssumeNoGweiOverflowToUpdateEffectiveBalance.
     *  @note       This axiom is used as a simplification to ensure that balance 
     *              overflows don't occur. To remove this axiom a strategy similar
     *              to that applied within the deposit processing could be applied.  
     */
    function updateEffectiveBalance(s: BeaconState) : BeaconState
        requires |s.validators| == |s.balances|
        requires is_valid_state_epoch_attestations(s)

        ensures updateEffectiveBalance(s) 
                == s.(validators := updateEffectiveBalance(s).validators)
        ensures is_valid_state_epoch_attestations(updateEffectiveBalance(s))
    {
        AssumeNoGweiOverflowToUpdateEffectiveBalance(s.balances);

        var HYSTERESIS_INCREMENT := EFFECTIVE_BALANCE_INCREMENT / HYSTERESIS_QUOTIENT;
        var DOWNWARD_THRESHOLD := HYSTERESIS_INCREMENT * HYSTERESIS_DOWNWARD_MULTIPLIER;
        var UPWARD_THRESHOLD := HYSTERESIS_INCREMENT * HYSTERESIS_UPWARD_MULTIPLIER;
        updateEffectiveBalanceHelper(s, |s.validators|, UPWARD_THRESHOLD as nat, DOWNWARD_THRESHOLD as nat)
    }

    /**
     *  A helper function for updateEffectiveBalance.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after applying the effective balance updates.
     *
     *  @note       This function uses axiom AssumeIsValidStateEpoch_Attestations.
     */
    function updateEffectiveBalanceHelper(s: BeaconState, len: nat, up: nat, down: nat) : BeaconState
        requires len <= |s.balances| == |s.validators| 
        requires is_valid_state_epoch_attestations(s)
        requires forall v :: 0 <= v < |s.validators| 
                 ==> min((s.balances[v] - s.balances[v] % EFFECTIVE_BALANCE_INCREMENT) as nat, MAX_EFFECTIVE_BALANCE as nat) as nat 
                < 0x10000000000000000
            
        ensures |updateEffectiveBalanceHelper(s,len, up, down).validators| == |s.validators|  
        ensures |updateEffectiveBalanceHelper(s, len, up, down).balances| == |s.balances| 
        ensures updateEffectiveBalanceHelper(s, len, up, down).balances == s.balances
        ensures forall v :: len <= v < |s.validators| 
                ==> updateEffectiveBalanceHelper(s,len, up, down).validators[v]  == s.validators[v]
        ensures forall v :: 0 <= v < len ==> 
            assert v < |s.validators|;
            var new_val := if (s.balances[v] as nat + down < s.validators[v].effective_balance as nat) 
                        || (s.validators[v].effective_balance as nat + up < s.balances[v] as nat)
                        then 
                            set_effective_balance(s, 
                                                  v as ValidatorIndex, 
                                                  min((s.balances[v] - s.balances[v] % EFFECTIVE_BALANCE_INCREMENT) as nat, 
                                                      MAX_EFFECTIVE_BALANCE as nat) as Gwei
                                                  ).validators[v] 
                        else 
                            s.validators[v]; 
            updateEffectiveBalanceHelper(s,len, up, down).validators[v] == new_val
       
        ensures updateEffectiveBalanceHelper(s, len, up, down) 
                == s.(validators := updateEffectiveBalanceHelper(s, len, up, down).validators)
        ensures is_valid_state_epoch_attestations(updateEffectiveBalanceHelper(s,len, up, down))

        decreases len
    {
        if len == 0 then s

        else
            var i := len - 1;
            assert i < |s.balances|;
            
            var s1 := if (s.balances[i] as nat + down < s.validators[i].effective_balance as nat) 
                        || (s.validators[i].effective_balance as nat + up < s.balances[i] as nat)
                        then 
                            var new_bal 
                                := min((s.balances[i] - s.balances[i] % EFFECTIVE_BALANCE_INCREMENT) as nat, 
                                        MAX_EFFECTIVE_BALANCE as nat);
                            set_effective_balance(s, i as ValidatorIndex, new_bal as Gwei)
                        else s;   

            assert s1.validators[i] 
                    == if (s.balances[i] as nat + down < s.validators[i].effective_balance as nat) 
                        || (s.validators[i].effective_balance as nat + up < s.balances[i] as nat)
                        then 
                            set_effective_balance(s, 
                                                  i as ValidatorIndex, 
                                                  min((s.balances[i] - s.balances[i] % EFFECTIVE_BALANCE_INCREMENT) as nat, 
                                                      MAX_EFFECTIVE_BALANCE as nat) as Gwei
                                                  ).validators[i] 
                        else 
                            s.validators[i];
            AssumeIsValidStateEpoch_Attestations(s1);
            updateEffectiveBalanceHelper(s1, len-1, up, down)
    }
    
    /**
     *  The functional equivalent of process_slashings_reset.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after applying the epoch slashings reset.
     */
    function updateSlashingsReset(s: BeaconState) : BeaconState
        requires is_valid_state_epoch_attestations(s)

        ensures updateSlashingsReset(s) 
                == s.(slashings := updateSlashingsReset(s).slashings)
        ensures is_valid_state_epoch_attestations(updateSlashingsReset(s))
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
        requires is_valid_state_epoch_attestations(s)

        ensures updateRandaoMixes(s) 
                == s.(randao_mixes := updateRandaoMixes(s).randao_mixes)
        ensures is_valid_state_epoch_attestations(updateRandaoMixes(s))
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
    
    // /**
    //  *  The functional equivalent of process_historical_roots_update.
    //  *
    //  *  @param  s   A beacon state.
    //  *  @returns    The state obtained after applying the epoch historical roots update.
    //  */
    // function updateHistoricalRoots(s: BeaconState) : BeaconState
    //     requires is_valid_state_epoch_attestations(s)

    //     ensures updateHistoricalRoots(s) 
    //             == s.(historical_roots := updateHistoricalRoots(s).historical_roots)
    //     ensures is_valid_state_epoch_attestations(updateHistoricalRoots(s))
    // {
    //    var next_epoch := (get_current_epoch(s) + 1) as Epoch;
    //    if next_epoch % (SLOTS_PER_HISTORICAL_ROOT / SLOTS_PER_EPOCH) == 0 then
    //         var historical_batch := HistoricalBatch(s.block_roots, s.state_roots);
    //         s.(
    //             historical_roots := s.historical_roots + [hash(historical_batch)]
    //         )
        
    //     else s
    // }


    function updateHistoricalSummaries(s: BeaconState) : BeaconState
        requires is_valid_state_epoch_attestations(s)

        ensures updateHistoricalSummaries(s)
                == s.(historical_summaries := updateHistoricalSummaries(s).historical_summaries)
        ensures is_valid_state_epoch_attestations(updateHistoricalSummaries(s))
    {
        var next_epoch := (get_current_epoch(s) + 1) as Epoch;
        if next_epoch % (SLOTS_PER_HISTORICAL_ROOT / SLOTS_PER_EPOCH) == 0 then
            var historical_summary := HistoricalSummary(s.block_roots, s.state_roots);
            s.(
                historical_summaries := s.historical_summaries + [(historical_summary)]
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
        requires is_valid_state_epoch_attestations(s)

        ensures updateParticipationRecords(s) 
                == s.(previous_epoch_attestations := updateParticipationRecords(s).previous_epoch_attestations,
                     current_epoch_attestations := updateParticipationRecords(s).current_epoch_attestations
                     )
        ensures is_valid_state_epoch_attestations(updateParticipationRecords(s))
    {
        //  rotate the attestations.
        s.(
            previous_epoch_attestations := s.current_epoch_attestations,
            current_epoch_attestations := []
        )
    }

}