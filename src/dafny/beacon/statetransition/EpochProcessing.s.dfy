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
include "../../utils/Eth2Types.dfy"
include "../helpers/helper_lemmas/MathHelper.dfy"
include "../../utils/NativeTypes.dfy"
include "../../libraries/integers/power.i.dfy"
include "../statetransition/ProcessOperations.s.dfy"
include "../../utils/Helpers.dfy"
include "../../utils/MathHelpers.dfy"
include "../validators/ValidatorHelpers.dfy"


/**
 *  Provide a functional specification of Epoch processing.
 */
module EpochProcessingSpec {
    
    //  Import some constants, types and beacon chain helpers.
    import opened Constants
    import opened BeaconChainTypes
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened BeaconHelpers
    import opened Eth2Types
    import opened MathHelperLemmas
    import opened NativeTypes
    import opened Math__power_i
    import opened Math__power_s
    import opened ProcessOperationsSpec
    import opened Helpers
    import opened MathHelpers
    import opened ValidatorHelpers
    
    function updateEpoch(s: BeaconState): BeaconState
    //  Make sure s.slot does not overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        //  And we should only execute this method when:
        requires (s.slot + 1) % SLOTS_PER_EPOCH == 0

        requires |s.validators| == |s.balances|

        requires forall a :: a in s.previous_epoch_attestations ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6 
        requires forall a :: a in s.previous_epoch_attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in s.previous_epoch_attestations ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
        
        ensures 
            var s1 := updateFinalisedCheckpoint(updateJustification(s), s);
            assert forall a :: a in s1.previous_epoch_attestations ==> a.data.index < get_committee_count_per_slot(s1, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6;
            assert forall a :: a in s1.previous_epoch_attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s1.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat ;
            assert forall a :: a in s1.previous_epoch_attestations ==> 0 < |get_beacon_committee(s1, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat ;
            assert s1 == updateJustificationAndFinalisation(s);
            //assert updateEpoch(s) == updateRAndP(s1);
            //updateEpoch(s) == updateRAndP(updateFinalisedCheckpoint(updateJustification(s), s))
            updateEpoch(s) == updateParticipationRecords(updateHistoricalRoots(updateRandaoMixes(updateSlashingsReset(updateEffectiveBalance(updateEth1DataReset(updateSlashings(updateRAndP(updateJustificationAndFinalisation(s)))))))))
        ensures updateEpoch(s).latest_block_header == s.latest_block_header
    {
        var s1 := updateFinalisedCheckpoint(updateJustification(s), s);
        assert s1 == updateJustificationAndFinalisation(s);
        assert s1 == updateJustification(s).(finalised_checkpoint := updateFinalisedCheckpoint(updateJustification(s), s).finalised_checkpoint);
        assert s1.previous_epoch_attestations == s.previous_epoch_attestations;
        assert s1.validators == s.validators;

        assert s.slot == s1.slot;
        assert s.balances == s1.balances;
        assert |s1.validators| == |s1.balances|;

        assert get_current_epoch(s1) == get_current_epoch(s1);
            
        //assert forall a :: a in s1.previous_epoch_attestations ==> get_committee_count_per_slot(s1, compute_epoch_at_slot(a.data.slot)) == get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot));
        //assert forall a :: a in s1.previous_epoch_attestations ==> |get_beacon_committee(s1, a.data.slot, a.data.index)| == |get_beacon_committee(s, a.data.slot, a.data.index)| ;
        
        assert forall a :: a in s1.previous_epoch_attestations ==> a.data.index < get_committee_count_per_slot(s1, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6;
        assert forall a :: a in s1.previous_epoch_attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s1.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat ;
        assert forall a :: a in s1.previous_epoch_attestations ==> 0 < |get_beacon_committee(s1, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat ;

        var s2 := updateRAndP(s1);
        assert s2 == updateRAndP(updateJustificationAndFinalisation(s));

        // process_registry_updates(state)
        var s3 := s2;

        assert |s3.validators| == |s3.balances| == |s.validators|;
        var s4 := updateSlashings(s3);
        assert s4 == updateSlashings(updateRAndP(updateJustificationAndFinalisation(s)));

        var s5 := updateEth1DataReset(s4);
        assert s5 == updateEth1DataReset(updateSlashings(updateRAndP(updateJustificationAndFinalisation(s))));

        assert |s5.validators| == |s5.balances| == |s.validators|;
        var s6 := updateEffectiveBalance(s5);
        assert s6 == updateEffectiveBalance(updateEth1DataReset(updateSlashings(updateRAndP(updateJustificationAndFinalisation(s)))));

        var s7 := updateSlashingsReset(s6);
        assert s7 == updateSlashingsReset(updateEffectiveBalance(updateEth1DataReset(updateSlashings(updateRAndP(updateJustificationAndFinalisation(s))))));

        var s8 := updateRandaoMixes(s7);
        assert s8 == updateRandaoMixes(updateSlashingsReset(updateEffectiveBalance(updateEth1DataReset(updateSlashings(updateRAndP(updateJustificationAndFinalisation(s)))))));

        var s9 := updateHistoricalRoots(s8);
        assert s9 == updateHistoricalRoots(updateRandaoMixes(updateSlashingsReset(updateEffectiveBalance(updateEth1DataReset(updateSlashings(updateRAndP(updateJustificationAndFinalisation(s))))))));

        var s10 := updateParticipationRecords(s9);
        assert s10 == updateParticipationRecords(updateHistoricalRoots(updateRandaoMixes(updateSlashingsReset(updateEffectiveBalance(updateEth1DataReset(updateSlashings(updateRAndP(updateJustificationAndFinalisation(s)))))))));
        
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

    function updateRAndP(s: BeaconState): BeaconState
        requires |s.validators| == |s.balances|
        //requires if get_current_epoch(s) > GENESIS_EPOCH + 1 then  get_previous_epoch(s) >= s.finalised_checkpoint.epoch else true
        //requires if get_current_epoch(s) > GENESIS_EPOCH + 1 then  EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s) else true
        //requires if get_current_epoch(s) > GENESIS_EPOCH + 1 then  1 <= get_previous_epoch(s) else true // <= get_current_epoch(s)
        
        requires forall a :: a in s.previous_epoch_attestations ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6 
        requires forall a :: a in s.previous_epoch_attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in s.previous_epoch_attestations ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat
        
        ensures     if get_current_epoch(s) <= GENESIS_EPOCH + 1 then updateRAndP(s) == s
                    else 
                        updateRAndP(s) == updateRewardsAndPenalties(s, get_attestation_deltas(s).0, get_attestation_deltas(s).1)
    {
        if get_current_epoch(s) <= GENESIS_EPOCH + 1 then s
        else
            RAndPHelperLemma(s);
            assert EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s);
            assert 1 <= get_previous_epoch(s);
            var (rewards, penalties) := get_attestation_deltas(s);
            updateRewardsAndPenalties(s, rewards, penalties)

    }

    lemma RAndPHelperLemma(s: BeaconState)
        ensures get_previous_epoch(s) >= s.finalised_checkpoint.epoch


    function updateRewardsAndPenalties(s: BeaconState, rewards: seq<Gwei>, penalties: seq<Gwei>): BeaconState
        requires |rewards| == |penalties| <= |s.validators| == |s.balances|
        //requires forall i :: 0 <= i < |rewards| ==> s.balances[i] as nat + rewards[i] as nat < 0x10000000000000000
        
        ensures |s.balances| == |updateRewardsAndPenalties(s, rewards, penalties).balances|
        ensures |s.validators| == |updateRewardsAndPenalties(s, rewards, penalties).validators|
        ensures forall i :: |rewards| <= i < |s.balances| ==> updateRewardsAndPenalties(s, rewards, penalties).balances[i] == s.balances[i]
        ensures 
             assume forall i :: 0 <= i < |rewards| ==> s.balances[i] as nat + rewards[i] as nat < 0x10000000000000000;
             forall i :: 0 <= i < |rewards| ==> updateRewardsAndPenalties(s, rewards, penalties).balances[i] == if s.balances[i] + rewards[i] > penalties[i] then 
                                                        s.balances[i] + rewards[i] - penalties[i]
                                                    else    
                                                        0 as Gwei
        ensures forall i :: 0 <= i < |s.validators| ==> updateRewardsAndPenalties(s, rewards, penalties).validators[i] == s.validators[i]
        ensures updateRewardsAndPenalties(s, rewards, penalties) == s.(balances := updateRewardsAndPenalties(s, rewards, penalties).balances)

        decreases |rewards|, |penalties|
    {
        if |rewards| == 0 then s
        else
            assume forall i :: 0 <= i < |rewards| ==> s.balances[i] as nat + rewards[i] as nat < 0x10000000000000000;
            var index := |rewards| - 1;
            // var s' := if rewards[|rewards|-1] > penalties[|penalties|-1] then 
            //                 //assume s.balances[index] as nat + rewards[|rewards|-1] as nat - penalties[|penalties|-1] as nat < 0x10000000000000000;
            //                 increase_balance(s, index as ValidatorIndex, rewards[|rewards|-1] - penalties[|penalties|-1])
            //             else 
            //                 //assume s.balances[index] as nat + penalties[|penalties|-1] as nat - rewards[|rewards|-1] as nat < 0x10000000000000000;
            //                 decrease_balance(s, index as ValidatorIndex, penalties[|penalties|-1] - rewards[|rewards|-1]);
            var s1 := increase_balance(s, index as ValidatorIndex, rewards[index]);
            assert s1.balances[index] == s.balances[index] + rewards[index];

            var s2 := decrease_balance(s1, index as ValidatorIndex, penalties[index]);
            assert s2.balances[index] == if s1.balances[index] > penalties[index] then s1.balances[index] - penalties[index] else 0 as Gwei;
            assert if s.balances[index] + rewards[index] > penalties[index] then s2.balances[index] == s.balances[index] + rewards[index] - penalties[index] 
                                                                         else s2.balances[index] == 0 as Gwei;

            //updateRewardsAndPenaltiesLemma(s, rewards, penalties);
            updateRewardsAndPenalties(s2, rewards[..index], penalties[..index])
            //s.(balances := increase_balance(s,get_validator_index(pk, d.data.pubkey),d.data.amount).balances)
    }



    function method get_total_slashings(slashings: seq<Gwei>): Gwei
    {
        if |slashings| == 0 then 0 as Gwei
        else 
            assume slashings[0] as nat + get_total_slashings(slashings[1..]) as nat < 0x10000000000000000;
            slashings[0] + get_total_slashings(slashings[1..])
    }

    function updateSlashings(s: BeaconState) : BeaconState
        requires |s.balances| == |s.validators|
        ensures 
            var epoch := get_current_epoch(s);
            var total_balance := get_total_active_balance_full(s);
            var sumSlashings := get_total_slashings(s.slashings);
            var adjusted_total_slashing_balance := min((sumSlashings as nat * PROPORTIONAL_SLASHING_MULTIPLIER as nat) as nat, total_balance as nat) as Gwei;
            var increment := EFFECTIVE_BALANCE_INCREMENT; 
            assert total_balance > 0 as Gwei;
            assert increment > 0 as Gwei;
            assume forall v :: 0 <= v < |s.validators| ==> 0 <= s.validators[v].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat < 0x10000000000000000;
            assume epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2 < 0x10000000000000000;
            updateSlashings(s) == updateSlashingsHelper(s, |s.validators|, epoch, total_balance, adjusted_total_slashing_balance, increment)
    {
        var epoch := get_current_epoch(s);
        var total_balance := get_total_active_balance_full(s);
        var sumSlashings := get_total_slashings(s.slashings);
        var adjusted_total_slashing_balance := min((sumSlashings as nat * PROPORTIONAL_SLASHING_MULTIPLIER as nat) as nat, total_balance as nat) as Gwei;
        var increment := EFFECTIVE_BALANCE_INCREMENT; 
        
        assert total_balance > 0 as Gwei;
        assert increment > 0 as Gwei;
        assume forall v :: 0 <= v < |s.validators| ==> 0 <= s.validators[v].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat < 0x10000000000000000;
        assume epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2 < 0x10000000000000000;
         
        updateSlashingsHelper(s, |s.validators|, epoch, total_balance, adjusted_total_slashing_balance, increment)
        
    }

    function updateSlashingsHelper(s: BeaconState, len: nat, epoch: Epoch, total_balance: Gwei, adjusted_total_slashing_balance: Gwei, increment: Gwei) : BeaconState
        requires len <= |s.balances| == |s.validators| 
        requires total_balance > 0 as Gwei
        requires increment > 0 as Gwei
        requires forall v :: 0 <= v < |s.validators| ==> 0 <= s.validators[v].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat < 0x10000000000000000
        requires epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2 < 0x10000000000000000;
            

        ensures |updateSlashingsHelper(s, len, epoch, total_balance, adjusted_total_slashing_balance, increment).validators| == |s.validators| 
        ensures |updateSlashingsHelper(s, len, epoch, total_balance, adjusted_total_slashing_balance, increment).balances| == |s.balances| 
        
        ensures forall v :: 0 <= v < |s.validators| ==> updateSlashingsHelper(s, len, epoch, total_balance, adjusted_total_slashing_balance, increment).validators[v]  == s.validators[v]
        //ensures forall v :: 0 <= v < |s.validators| ==> updateSlashingsHelper(s, len, epoch, total_balance, adjusted_total_slashing_balance, increment).validators[v].effective_balance  == s.validators[v].effective_balance
        ensures updateSlashingsHelper(s, len, epoch, total_balance, adjusted_total_slashing_balance, increment) == s.(balances := updateSlashingsHelper(s, len, epoch, total_balance, adjusted_total_slashing_balance, increment).balances)
        ensures forall v :: len <= v < |s.balances| ==> updateSlashingsHelper(s, len, epoch, total_balance, adjusted_total_slashing_balance, increment).balances[v]  == s.balances[v]

        ensures forall v :: 0 <= v < len ==> 
        
            // var penalty_numerator := s.validators[v].effective_balance as nat / increment as nat * adjusted_total_slashing_balance as nat;
            // var penalty := penalty_numerator / total_balance  as nat * increment as nat;
            //var penalty := s.validators[v].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat;
            
            //assume 0 <= s.validators[v].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat < 0x10000000000000000;
            //assume epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2 < 0x10000000000000000;
            assert v < |s.balances|;

            var new_bal := if (s.validators[v].slashed && (epoch + EPOCHS_PER_SLASHINGS_VECTOR / 2) == s.validators[v].withdrawable_epoch)
                                    // then if s.balances[v] > penalty as Gwei then s.balances[v] - penalty as Gwei
                                    //                                                 else 0 as Gwei
                                    then decrease_balance(s, v as ValidatorIndex, (s.validators[v].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat) as Gwei).balances[v]
                                    else s.balances[v];
            updateSlashingsHelper(s, len, epoch, total_balance, adjusted_total_slashing_balance, increment).balances[v] == new_bal
       
        
        decreases len
    {
        if len == 0 then s
        else
            var i := len - 1;

            assert i < |s.balances|;
            
            //var penalty_numerator := s.validators[i].effective_balance as nat / increment as nat * adjusted_total_slashing_balance as nat;
            //var penalty := penalty_numerator  / total_balance  as nat * increment as nat;
            //var penalty := s.validators[i].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat;
            
            //assume 0 <= penalty < 0x10000000000000000;
            //assume 0 <= s.validators[i].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat < 0x10000000000000000;
            
            //assume epoch as nat + EPOCHS_PER_SLASHINGS_VECTOR as nat / 2 < 0x10000000000000000;
            
            var s1 := if (s.validators[i].slashed && (epoch + EPOCHS_PER_SLASHINGS_VECTOR / 2) == s.validators[i].withdrawable_epoch) 
                    then decrease_balance(s, i as ValidatorIndex, (s.validators[i].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat) as Gwei)
                    else s;

            // var new_bal := if (s.validators[i].slashed && (epoch + EPOCHS_PER_SLASHINGS_VECTOR / 2) == s.validators[i].withdrawable_epoch)
            //                             // then if s.balances[i] > penalty as Gwei then s.balances[i] - penalty as Gwei
            //                             //                                                 else 0 as Gwei
            //                             then decrease_balance(s, i as ValidatorIndex, penalty as Gwei).balances[i]
            //                             else s.balances[i];
                                        
            assert s1.balances[i] == if (s.validators[i].slashed && (epoch + EPOCHS_PER_SLASHINGS_VECTOR / 2) == s.validators[i].withdrawable_epoch)
                                        // then if s.balances[i] > penalty as Gwei then s.balances[i] - penalty as Gwei
                                        //                                                 else 0 as Gwei
                                        then decrease_balance(s, i as ValidatorIndex, (s.validators[i].effective_balance as nat * adjusted_total_slashing_balance as nat / total_balance  as nat) as Gwei).balances[i]
                                        else s.balances[i];
            assert forall v :: 0 <= v < i ==> s1.balances[v] == s.balances[v];
            assert forall v :: i < v < |s.balances| ==> s1.balances[v] == s.balances[v];
            //assert forall v :: i < v < |s.validators| ==> s1.validators[v] == s.validators[v];
            assert forall v :: 0 <= v < |s.validators| ==> s1.validators[v]  == s.validators[v];
            assert |s1.balances| == |s1.validators|; 
            updateSlashingsHelper(s1, len-1, epoch, total_balance, adjusted_total_slashing_balance, increment)

    }


    
    function updateEth1DataReset(s: BeaconState) : BeaconState
    {
        var next_epoch := get_current_epoch(s) + 1;
        // Reset eth1 data votes
        if (next_epoch % EPOCHS_PER_ETH1_VOTING_PERIOD) == 0 then
            s.(eth1_data_votes := [])
        else s
    }
    
    function updateEffectiveBalance(s: BeaconState) : BeaconState
    {
        s
    }

    
    
    
    function updateSlashingsReset(s: BeaconState) : BeaconState
    {
        var next_epoch := get_current_epoch(s) + 1;
        // Reset slashings
        s.(
            slashings := s.slashings[(next_epoch % EPOCHS_PER_SLASHINGS_VECTOR) as nat := 0 as Gwei]
        )

    }

    function updateRandaoMixes(s: BeaconState) : BeaconState
    {
        var current_epoch := get_current_epoch(s);
        var next_epoch := current_epoch + 1;
        // Set randao mix
        // state.randao_mixes[next_epoch % EPOCHS_PER_HISTORICAL_VECTOR] = get_randao_mix(s, current_epoch)
        s.(
            randao_mixes := s.randao_mixes[(next_epoch % EPOCHS_PER_HISTORICAL_VECTOR) as nat := get_randao_mix(s, current_epoch)]
        )
    }
    
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
     *  Final section of process_final_updates where attestations are rotated.
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

    

    
    // Helpers - Rewards and penalties

    function method integer_square_root(n:uint64) : uint64
        requires n < 0xFFFFFFFFFFFFFFFF;
        ensures power(integer_square_root(n) as nat,2) <= n as nat;
        //ensures !(exists x' {:trigger power(x' as nat,2)} :: x'>x && power(x' as nat,2) <= n as nat)
    
    function method get_base_reward(s: BeaconState, index: ValidatorIndex) : Gwei
        requires index as int < |s.validators|
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires s.validators[index].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000
    {
        var total_balance : Gwei := get_total_active_balance_full(s);
        var effective_balance : Gwei := s.validators[index].effective_balance;

        (EFFECTIVE_BALANCE_INCREMENT as int * BASE_REWARD_FACTOR as int / integer_square_root(total_balance) as int) as Gwei 
    }

    function method get_proposer_reward(state: BeaconState, attesting_index: ValidatorIndex): Gwei
        requires attesting_index as int < |state.validators|
        requires get_total_active_balance_full(state) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(state)) > 1
        requires state.validators[attesting_index].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(state)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000
    {
        (get_base_reward(state, attesting_index) / PROPOSER_REWARD_QUOTIENT) as Gwei  
    }
    
    function method get_finality_delay(state: BeaconState): uint64
        requires get_previous_epoch(state) >= state.finalised_checkpoint.epoch
    {
        get_previous_epoch(state) - state.finalised_checkpoint.epoch
    }
     
    predicate method is_in_inactivity_leak(state: BeaconState)
        requires get_previous_epoch(state) >= state.finalised_checkpoint.epoch
    {
        get_finality_delay(state) > MIN_EPOCHS_TO_INACTIVITY_PENALTY
    }
    
    function method get_eligible_validator_indices(state: BeaconState): seq<ValidatorIndex>
        ensures forall i :: 0 <= i < |get_eligible_validator_indices(state)|  
            ==> get_eligible_validator_indices(state)[i] as nat < |state.validators|
    {
        var previous_epoch := get_previous_epoch(state);
        get_eligible_validator_indices_helper(state.validators, previous_epoch)
        //     return [
        //         ValidatorIndex(index) for index, v in enumerate(state.validators)
        //         if is_active_validator(v, previous_epoch) or (v.slashed and previous_epoch + 1 < v.withdrawable_epoch)
        //     ]
    }

    function method get_eligible_validator_indices_helper(v: ListOfValidators, previous_epoch: Epoch): seq<ValidatorIndex>
        ensures forall i :: 0 <= i < |get_eligible_validator_indices_helper(v, previous_epoch)|  
            ==> get_eligible_validator_indices_helper(v, previous_epoch)[i] as nat < |v|
    {
        if |v| == 0 then []
        else 
            if is_active_validator(v[|v|-1], previous_epoch) || (v[|v|-1].slashed && (previous_epoch as int + 1 < v[|v|-1].withdrawable_epoch as int)) then
                get_eligible_validator_indices_helper(v[..|v|-1], previous_epoch) + [(|v|-1) as ValidatorIndex]
            else 
                get_eligible_validator_indices_helper(v[..|v|-1], previous_epoch)
    }

    //datatype RewardsAndPenalties = rewardsAndPenalties(rewards: seq<Gwei>, penalties: seq<Gwei>)

    /** Helper with shared logic for use by get source, target, and head deltas functions */

    //Components of attestation deltas

    // Return attester micro-rewards/penalties for source-vote for each validator.
    function method get_source_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s)

        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        ensures |get_source_deltas(s).0| == |get_source_deltas(s).1| == |s.validators|
    {
        var matching_source_attestations := get_matching_source_attestations(s, get_previous_epoch(s));

        get_attestation_component_deltas(s, matching_source_attestations)
    }

    // Return attester micro-rewards/penalties for target-vote for each validator.
    function method get_target_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        requires get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat
        //requires s.slot - get_previous_epoch(s) *  SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT  // equivalent to above requires

        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s)
        requires 1 <= get_previous_epoch(s) <= get_current_epoch(s)

        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        ensures |get_target_deltas(s).0| == |get_target_deltas(s).1| == |s.validators|
    {
        var matching_target_attestations := get_matching_target_attestations(s, get_previous_epoch(s));

        get_attestation_component_deltas(s, matching_target_attestations)
    }


    // def get_head_deltas(state: BeaconState) -> Tuple[Sequence[Gwei], Sequence[Gwei]]:
    // """
    // Return attester micro-rewards/penalties for head-vote for each validator.
    // """
    // matching_head_attestations = get_matching_head_attestations(state, get_previous_epoch(state))
    // return get_attestation_component_deltas(state, matching_head_attestations)
    function method get_head_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        requires get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat
        //requires s.slot - get_previous_epoch(s) *  SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT  // equivalent to above requires
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s)
        requires 1 <= get_previous_epoch(s) <= get_current_epoch(s)

        requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        ensures |get_head_deltas(s).0| == |get_head_deltas(s).1| == |s.validators|
    {
        var matching_head_attestations := get_matching_head_attestations(s, get_previous_epoch(s));
        get_attestation_component_deltas(s, matching_head_attestations)
    }

    // def get_inclusion_delay_deltas(state: BeaconState) -> Tuple[Sequence[Gwei], Sequence[Gwei]]:
    // """
    // Return proposer and inclusion delay micro-rewards/penalties for each validator.
    // """
    // rewards = [Gwei(0) for _ in range(len(state.validators))]
    // matching_source_attestations = get_matching_source_attestations(state, get_previous_epoch(state))

    // for index in get_unslashed_attesting_indices(state, matching_source_attestations):
    //     attestation = min([
    //         a for a in matching_source_attestations
    //         if index in get_attesting_indices(state, a.data, a.aggregation_bits)
    //     ], key=lambda a: a.inclusion_delay)
    //     rewards[attestation.proposer_index] += get_proposer_reward(state, index)
    //     max_attester_reward = Gwei(get_base_reward(state, index) - get_proposer_reward(state, index))
    //     rewards[index] += Gwei(max_attester_reward // attestation.inclusion_delay)

    // # No penalties associated with inclusion delay
    // penalties = [Gwei(0) for _ in range(len(state.validators))]
    // return rewards, penalties

    function method get_inclusion_delay_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1

        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
        
        ensures |get_inclusion_delay_deltas(s).0| == |get_inclusion_delay_deltas(s).1| == |s.validators|
    {
        var rewards : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var penalties : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);

        var matching_source_attestations := get_matching_source_attestations(s, get_previous_epoch(s));
        var unslashed_attesting_indices := get_unslashed_attesting_indices(s, matching_source_attestations);

        // resolve the following assume at a later date i.e. look at the bound for effectBalance as part of the proof required
        assume forall i :: i in unslashed_attesting_indices ==> s.validators[i].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000;
  
        get_inclusion_delay_deltas_helper(s, unslashed_attesting_indices, matching_source_attestations, rewards, penalties)

    }

    function method get_inclusion_delay_deltas_helper(s: BeaconState, unslashed_attesting_indices: set<ValidatorIndex>, matching_source_attestations: seq<PendingAttestation>, rewards: seq<Gwei>, penalties: seq<Gwei>) : (seq<Gwei>,seq<Gwei>)
        requires |rewards| == |penalties| == |s.validators|
        requires forall i :: i in unslashed_attesting_indices ==> i as int < |s.validators|
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires forall i :: i in unslashed_attesting_indices ==> 
                s.validators[i as nat].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000

        ensures |get_inclusion_delay_deltas_helper(s, unslashed_attesting_indices, matching_source_attestations, rewards, penalties).0| == |rewards| == |s.validators|
        ensures |get_inclusion_delay_deltas_helper(s, unslashed_attesting_indices, matching_source_attestations, rewards, penalties).1| == |penalties| == |s.validators|
    
    {
        if unslashed_attesting_indices == {} then (rewards, penalties)
        else
            var index := PickIndex(unslashed_attesting_indices);
            var attestation := get_min_attestation(matching_source_attestations, index);
            assume attestation.proposer_index as nat < |rewards|;
            assume (rewards[attestation.proposer_index as nat] as nat + get_proposer_reward(s, index) as nat) < 0x10000000000000000; 
            var rewards' := rewards[attestation.proposer_index as nat := (rewards[attestation.proposer_index as nat] as nat + get_proposer_reward(s, index) as nat) as Gwei];
            var penalties' := penalties;
            
            assume get_base_reward(s, index) > get_proposer_reward(s, index);
            // or set to 0
            var max_attester_reward := get_base_reward(s, index) - get_proposer_reward(s, index);
            assume attestation.inclusion_delay > 0;
            assume (rewards'[index as nat] as nat + max_attester_reward as nat / attestation.inclusion_delay as nat) < 0x10000000000000000;

            assert |rewards'| == |rewards|;
            assert |penalties'| == |penalties|;
            get_inclusion_delay_deltas_helper(s, unslashed_attesting_indices - {index}, matching_source_attestations, rewards'[index as nat := (rewards'[index as nat] as nat
                                            + max_attester_reward as nat / attestation.inclusion_delay as nat) as Gwei], penalties)

    }

    function method get_min_attestation(sa : seq<PendingAttestation>, index: ValidatorIndex) : PendingAttestation
        

    // def get_inactivity_penalty_deltas(state: BeaconState) -> Tuple[Sequence[Gwei], Sequence[Gwei]]:
    // """
    
    // """
    // penalties = [Gwei(0) for _ in range(len(state.validators))]
    // if is_in_inactivity_leak(state):
    //     matching_target_attestations = get_matching_target_attestations(state, get_previous_epoch(state))
    //     matching_target_attesting_indices = get_unslashed_attesting_indices(state, matching_target_attestations)
    //     for index in get_eligible_validator_indices(state):
    //         # If validator is performing optimally this cancels all rewards for a neutral balance
    //         base_reward = get_base_reward(state, index)
    //         penalties[index] += Gwei(BASE_REWARDS_PER_EPOCH * base_reward - get_proposer_reward(state, index))
    //         if index not in matching_target_attesting_indices:
    //             effective_balance = state.validators[index].effective_balance
    //             penalties[index] += Gwei(effective_balance * get_finality_delay(state) // INACTIVITY_PENALTY_QUOTIENT)

    // # No rewards associated with inactivity penalties
    // rewards = [Gwei(0) for _ in range(len(state.validators))]
    // return rewards, penalties

    // Return inactivity reward/penalty deltas for each validator.
    function method get_inactivity_penalty_deltas(s: BeaconState) : (seq<Gwei>,seq<Gwei>)
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        requires get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat
        requires s.slot - get_previous_epoch(s) *  SLOTS_PER_EPOCH <=  SLOTS_PER_HISTORICAL_ROOT 
        requires 1 <= get_previous_epoch(s) <= get_current_epoch(s)
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1

        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
        
        ensures |get_inactivity_penalty_deltas(s).0| == |get_inactivity_penalty_deltas(s).1| == |s.validators|
    {
        var rewards : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var penalties : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);

        if (is_in_inactivity_leak(s)) then
            var matching_target_attestations := get_matching_target_attestations(s, get_previous_epoch(s));
            var matching_target_attesting_indices := get_unslashed_attesting_indices(s, matching_target_attestations);
            var eligible_validator_indices := get_eligible_validator_indices(s);
            assert forall i :: 0 <= i < |eligible_validator_indices| ==> eligible_validator_indices[i] as nat < |s.validators|;
        
            assume forall i :: 0 <= i < |eligible_validator_indices| ==> s.validators[eligible_validator_indices[i] as nat].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000;
   
            get_inactivity_penalty_deltas_helper(s, eligible_validator_indices, matching_target_attesting_indices, rewards, penalties)
        else    
            (rewards,penalties)
        
    }

    function method get_inactivity_penalty_deltas_helper(s: BeaconState, 
                                                    eligible_indices: seq<ValidatorIndex>, 
                                                    target_indices: set<ValidatorIndex>,
                                                    rewards: seq<Gwei>,
                                                    penalties: seq<Gwei>)  
                                                : (seq<Gwei>,seq<Gwei>)
        requires |rewards| == |penalties| == |s.validators|
        requires forall i :: 0 <= i < |eligible_indices| ==> eligible_indices[i] as nat < |s.validators|
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires forall i :: 0 <= i < |eligible_indices| ==> s.validators[eligible_indices[i] as nat].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch

         ensures |get_inactivity_penalty_deltas_helper(s, eligible_indices, target_indices, rewards, penalties).0| == |rewards| == |s.validators|
        ensures |get_inactivity_penalty_deltas_helper(s, eligible_indices, target_indices, rewards, penalties).1| == |penalties| == |s.validators|
    {
        if |eligible_indices| == 0 then (rewards, penalties)
        else
            var base_reward := get_base_reward(s,eligible_indices[0]);
            var first_part_of_penalty := (BASE_REWARDS_PER_EPOCH * base_reward - get_proposer_reward(s, eligible_indices[0])) as Gwei;

            var rewards' := rewards;
            assert |rewards'| == |rewards|;
            

            if eligible_indices[0] !in target_indices then
                var effective_balance := s.validators[eligible_indices[0] as nat].effective_balance;
                assume INACTIVITY_PENALTY_QUOTIENT as nat > 0;
                assume (effective_balance as nat * get_finality_delay(s) as nat / INACTIVITY_PENALTY_QUOTIENT as nat) < 0x10000000000000000;
                var second_part_of_penalty := (effective_balance as nat * get_finality_delay(s) as nat / INACTIVITY_PENALTY_QUOTIENT as nat) as Gwei;
                
                assume (penalties[eligible_indices[0] as nat] as nat + first_part_of_penalty as nat + second_part_of_penalty as nat) < 0x10000000000000000;
                var penalties' := penalties[eligible_indices[0] as nat := (penalties[eligible_indices[0] as nat] as nat + first_part_of_penalty as nat + second_part_of_penalty as nat) as Gwei];
                assert |penalties'| == |penalties|;

                get_inactivity_penalty_deltas_helper(s, eligible_indices[1..], target_indices, rewards', penalties')
            else
                assume penalties[eligible_indices[0] as nat] as nat + first_part_of_penalty as nat < 0x10000000000000000;
                var penalties' := penalties[eligible_indices[0] as nat := (penalties[eligible_indices[0] as nat] as nat + first_part_of_penalty as nat) as Gwei];
                assert |penalties'| == |penalties|;
                get_inactivity_penalty_deltas_helper(s, eligible_indices[1..], target_indices, rewards', penalties')
            
    }


    
    // Helper with shared logic for use by get source, target, and head deltas functions
    function method get_attestation_component_deltas(s: BeaconState, attestations: seq<PendingAttestation>) : (seq<Gwei>,seq<Gwei>)
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s) 

        requires forall a :: a in attestations ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in attestations ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 

        ensures |get_attestation_component_deltas(s, attestations).0| == |get_attestation_component_deltas(s, attestations).1| == |s.validators|
        
    {
        var rewards : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var penalties : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var total_balance := get_total_active_balance_full(s);
        var unslashed_attesting_indices := get_unslashed_attesting_indices(s, attestations);
        var attesting_balance := get_total_balance(s, unslashed_attesting_indices);
        var indices := get_eligible_validator_indices(s);

        assert forall i :: 0 <= i < |indices| ==> indices[i] as nat < |s.validators|;

        // resolve the following assume at a later date i.e. look at the bound for effectBalance as part of the proof required
        assume forall i :: 0 <= i < |indices| ==> s.validators[indices[i]].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000;
  
        
        get_attestation_component_deltas_helper(s, indices, total_balance, unslashed_attesting_indices, attesting_balance, rewards, penalties)
        
    }

    function method get_attestation_component_deltas_helper(s: BeaconState, 
                                                    indices: seq<ValidatorIndex>, 
                                                    total_balance: Gwei,
                                                    unslashed_attesting_indices: set<ValidatorIndex>,
                                                    attesting_balance: Gwei,
                                                    rewards: seq<Gwei>,
                                                    penalties: seq<Gwei>)  
                                                : (seq<Gwei>,seq<Gwei>)
        requires |rewards| == |penalties| == |s.validators|
        requires EFFECTIVE_BALANCE_INCREMENT <= total_balance 
        requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        requires forall i :: 0 <= i < |indices| ==> indices[i] as nat < |s.validators|
        requires get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF 
        requires integer_square_root(get_total_active_balance_full(s)) > 1
        requires forall i :: 0 <= i < |indices| ==> s.validators[indices[i]].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000
     
        ensures |get_attestation_component_deltas_helper(s, indices, total_balance, unslashed_attesting_indices, attesting_balance, rewards, penalties).0| == |rewards| == |s.validators|
        ensures |get_attestation_component_deltas_helper(s, indices, total_balance, unslashed_attesting_indices, attesting_balance, rewards, penalties).1| == |penalties| == |s.validators|
    {
        if |indices| == 0 then (rewards, penalties)
        else
            var index := indices[0];
            assert index as nat < |s.validators|;
            assert integer_square_root(get_total_active_balance_full(s)) > 1;
            assert s.validators[index].effective_balance as int * BASE_REWARD_FACTOR as int / integer_square_root(get_total_active_balance_full(s)) as int / BASE_REWARDS_PER_EPOCH as int < 0x10000000000000000;

            if index in unslashed_attesting_indices then
                var increment := EFFECTIVE_BALANCE_INCREMENT;
                var rewards_numerator :=  get_base_reward(s, index) as nat * (attesting_balance as nat / increment as nat); // this is moved above the else branch to faciliate the related assume statement

                assert (total_balance as nat / increment as nat) >= 1;
                // resolve the following assume at a later date i.e. look at the bounds for each component
                assume rewards_numerator > 0;
                assume rewards[index as nat] as nat + get_base_reward(s, index) as nat < 0x10000000000000000;
                assume rewards[index as nat] as nat + rewards_numerator / (total_balance as nat / increment as nat) < 0x10000000000000000;
                
                if is_in_inactivity_leak(s) then   
                    //(rewards[indices[0] := rewards[indices[0]] + get_base_reward(s, indices[0])], penalties)
                    get_attestation_component_deltas_helper(s, indices[1..], total_balance, unslashed_attesting_indices, attesting_balance, rewards[index as nat := (rewards[index as nat] as nat + get_base_reward(s, index) as nat) as Gwei], penalties)
                else
                    //  var rewards_numerator :=  get_base_reward(s, index) * (attesting_balance / increment); 
                    //(rewards[indices[0] := rewards[indices[0]] + rewards_numerator / (total_balance / increment)], penalties)
                    get_attestation_component_deltas_helper(s, indices[1..], total_balance, unslashed_attesting_indices, attesting_balance, rewards[index as nat := (rewards[index as nat] as nat + rewards_numerator / (total_balance as nat / increment as nat)) as Gwei], penalties)
            else
                // resolve the following assume at a later date i.e. look at the bounds for each component
                assume penalties[index as nat] as nat + get_base_reward(s, index) as nat < 0x10000000000000000;

                //(rewards, penalties[indices[0] := penalties[indices[0]] + get_base_reward(s, indices[0])])
                get_attestation_component_deltas_helper(s, indices[1..], total_balance, unslashed_attesting_indices, attesting_balance, rewards, penalties[index as nat := (penalties[index as nat] as nat + get_base_reward(s, index) as nat) as Gwei])

    }
    
    
    // def get_attestation_deltas(state: BeaconState) -> Tuple[Sequence[Gwei], Sequence[Gwei]]:
    // """
    // Return attestation reward/penalty deltas for each validator.
    // """
    // source_rewards, source_penalties = get_source_deltas(state)
    // target_rewards, target_penalties = get_target_deltas(state)
    // head_rewards, head_penalties = get_head_deltas(state)
    // inclusion_delay_rewards, _ = get_inclusion_delay_deltas(state)
    // _, inactivity_penalties = get_inactivity_penalty_deltas(state)

    // rewards = [
    //     source_rewards[i] + target_rewards[i] + head_rewards[i] + inclusion_delay_rewards[i]
    //     for i in range(len(state.validators))
    // ]

    // penalties = [
    //     source_penalties[i] + target_penalties[i] + head_penalties[i] + inactivity_penalties[i]
    //     for i in range(len(state.validators))
    // ]

    // return rewards, penalties
    function method get_attestation_deltas(s: BeaconState) : (seq<Gwei>, seq<Gwei>)
        //requires get_previous_epoch(s) >= s.finalised_checkpoint.epoch
        //requires integer_square_root(get_total_active_balance_full(s)) > 1
        //requires get_total_active_balance_full(s) > 1
        //requires EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s)

        //requires get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat
        requires 1 <= get_previous_epoch(s) //<= get_current_epoch(s)
        // i.e. this means it isn't applicable to the GENESIS_EPOCH

        requires forall a :: a in s.previous_epoch_attestations ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        requires forall a :: a in s.previous_epoch_attestations ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        requires forall a :: a in s.previous_epoch_attestations ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 


        // requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        // requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        // requires forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        // requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        // requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        // requires forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        // requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6
        // requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat 
        // requires forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat 
    
        ensures |get_attestation_deltas(s).0| == |get_attestation_deltas(s).1| == |s.validators|
    {
        //assert forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> a in s.previous_epoch_attestations;
        // assert forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6;
        // assert forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat; 
        // assert forall a :: a in get_matching_source_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat ;
    
        // assert forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6;
        // assert forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat ;
        // assert forall a :: a in get_matching_target_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat; 
    
        // assert forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> a.data.index < get_committee_count_per_slot(s, compute_epoch_at_slot(a.data.slot)) <= TWO_UP_6;
        // assert forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> TWO_UP_5 as nat <= |get_active_validator_indices(s.validators, compute_epoch_at_slot(a.data.slot))| <= TWO_UP_11 as nat * TWO_UP_11 as nat ;
        // assert forall a :: a in get_matching_head_attestations(s, get_previous_epoch(s)) ==> 0 < |get_beacon_committee(s, a.data.slot, a.data.index)| == |a.aggregation_bits| <= MAX_VALIDATORS_PER_COMMITTEE as nat ;
    
        
        var rewards : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        var penalties : seq<Gwei> := timeSeq<Gwei>(0,|s.validators|);
        
        RAndPHelperLemma(s);
        assert get_previous_epoch(s) >= s.finalised_checkpoint.epoch;
        assert EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s);

        assume get_total_active_balance_full(s) < 0xFFFFFFFFFFFFFFFF;
        assume integer_square_root(get_total_active_balance_full(s)) > 1; // ie as EFFECTIVE_BALANCE_INCREMENT <= get_total_active_balance_full(s)
        assert get_previous_epoch(s) as nat *  SLOTS_PER_EPOCH as nat  <  s.slot as nat;
        
        var (sr, sp) := get_source_deltas(s);
        var (tr, tp) := get_target_deltas(s);
        var (hr, hp) := get_head_deltas(s);
        var (ddr, ddp) := get_inclusion_delay_deltas(s);
        var (pdr, pdp) := get_inactivity_penalty_deltas(s);

        assert |sr| == |tr| == |hr| == |ddr| == |pdr| == |s.validators|;
        assert |sp| == |tp| == |hp| == |ddp| == |pdp| == |s.validators|;

        (get_attestation_deltas_helper_sum_rewards(sr, tr, hr, ddr, pdr, rewards),
         get_attestation_deltas_helper_sum_penalties(sp, tp, hp, ddp, pdp, penalties))

    }

    function method get_attestation_deltas_helper_sum_rewards(sr: seq<Gwei>, tr: seq<Gwei>, hr: seq<Gwei>, ddr: seq<Gwei>, pdr: seq<Gwei>, rewards: seq<Gwei>) : seq<Gwei>
        requires |sr| == |tr| == |hr| == |ddr| == |pdr| <= |rewards|
        ensures |get_attestation_deltas_helper_sum_rewards(sr, tr, hr, ddr, pdr, rewards)| == |rewards|
    {
        if |sr| == 0 then rewards
        else    
            assume rewards[0] as nat + sr[0] as nat + tr[0] as nat + hr[0] as nat + ddr[0] as nat + pdr[0] as nat < 0x10000000000000000;
            get_attestation_deltas_helper_sum_rewards(sr[1..], tr[1..], hr[1..], ddr[1..], pdr[1..], rewards[0 := rewards[0] + sr[0] + tr[0] + hr[0] + ddr[0] + pdr[0]])
    }

    function method get_attestation_deltas_helper_sum_penalties(sp: seq<Gwei>, tp: seq<Gwei>, hp: seq<Gwei>, ddp: seq<Gwei>, pdp: seq<Gwei>, penalties: seq<Gwei>) : seq<Gwei>
        requires |sp| == |tp| == |hp| == |ddp| == |pdp| <= |penalties|
        ensures |get_attestation_deltas_helper_sum_penalties(sp, tp, hp, ddp, pdp, penalties)| == |penalties|
    {
        if |sp| == 0 then penalties
        else    
            assume penalties[0] as nat + sp[0] as nat + tp[0] as nat + hp[0] as nat + ddp[0] as nat + pdp[0] as nat  < 0x10000000000000000;
            get_attestation_deltas_helper_sum_penalties(sp[1..], tp[1..], hp[1..], ddp[1..], pdp[1..], penalties[0 := penalties[0] + sp[0] + tp[0] + hp[0] + ddp[0] + pdp[0]])
    }


    /////////////////////////

    // lemma individualBalanceBoundMaintained(sb: seq<Gwei>, d: Deposit)
    //     requires total_balances(sb) + d.data.amount as int < 0x10000000000000000
    //     ensures forall i :: 0 <= i < |sb| ==> sb[i] as int + d.data.amount as int < 0x10000000000000000
    // {
    //     if |sb| == 0 {
    //         // Thanks Dafny
    //     }
    //     else {
    //         //assert total_balances(sb) == sb[0] as int + total_balances(sb[1..]);
    //         //assert sb[0] as int + d.data.amount as int < 0x10000000000000000;
    //         //assert total_balances(sb[1..]) + d.data.amount as int < 0x10000000000000000;
    //         individualBalanceBoundMaintained(sb[1..],d);
    //     }
    // } 

    // lemma updateBalTotalBySingleDeposit(s: BeaconState, d: Deposit)
    //     requires s.eth1_deposit_index as int +  1 < 0x10000000000000000 
    //     requires |s.validators| == |s.balances|
    //     requires |s.validators| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
    //     requires total_balances(s.balances) + d.data.amount as int < 0x10000000000000000
        
    //     ensures total_balances(updateDeposit(s,d).balances) == total_balances(s.balances) + d.data.amount as int < 0x10000000000000000
    //     //ensures total_balances(updateDeposit(s,d).balances) == total_balances(s.balances) + total_deposits([d]) 
    // {
    //     var pk := seqKeysInValidators(s.validators); 
    //     if |s.balances| == 0 {
    //         // Thanks Dafny
    //     }
    //     else {
    //         if d.data.pubkey in pk {
    //             var index := get_validator_index(pk, d.data.pubkey);
    //             individualBalanceBoundMaintained(s.balances,d);
    //             //assert updateDeposit(s,d).balances ==  increase_balance(s,index,d.data.amount).balances;
    //             //assert increase_balance(s,index,d.data.amount).balances[index] == s.balances[index] + d.data.amount;
    //             //assert forall i :: 0 <= i < |s.balances| && i != index as int ==> increase_balance(s,index,d.data.amount).balances[i] == s.balances[i];
    //             //assert total_balances(updateDeposit(s,d).balances) == total_balances(increase_balance(s,index,d.data.amount).balances) ;
    //             updateExistingBalance(s, index, d.data.amount);
    //             //assert total_balances(updateDeposit(s,d).balances) == total_balances(s.balances) + d.data.amount as int ;
    //         }
    //         else {
    //             //assert updateDeposit(s,d).balances == s.balances + [d.data.amount];
    //             distBalancesProp(s.balances,[d.data.amount]);
    //             //assert total_balances(s.balances + [d.data.amount]) == total_balances(s.balances) + total_balances([d.data.amount]);
    //         }
    //     }
    // }

    // lemma updateExistingBalance(s: BeaconState, index: ValidatorIndex, delta: Gwei)
    //     requires index as int < |s.balances| 
    //     requires s.balances[index] as int + delta as int < 0x10000000000000000
    //     requires |s.balances| < VALIDATOR_REGISTRY_LIMIT as int

    //     ensures total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances) + delta as int
    // {
    //     //assert increase_balance(s,index,delta).balances[index] == s.balances[index] + delta;
    //     //assert forall i :: 0 <= i < |s.balances| && i != index as int ==> increase_balance(s,index,delta).balances[i] == s.balances[i];

    //     if index as int < |s.balances|-1 {
    //         assert increase_balance(s,index,delta).balances == increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]] + increase_balance(s,index,delta).balances[(index+1)..];
                                                                
    //         //assert total_balances(increase_balance(s,index,delta).balances[..index]) == total_balances(s.balances[..index]);
    //         //assert total_balances([increase_balance(s,index,delta).balances[index]]) == total_balances([s.balances[index]]) + delta as int;
    //         //assert total_balances(increase_balance(s,index,delta).balances[(index+1)..]) == total_balances(s.balances[(index+1)..]);

    //         //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]] + increase_balance(s,index,delta).balances[(index+1)..]);

    //         distBalancesProp(increase_balance(s,index,delta).balances[..index], [increase_balance(s,index,delta).balances[index]]);
    //         //assert total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]]) == total_balances(increase_balance(s,index,delta).balances[..index]) + total_balances([increase_balance(s,index,delta).balances[index]]);
    //         distBalancesProp(increase_balance(s,index,delta).balances[..index]+[increase_balance(s,index,delta).balances[index]], increase_balance(s,index,delta).balances[(index+1)..]);
    //         //assert total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]] + increase_balance(s,index,delta).balances[(index+1)..]) == total_balances(increase_balance(s,index,delta).balances[..index]) + total_balances([increase_balance(s,index,delta).balances[index]]) + total_balances(increase_balance(s,index,delta).balances[index+1..]);

    //         //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(increase_balance(s,index,delta).balances[..index]) + total_balances([increase_balance(s,index,delta).balances[index]]) + total_balances(increase_balance(s,index,delta).balances[index+1..]);
    //         //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]) + delta as int + total_balances(s.balances[(index+1)..]);

    //         //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]) + total_balances(s.balances[(index+1)..]) + delta as int;

    //         assert s.balances == s.balances[..index] + [s.balances[index]] + s.balances[(index+1)..];
    //         //assert total_balances(s.balances) == total_balances(s.balances[..index] + [s.balances[index]] + s.balances[(index+1)..]);

    //         distBalancesProp(s.balances[..index], [s.balances[index]]);
    //         //assert total_balances(s.balances[..index] + [s.balances[index]]) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]);
    //         distBalancesProp(s.balances[..index]+[s.balances[index]], s.balances[(index+1)..]);
    //         //assert total_balances(s.balances[..index] + [s.balances[index]] + s.balances[(index+1)..]) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]) + total_balances(s.balances[index+1..]);

    //         //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances) + delta as int;
    //     }
    //     else {
    //         //assert index as int == |s.balances| - 1;
    //         assert increase_balance(s,index,delta).balances == increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]];
                                                                
    //         //assert total_balances(increase_balance(s,index,delta).balances[..index]) == total_balances(s.balances[..index]);
    //         //assert total_balances([increase_balance(s,index,delta).balances[index]]) == total_balances([s.balances[index]]) + delta as int;
            
    //         //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]]);

    //         distBalancesProp(increase_balance(s,index,delta).balances[..index], [increase_balance(s,index,delta).balances[index]]);
    //         //assert total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]]) == total_balances(increase_balance(s,index,delta).balances[..index]) + total_balances([increase_balance(s,index,delta).balances[index]]);
            
            
    //         //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]) + delta as int;

    //         assert s.balances == s.balances[..index] + [s.balances[index]] ;
    //         //assert total_balances(s.balances) == total_balances(s.balances[..index] + [s.balances[index]]);

    //         distBalancesProp(s.balances[..index], [s.balances[index]]);
    //         //assert total_balances(s.balances[..index] + [s.balances[index]]) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]);
            
    //         //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances) + delta as int;
    //     }
    // }

    // lemma distBalancesProp(sb1: seq<Gwei>, sb2: seq<Gwei>)
    //     ensures total_balances(sb1 + sb2) == total_balances(sb1) + total_balances(sb2) 
    // {
    //     if |sb1| == 0 {
    //         assert sb1 + sb2 == sb2;
    //     }
    //     else {
    //         var sb := sb1 + sb2;
    //         //assert sb == [sb1[0]] +  sb1[1..] + sb2;
    //         assert sb[1..] == sb1[1..] + sb2;
    //         assert total_balances(sb) == sb[0] as int + total_balances(sb[1..]);
    //         //assert total_balances(sb1 + sb2) == sb[0] as int + total_balances(sb1[1..] + sb2);
    //         distBalancesProp(sb1[1..],sb2);

    //     }
    // }

    // lemma distDepositsProp(sd1: seq<Deposit>, sd2: seq<Deposit>)
    //     ensures total_deposits(sd1 + sd2) == total_deposits(sd1) + total_deposits(sd2) 
    // {
    //     if |sd2| == 0 {
    //         assert sd1 + sd2 == sd1;
    //     }
    //     else {
    //         var sd := sd1 + sd2;
    //         //assert sd == sd1 + sd2[..|sd2|-1] +  [sd2[|sd2|-1]];
    //         assert sd[..|sd|-1] == sd1 + sd2[..|sd2|-1] ;
    //         assert total_deposits(sd) == total_deposits(sd[..|sd|-1]) + sd2[|sd2|-1].data.amount as int;
    //         //assert total_deposits(sd1 + sd2) == total_deposits(sd1 + sd2[..|sd2|-1] ) + sd2[|sd2|-1].data.amount as int;
    //         distDepositsProp(sd1, sd2[..|sd2|-1] );
    //     }
    // }
    // lemma subsetDepositSumProp(deposits: seq<Deposit>, i: nat)
    //     requires i <= |deposits|
    //     ensures total_deposits(deposits[..i]) <= total_deposits(deposits);
    // {
    //     if i == |deposits| {
    //         assert deposits[..i] == deposits;
    //     }
    //     else {
    //         //assert i < |deposits|;
    //         assert deposits == deposits[..i] + deposits[i..];
    //         assert total_deposits(deposits) == total_deposits(deposits[..i] + deposits[i..]);
    //         distDepositsProp(deposits[..i], deposits[i..]);
    //         //assert total_deposits(deposits[..i] + deposits[i..]) == total_deposits(deposits[..i]) + total_deposits(deposits[i..]); 
    //     }
    // }

    

}