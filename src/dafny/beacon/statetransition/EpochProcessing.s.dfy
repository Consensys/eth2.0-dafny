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



    
    // // Helper lemmas


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