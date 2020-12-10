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

include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "../utils/MathHelpers.dfy"
include "../ssz/Constants.dfy"
include "BeaconChainTypes.dfy"
include "Validators.dfy"
include "Attestations.dfy"
include "Helpers.dfy"

/**
 * State transition functional specification for the Beacon Chain.
 */
module StateTransitionSpec {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NativeTypes
    import opened Eth2Types
    import opened Constants
    import opened BeaconChainTypes
    import opened Validators
    import opened Attestations
    import opened BeaconHelpers
    import opened MathHelpers

    /**
     *  Collect pubkey in a list of validators.
     *
     *  @param  xv  A list of validators,
     *  @returns    The set of keys helpd byt the validators in `xv`.
     */
    function keysInValidators(xv : seq<Validator>) : set<BLSPubkey>
        decreases xv
    {
        if |xv| == 0 then  
            {}
        else 
            { xv[0].pubkey } + keysInValidators(xv[1..])
    }

       /**
     *  Collect pubkey in a list of validators.
     *
     *  @param  xv  A list of validators,
     *  @returns    The sequence\list of keys helpd byt the validators in `xv`.
     */
    function method seqKeysInValidators(xv : seq<Validator>) : seq<BLSPubkey>
        ensures |seqKeysInValidators(xv)| == |xv|
        decreases xv
    {
        if |xv| == 0 then  
            []
        else 
            [ xv[0].pubkey ] + seqKeysInValidators(xv[1..])
    }

    /**
     *  Collect pubkey in a list of deposits.
     *
     *  @param  xd  A list of validators,
     *  @returns    The sequence\list of keys held by the depositors in `xd`.
     */
    function method seqKeysInDeposits(xd : seq<Deposit>) : seq<BLSPubkey>
        ensures |seqKeysInDeposits(xd)| == |xd|
        decreases xd
    {
        if |xd| == 0 then  
            []
        else 
            [ xd[0].data.pubkey ] + seqKeysInDeposits(xd[1..])
    }

    //  Specifications of finalisation of a state and forward to future slot.

    /**
     *  Result of processing a block.
     *  
     *  @param  s   A state.
     *  @param  b   A block to add to the state `s`.
     *  @returns    The state `s` updated to point to `b` with state_root set to 0.
     */
    function addBlockToState(s: BeaconState, b: BeaconBlock) :  BeaconState 
        //  Verify that the slots match
        requires b.slot == s.slot  
        // Verify that the parent matches
        requires b.parent_root == hash_tree_root(s.latest_block_header) 
        requires |s.validators| == |s.balances| 
        ensures |addBlockToState(s,b).validators| == |addBlockToState(s,b).balances|
        ensures addBlockToState(s,b).eth1_deposit_index == s.eth1_deposit_index
        ensures addBlockToState(s,b).validators == s.validators
        ensures addBlockToState(s,b).balances == s.balances
    {
        s.(
            latest_block_header := BeaconBlockHeader(
                b.slot,
                b.parent_root,
                DEFAULT_BYTES32
            )
        )
    }

    /**
     *  Complete the current slot.
     *
     *  @param  s   A beacon state.
     *  @returns    A new state `s' such that:
     *              1. a new latest_block_header' state_root set to the hash_tree_root(s) 
     *              2. the hash_tree_root(s) archived in the s'.state_roots for the slot
     *              3. the hash_tree_root of the new_block_header is archived 
     *              in s'.block_roots
     */
    function resolveStateRoot(s: BeaconState): BeaconState 
        //  Make sure s.slot does not  overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        //  parent_root of the state block header is preserved
        ensures s.latest_block_header.parent_root == resolveStateRoot(s).latest_block_header.parent_root
        //  eth1_deposit_index is left unchanged
        ensures s.eth1_deposit_index == resolveStateRoot(s).eth1_deposit_index

        ensures  s.latest_block_header.state_root != DEFAULT_BYTES32 ==>
            resolveStateRoot(s) == advanceSlot(s)
    {
        var new_latest_block_header := 
            if (s.latest_block_header.state_root == DEFAULT_BYTES32 ) then 
                s.latest_block_header.(state_root := hash_tree_root(s))
            else 
                s.latest_block_header
            ;
        //  new state
        s.(
            slot := s.slot + 1,
            latest_block_header := new_latest_block_header,
            block_roots := s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(new_latest_block_header)],
            state_roots := s.state_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s)]
        )
    }

    /**
     *  Finalise a state and forward to slot in the future.
     *  
     *  @param  s       A state
     *  @param  slot    A slot. 
     *  @returns        A new state obtained by archiving roots and incrementing slot.
     *                  slot.
     */
    function forwardStateToSlot(s: BeaconState, slot: Slot) : BeaconState 
        requires s.slot <= slot
        requires |s.validators| == |s.balances|

        ensures forwardStateToSlot(s, slot).slot == slot
        ensures forwardStateToSlot(s, slot).eth1_deposit_index == s.eth1_deposit_index
        ensures |forwardStateToSlot(s, slot).validators| == |forwardStateToSlot(s, slot).balances|
        ensures forwardStateToSlot(s, slot).validators == s.validators
        ensures forwardStateToSlot(s, slot).balances == s.balances
        
        //  termination ranking function
        decreases slot - s.slot
    {
        if (s.slot == slot) then 
            s
        else
            nextSlot(forwardStateToSlot(s, slot - 1))
    }

    /**
     *  Advance a state by one slot.
     *
     *  @param  s   A beacon state.
     *  @returns    The successor state for `slot + 1`.
     *
     *  @note       This function increment the slot number and archives 
     *              the previous state_root and block_root, and copy verbatim the 
     *              latest_block_header.
     */
    function advanceSlot(s : BeaconState) : BeaconState 
        //  Make sure s.slot does not overflow
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
    {
        //  Add header root to history of block_roots
        var new_block_roots := s.block_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s.latest_block_header)];
        //  Add state root to history of state roots
        var new_state_roots := s.state_roots[(s.slot % SLOTS_PER_HISTORICAL_ROOT) as int := hash_tree_root(s)];
        //  Increment slot and copy latest_block_header
        s.(
            slot := s.slot + 1,
            block_roots := new_block_roots,
            state_roots := new_state_roots
        )
    }

    /**
     *  Defines the value of state at next slot.
     */
    function nextSlot(s: BeaconState) : BeaconState 
        requires s.slot as nat + 1 < 0x10000000000000000 as nat
        requires |s.validators| == |s.balances|
        ensures nextSlot(s).latest_block_header.state_root != DEFAULT_BYTES32
        /** If s.slot is not at the boundary of an epoch, the 
            attestation/finality fields are unchanged. */
        ensures  (s.slot as nat + 1) %  SLOTS_PER_EPOCH as nat != 0  ==>
            nextSlot(s).justification_bits  == s.justification_bits
            && nextSlot(s).previous_epoch_attestations  == s.previous_epoch_attestations
            && nextSlot(s).current_epoch_attestations  == s.current_epoch_attestations
            && nextSlot(s).previous_justified_checkpoint  == s.previous_justified_checkpoint
            && nextSlot(s).current_justified_checkpoint  == s.current_justified_checkpoint
            && nextSlot(s).validators  == s.validators
            && nextSlot(s).balances  == s.balances
            && |nextSlot(s).validators| == |nextSlot(s).balances| 
            &&  nextSlot(s).eth1_deposit_index  == s.eth1_deposit_index

    {
            if (s.slot + 1) %  SLOTS_PER_EPOCH == 0 then 
                //  Apply update on partially resolved state, and then update slot
                assert(s.slot % SLOTS_PER_EPOCH != 0);
                // updateJustification(resolveStateRoot(s).(slot := s.slot)).(slot := s.slot + 1)
                var s1 := resolveStateRoot(s).(slot := s.slot);
                var s2 := updateJustificationAndFinalisation(s1);
                var s3 := finalUpdates(s2);
                var s4 := s3.(slot := s.slot + 1);
                s4
            else 
                //  @note: this captures advanceSlot as a special case of resolveStateRoot 
                resolveStateRoot(s)
    }

    /**
     *  Take into account deposits in a block.
     *
     *  @param  s           A beacon state.
     *  @param  deposits    A list of deposits from a block body.
     *  @returns            The state obtained after taking account the deposits in `body` from state `s` 
     */
    function updateDeposits(s: BeaconState, deposits: seq<Deposit>) : BeaconState 
        requires s.eth1_deposit_index as int +  |deposits| < 0x10000000000000000 
        requires |s.validators| == |s.balances|
        requires |s.validators| + |deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        //requires forall i,j :: 0 <= i < j < |s.validators| ==> s.validators[i].pubkey != s.validators[j].pubkey

        requires total_balances(s.balances) + total_deposits(deposits) < 0x10000000000000000 // less than total eth
        //requires forall i :: 0 <= i < |s.validators| ==> s.balances[i] as int + get_deposit_total(s.validators[i].pubkey, deposits) as int < 0x10000000000000000
        
        //ensures updateDeposits(s, deposits).slot == s.slot 
        //ensures updateDeposits(s, deposits).latest_block_header == s.latest_block_header
        //ensures updateDeposits(s, deposits).block_roots == s.block_roots
        //ensures updateDeposits(s, deposits).state_roots == s.state_roots

        ensures updateDeposits(s, deposits).eth1_deposit_index == s.eth1_deposit_index  + |deposits| as uint64 
        ensures |s.validators| <= |updateDeposits(s,deposits).validators| <= |s.validators| + |deposits| 
        
        // include properties ???
        //ensures |updateDeposits(s,deposits).validators| == |updateDeposits(s,deposits).balances|        
        //ensures |s.balances| <= |updateDeposits(s,deposits).balances| <= |s.balances| + |deposits| 

        ensures total_balances(updateDeposits(s,deposits).balances) == total_balances(s.balances) + total_deposits(deposits)
        
         decreases |deposits|
    {
        if |deposits| == 0 then s
        else 
            //assert |deposits| > 0;
            //assert forall i :: 0 <= i < |s.validators| ==> s.balances[i] as int + get_deposit_total(s.validators[i].pubkey, deposits) as int < 0x10000000000000000
            //assert total_balances(s.balances) + total_deposits(deposits[..|deposits|-1]) < 0x10000000000000000 ;
            //assert total_deposits(deposits[..|deposits|-1]) + total_deposits([deposits[|deposits|-1]]) == total_deposits(deposits) ;
            //updateDeposits(s,deposits[..|deposits|-1])
            //assert total_balances(s.balances) + total_deposits([deposits[|deposits|-1]]) < 0x10000000000000000;
            //updateBalancesLemma(s,deposits);
            //assert total_balances(s.balances) + total_deposits(deposits[..|deposits|-1]) < 0x10000000000000000;
            //assert deposits[|deposits|-1].data.amount as int < total_deposits(deposits);
            //assert total_balances(updateDeposits(s,deposits[..|deposits|-1]).balances) + deposits[|deposits|-1].data.amount as int < 0x10000000000000000;

            updateBalTotalBySingleDeposit(updateDeposits(s,deposits[..|deposits|-1]), deposits[|deposits|-1]);

            updateDeposit(updateDeposits(s,deposits[..|deposits|-1]),deposits[|deposits|-1])
    }

    /**
     *  Take into account a single deposit from a block.
     *
     *  @param  s       A beacon state.
     *  @param  d       A single deposit.
     *  @returns        The state obtained after taking account the deposit `d` from state `s` 
     */
    function updateDeposit(s: BeaconState, d: Deposit) : BeaconState 
        requires s.eth1_deposit_index as int +  1 < 0x10000000000000000 
        requires |s.validators| == |s.balances|
        requires |s.validators| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
        requires total_balances(s.balances) + d.data.amount as int < 0x10000000000000000
        
        //requires d.data.pubkey in seqKeysInValidators(s.validators) ==> s.balances[get_validator_index(seqKeysInValidators(s.validators), d.data.pubkey)] as int + d.data.amount as int < 0x10000000000000000
        
        ensures d.data.pubkey !in seqKeysInValidators(s.validators) ==> updateDeposit(s,d).validators == s.validators + [get_validator_from_deposit(d)]
        ensures d.data.pubkey in seqKeysInValidators(s.validators)  ==> updateDeposit(s,d).validators == s.validators 
        
        ensures updateDeposit(s,d).eth1_deposit_index == s.eth1_deposit_index + 1
        //ensures updateDeposit(s,d).slot == s.slot
        //ensures updateDeposit(s,d).latest_block_header == s.latest_block_header
        //ensures updateDeposit(s,d).block_roots == s.block_roots
        //ensures updateDeposit(s,d).state_roots == s.state_roots

        ensures |updateDeposit(s,d).validators| == |updateDeposit(s,d).balances|        // maybe include in property lemmas
        ensures |s.validators| <= |updateDeposit(s,d).validators| <= |s.validators| + 1 // maybe include in property lemmas
        ensures |s.balances| <= |updateDeposit(s,d).balances| <= |s.balances| + 1 // maybe include in property lemmas
        ensures forall i :: 0 <= i < |s.balances| ==> s.balances[i] <= updateDeposit(s,d).balances[i]
        //ensures total_balances(updateDeposit(s,d).balances) == total_balances(s.balances) + d.data.amount as int < 0x10000000000000000
        // in lemma
        
    {
        var pk := seqKeysInValidators(s.validators); 
        
        s.(
            eth1_deposit_index := (s.eth1_deposit_index as int + 1) as uint64,
            validators := if d.data.pubkey in pk then 
                                s.validators // unchanged validator members
                            else 
                                validator_append(s.validators, get_validator_from_deposit(d)), //(s.validators + [get_validator_from_deposit(d)]),
            balances := if d.data.pubkey in pk then 
                                individualBalanceBoundMaintained(s.balances,d);
                                //assert s.balances[get_validator_index(pk, d.data.pubkey)] as int + d.data.amount as int < 0x10000000000000000;
                                increase_balance(s,get_validator_index(pk, d.data.pubkey),d.data.amount).balances
                            else 
                                balance_append(s.balances, d.data.amount) //s.balances + [d.data.amount]
        )
    }


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
        updateFinalisedCheckpoint(updateJustification(s))
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
    function updateFinalisedCheckpoint(s: BeaconState) : BeaconState
        ensures s.slot == updateFinalisedCheckpoint(s).slot
    {
        if get_current_epoch(s) <= GENESIS_EPOCH + 1 then 
            s 
        else 
            var bits : seq<bool> := s.justification_bits;
            var current_epoch := get_current_epoch(s);
            if (all(bits[1..4]) && current_epoch >= 3 && s.previous_justified_checkpoint.epoch  == current_epoch - 3) then 
                //  The 2nd/3rd/4th most recent epochs are justified, the 2nd using the 4th as source
                s.(finalised_checkpoint := s.previous_justified_checkpoint) 
            else if (all(bits[1..3]) && s.previous_justified_checkpoint.epoch == current_epoch - 2) then 
                // The 2nd/3rd most recent epochs are justified, the 2nd using the 3rd as source
                s.(finalised_checkpoint := s.previous_justified_checkpoint) 
            else if (all(bits[0..3]) && s.current_justified_checkpoint.epoch == current_epoch - 2) then 
                // The 1st/2nd/3rd most recent epochs are justified, the 1st using the 3rd as source
                s.(finalised_checkpoint := s.current_justified_checkpoint) 
            else if (false && all(bits[0..2]) && s.current_justified_checkpoint.epoch == current_epoch - 1) then 
                // The 1st/2nd most recent epochs are justified, the 1st using the 2nd as source
                s.(finalised_checkpoint := s.current_justified_checkpoint) 
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
    function total_deposits(deposits: seq<Deposit>): nat
    {
        if |deposits| == 0 then 0
        //else deposits[0].data.amount as nat + total_deposits(deposits[1..])
        else total_deposits(deposits[..|deposits|-1]) + deposits[|deposits|-1].data.amount as nat
    }

    function total_balances(bal: seq<Gwei>): nat
    {
        if |bal| == 0 then 0
        else bal[0] as nat + total_balances(bal[1..])
    }

        /**
     * Extract a validator from a single deposit.
     *
     *  @param  d       A single deposit.
     *  @returns        A validator created from the deposit information
     *
     *  @note           The `effective_balance` is not an active field in the current model but the code
     *                  to set this field is included as a comment for future reference.
     */
    function method get_validator_from_deposit(d: Deposit): Validator
        ensures get_validator_from_deposit(d).effectiveBalance <= MAX_EFFECTIVE_BALANCE as Gwei
    {
        var amount := d.data.amount; 
        var effective_balance := min((amount as int- amount as int % EFFECTIVE_BALANCE_INCREMENT) as nat, MAX_EFFECTIVE_BALANCE as nat);

        Validator(d.data.pubkey, effective_balance as Gwei)
    }

    /**
     *  Append a new validator
     */
    function method validator_append(sv: ListOfValidators, v: Validator): ListOfValidators
        requires |sv| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
    {
        sv + [v]
    }
    /**
     *  Append a new balance entry
     */
    function method balance_append(sb: ListOfBalances, b: Gwei): ListOfBalances
        requires |sb| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
    {
        sb + [b]
    }

     /**
     *  Get the index of a validator. 
     *
     *  @notes  Helper function as no alternative indexing functionality available.
     *
     */
    function method get_validator_index(pk: seq<BLSPubkey>, pubkey: BLSPubkey) : ValidatorIndex
        requires |pk| < VALIDATOR_REGISTRY_LIMIT as int
        requires pubkey in pk
        ensures get_validator_index(pk,pubkey) as int < |pk|
        ensures pk[get_validator_index(pk,pubkey)] == pubkey
        decreases pk
    {
        if pk[0] == pubkey then 0 as ValidatorIndex
        else 1 + get_validator_index(pk[1..], pubkey)
        // alternative reverse form
        //if pk[|pk|-1] == pubkey then (|pk|-1) as ValidatorIndex
        //else get_validator_index(pk[..|pk|-1], pubkey)

    }


    // Beacon State Mutators

    /** increase_balance
     *  Increase the validator balance at index ``index`` by ``delta``.
     *
     *  @notes  The datatype Gwei has temporarily been changed from uint64 to nat so as to simplify the
     *          properties required to process a deposit. Hence a further requires will be needed to prevent
     *          overflow once this temporary simplification is removed.
     *  
     **/
    function method increase_balance(s: BeaconState, index: ValidatorIndex, delta: Gwei): BeaconState 
        requires index as int < |s.balances| 
        requires s.balances[index] as int + delta as int < 0x10000000000000000
        ensures |s.balances| == |increase_balance(s,index,delta).balances|
        ensures increase_balance(s,index,delta).balances[index] == s.balances[index] + delta
    {
        s.(
            balances := s.balances[index as int := (s.balances[index] + delta)]
        )
    }
    
    // Helper lemmas


    lemma individualBalanceBoundMaintained(sb: seq<Gwei>, d: Deposit)
        requires total_balances(sb) + d.data.amount as int < 0x10000000000000000
        ensures forall i :: 0 <= i < |sb| ==> sb[i] as int + d.data.amount as int < 0x10000000000000000
    {
        if |sb| == 0 {
            // Thanks Dafny
        }
        else {
            //assert total_balances(sb) == sb[0] as int + total_balances(sb[1..]);
            //assert sb[0] as int + d.data.amount as int < 0x10000000000000000;
            //assert total_balances(sb[1..]) + d.data.amount as int < 0x10000000000000000;
            individualBalanceBoundMaintained(sb[1..],d);
        }
    } 

    lemma updateBalTotalBySingleDeposit(s: BeaconState, d: Deposit)
        requires s.eth1_deposit_index as int +  1 < 0x10000000000000000 
        requires |s.validators| == |s.balances|
        requires |s.validators| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
        requires total_balances(s.balances) + d.data.amount as int < 0x10000000000000000
        
        ensures total_balances(updateDeposit(s,d).balances) == total_balances(s.balances) + d.data.amount as int < 0x10000000000000000
        //ensures total_balances(updateDeposit(s,d).balances) == total_balances(s.balances) + total_deposits([d]) 
    {
        var pk := seqKeysInValidators(s.validators); 
        if |s.balances| == 0 {
            // Thanks Dafny
        }
        else {
            if d.data.pubkey in pk {
                var index := get_validator_index(pk, d.data.pubkey);
                individualBalanceBoundMaintained(s.balances,d);
                //assert updateDeposit(s,d).balances ==  increase_balance(s,index,d.data.amount).balances;
                //assert increase_balance(s,index,d.data.amount).balances[index] == s.balances[index] + d.data.amount;
                //assert forall i :: 0 <= i < |s.balances| && i != index as int ==> increase_balance(s,index,d.data.amount).balances[i] == s.balances[i];
                //assert total_balances(updateDeposit(s,d).balances) == total_balances(increase_balance(s,index,d.data.amount).balances) ;
                updateExistingBalance(s, index, d.data.amount);
                //assert total_balances(updateDeposit(s,d).balances) == total_balances(s.balances) + d.data.amount as int ;
            }
            else {
                //assert updateDeposit(s,d).balances == s.balances + [d.data.amount];
                distBalancesProp(s.balances,[d.data.amount]);
                //assert total_balances(s.balances + [d.data.amount]) == total_balances(s.balances) + total_balances([d.data.amount]);
            }
        }
    }

    lemma updateExistingBalance(s: BeaconState, index: ValidatorIndex, delta: Gwei)
        requires index as int < |s.balances| 
        requires s.balances[index] as int + delta as int < 0x10000000000000000
        requires |s.balances| < VALIDATOR_REGISTRY_LIMIT as int

        ensures total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances) + delta as int
    {
        //assert increase_balance(s,index,delta).balances[index] == s.balances[index] + delta;
        //assert forall i :: 0 <= i < |s.balances| && i != index as int ==> increase_balance(s,index,delta).balances[i] == s.balances[i];

        if index as int < |s.balances|-1 {
            assert increase_balance(s,index,delta).balances == increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]] + increase_balance(s,index,delta).balances[(index+1)..];
                                                                
            //assert total_balances(increase_balance(s,index,delta).balances[..index]) == total_balances(s.balances[..index]);
            //assert total_balances([increase_balance(s,index,delta).balances[index]]) == total_balances([s.balances[index]]) + delta as int;
            //assert total_balances(increase_balance(s,index,delta).balances[(index+1)..]) == total_balances(s.balances[(index+1)..]);

            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]] + increase_balance(s,index,delta).balances[(index+1)..]);

            distBalancesProp(increase_balance(s,index,delta).balances[..index], [increase_balance(s,index,delta).balances[index]]);
            //assert total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]]) == total_balances(increase_balance(s,index,delta).balances[..index]) + total_balances([increase_balance(s,index,delta).balances[index]]);
            distBalancesProp(increase_balance(s,index,delta).balances[..index]+[increase_balance(s,index,delta).balances[index]], increase_balance(s,index,delta).balances[(index+1)..]);
            //assert total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]] + increase_balance(s,index,delta).balances[(index+1)..]) == total_balances(increase_balance(s,index,delta).balances[..index]) + total_balances([increase_balance(s,index,delta).balances[index]]) + total_balances(increase_balance(s,index,delta).balances[index+1..]);

            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(increase_balance(s,index,delta).balances[..index]) + total_balances([increase_balance(s,index,delta).balances[index]]) + total_balances(increase_balance(s,index,delta).balances[index+1..]);
            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]) + delta as int + total_balances(s.balances[(index+1)..]);

            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]) + total_balances(s.balances[(index+1)..]) + delta as int;

            assert s.balances == s.balances[..index] + [s.balances[index]] + s.balances[(index+1)..];
            //assert total_balances(s.balances) == total_balances(s.balances[..index] + [s.balances[index]] + s.balances[(index+1)..]);

            distBalancesProp(s.balances[..index], [s.balances[index]]);
            //assert total_balances(s.balances[..index] + [s.balances[index]]) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]);
            distBalancesProp(s.balances[..index]+[s.balances[index]], s.balances[(index+1)..]);
            //assert total_balances(s.balances[..index] + [s.balances[index]] + s.balances[(index+1)..]) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]) + total_balances(s.balances[index+1..]);

            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances) + delta as int;
        }
        else {
            //assert index as int == |s.balances| - 1;
            assert increase_balance(s,index,delta).balances == increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]];
                                                                
            //assert total_balances(increase_balance(s,index,delta).balances[..index]) == total_balances(s.balances[..index]);
            //assert total_balances([increase_balance(s,index,delta).balances[index]]) == total_balances([s.balances[index]]) + delta as int;
            
            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]]);

            distBalancesProp(increase_balance(s,index,delta).balances[..index], [increase_balance(s,index,delta).balances[index]]);
            //assert total_balances(increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]]) == total_balances(increase_balance(s,index,delta).balances[..index]) + total_balances([increase_balance(s,index,delta).balances[index]]);
            
            
            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]) + delta as int;

            assert s.balances == s.balances[..index] + [s.balances[index]] ;
            //assert total_balances(s.balances) == total_balances(s.balances[..index] + [s.balances[index]]);

            distBalancesProp(s.balances[..index], [s.balances[index]]);
            //assert total_balances(s.balances[..index] + [s.balances[index]]) == total_balances(s.balances[..index]) + total_balances([s.balances[index]]);
            
            //assert total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances) + delta as int;
        }
    }

    lemma distBalancesProp(sb1: seq<Gwei>, sb2: seq<Gwei>)
        ensures total_balances(sb1 + sb2) == total_balances(sb1) + total_balances(sb2) 
    {
        if |sb1| == 0 {
            assert sb1 + sb2 == sb2;
        }
        else {
            var sb := sb1 + sb2;
            //assert sb == [sb1[0]] +  sb1[1..] + sb2;
            assert sb[1..] == sb1[1..] + sb2;
            assert total_balances(sb) == sb[0] as int + total_balances(sb[1..]);
            //assert total_balances(sb1 + sb2) == sb[0] as int + total_balances(sb1[1..] + sb2);
            distBalancesProp(sb1[1..],sb2);

        }
    }

    lemma distDepositsProp(sd1: seq<Deposit>, sd2: seq<Deposit>)
        ensures total_deposits(sd1 + sd2) == total_deposits(sd1) + total_deposits(sd2) 
    {
        if |sd2| == 0 {
            assert sd1 + sd2 == sd1;
        }
        else {
            var sd := sd1 + sd2;
            //assert sd == sd1 + sd2[..|sd2|-1] +  [sd2[|sd2|-1]];
            assert sd[..|sd|-1] == sd1 + sd2[..|sd2|-1] ;
            assert total_deposits(sd) == total_deposits(sd[..|sd|-1]) + sd2[|sd2|-1].data.amount as int;
            //assert total_deposits(sd1 + sd2) == total_deposits(sd1 + sd2[..|sd2|-1] ) + sd2[|sd2|-1].data.amount as int;
            distDepositsProp(sd1, sd2[..|sd2|-1] );
        }
    }
    lemma subsetDepositSumProp(deposits: seq<Deposit>, i: nat)
        requires i <= |deposits|
        ensures total_deposits(deposits[..i]) <= total_deposits(deposits);
    {
        if i == |deposits| {
            assert deposits[..i] == deposits;
        }
        else {
            //assert i < |deposits|;
            assert deposits == deposits[..i] + deposits[i..];
            assert total_deposits(deposits) == total_deposits(deposits[..i] + deposits[i..]);
            distDepositsProp(deposits[..i], deposits[i..]);
            //assert total_deposits(deposits[..i] + deposits[i..]) == total_deposits(deposits[..i]) + total_deposits(deposits[i..]); 
        }
    }

    

}