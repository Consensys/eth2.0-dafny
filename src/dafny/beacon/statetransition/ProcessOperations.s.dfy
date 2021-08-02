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

include "../../utils/NativeTypes.dfy"
include "../../utils/Eth2Types.dfy"
include "../../utils/Helpers.dfy"
include "../../utils/MathHelpers.dfy"
include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../validators/Validators.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../Helpers.dfy"

/**
 *  Proofs for process operations
 */
module ProcessOperationsSpec {
    
    //  Import some constants, types and beacon chain helpers.
    import opened NativeTypes
    import opened Eth2Types
    import opened Constants
    import opened BeaconChainTypes
    import opened Validators
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened BeaconHelpers
    import opened MathHelpers

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

        requires total_balances(s.balances) + total_deposits(deposits) < 0x10000000000000000 // less than total eth

        ensures updateDeposits(s, deposits).eth1_deposit_index == s.eth1_deposit_index  + |deposits| as uint64 
        ensures |s.validators| <= |updateDeposits(s,deposits).validators| <= |s.validators| + |deposits| 
        
        ensures total_balances(updateDeposits(s,deposits).balances) == total_balances(s.balances) + total_deposits(deposits)
        
         decreases |deposits|
    {
        if |deposits| == 0 then s
        else 
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
        
        ensures d.data.pubkey !in seqKeysInValidators(s.validators) ==> updateDeposit(s,d).validators == s.validators + [get_validator_from_deposit(d)]
        ensures d.data.pubkey in seqKeysInValidators(s.validators)  ==> updateDeposit(s,d).validators == s.validators 
        
        ensures updateDeposit(s,d).eth1_deposit_index == s.eth1_deposit_index + 1

        ensures |updateDeposit(s,d).validators| == |updateDeposit(s,d).balances|        // maybe include in property lemmas
        ensures |s.validators| <= |updateDeposit(s,d).validators| <= |s.validators| + 1 // maybe include in property lemmas
        ensures |s.balances| <= |updateDeposit(s,d).balances| <= |s.balances| + 1 // maybe include in property lemmas
        ensures forall i :: 0 <= i < |s.balances| ==> s.balances[i] <= updateDeposit(s,d).balances[i]
        
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
     * Extract a validator from a single deposit.
     *
     *  @param  d       A single deposit.
     *  @returns        A validator created from the deposit information
     *
     *  @note           The `effective_balance` is not an active field in the current model but the code
     *                  to set this field is included as a comment for future reference.
     */
    // function method get_validator_from_deposit(d: Deposit): Validator
    //     ensures get_validator_from_deposit(d).effectiveBalance <= MAX_EFFECTIVE_BALANCE as Gwei
    // {
    //     var amount := d.data.amount; 
    //     var effective_balance := min((amount as int- amount as int % EFFECTIVE_BALANCE_INCREMENT) as nat, MAX_EFFECTIVE_BALANCE as nat);

    //     Validator(d.data.pubkey, effective_balance as Gwei)
    // }

    /**
     *  Append a new validator
     */
    // function method validator_append(sv: ListOfValidators, v: Validator): ListOfValidators
    //     requires |sv| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
    // {
    //     sv + [v]
    // }
    /**
     *  Append a new balance entry
     */
    // function method balance_append(sb: ListOfBalances, b: Gwei): ListOfBalances
    //     requires |sb| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
    // {
    //     sb + [b]
    // }

     /**
     *  Get the index of a validator. 
     *
     *  @notes  Helper function as no alternative indexing functionality available.
     *
     */
    // function method get_validator_index(pk: seq<BLSPubkey>, pubkey: BLSPubkey) : ValidatorIndex
    //     requires |pk| < VALIDATOR_REGISTRY_LIMIT as int
    //     requires pubkey in pk
    //     ensures get_validator_index(pk,pubkey) as int < |pk|
    //     ensures pk[get_validator_index(pk,pubkey)] == pubkey
    //     decreases pk
    // {
    //     if pk[0] == pubkey then 0 as ValidatorIndex
    //     else 1 + get_validator_index(pk[1..], pubkey)
    //     // alternative reverse form
    //     //if pk[|pk|-1] == pubkey then (|pk|-1) as ValidatorIndex
    //     //else get_validator_index(pk[..|pk|-1], pubkey)

    // }

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
    
    // Beacon State Mutators

    /** increase_balance
     *  Increase the validator balance at index ``index`` by ``delta``.
     *
     *  @notes  The datatype Gwei has temporarily been changed from uint64 to nat so as to simplify the
     *          properties required to process a deposit. Hence a further requires will be needed to prevent
     *          overflow once this temporary simplification is removed.
     *  
     **/
    // function method increase_balance(s: BeaconState, index: ValidatorIndex, delta: Gwei): BeaconState 
    //     requires index as int < |s.balances| 
    //     requires s.balances[index] as int + delta as int < 0x10000000000000000
    //     ensures |s.balances| == |increase_balance(s,index,delta).balances|
    //     ensures increase_balance(s,index,delta).balances[index] == s.balances[index] + delta
    // {
    //     s.(
    //         balances := s.balances[index as int := (s.balances[index] + delta)]
    //     )
    // }

    
    lemma individualBalanceBoundMaintained(sb: seq<Gwei>, d: Deposit)
        requires total_balances(sb) + d.data.amount as int < 0x10000000000000000
        ensures forall i :: 0 <= i < |sb| ==> sb[i] as int + d.data.amount as int < 0x10000000000000000
    {
        if |sb| == 0 {
            // Thanks Dafny
        }
        else {
            individualBalanceBoundMaintained(sb[1..],d);
        }
    } 

    lemma updateBalTotalBySingleDeposit(s: BeaconState, d: Deposit)
        requires s.eth1_deposit_index as int +  1 < 0x10000000000000000 
        requires |s.validators| == |s.balances|
        requires |s.validators| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
        requires total_balances(s.balances) + d.data.amount as int < 0x10000000000000000
        
        ensures total_balances(updateDeposit(s,d).balances) == total_balances(s.balances) + d.data.amount as int < 0x10000000000000000
    {
        var pk := seqKeysInValidators(s.validators); 
        if |s.balances| == 0 {
            // Thanks Dafny
        }
        else {
            if d.data.pubkey in pk {
                var index := get_validator_index(pk, d.data.pubkey);
                individualBalanceBoundMaintained(s.balances,d);
                updateExistingBalance(s, index, d.data.amount);
            }
            else {
                distBalancesProp(s.balances,[d.data.amount]);
            }
        }
    }

    lemma updateExistingBalance(s: BeaconState, index: ValidatorIndex, delta: Gwei)
        requires index as int < |s.balances| 
        requires s.balances[index] as int + delta as int < 0x10000000000000000
        requires |s.balances| < VALIDATOR_REGISTRY_LIMIT as int

        ensures total_balances(increase_balance(s,index,delta).balances) == total_balances(s.balances) + delta as int
    {
        if index as int < |s.balances|-1 {
            assert increase_balance(s,index,delta).balances == increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]] + increase_balance(s,index,delta).balances[(index+1)..];
                                                                
            distBalancesProp(increase_balance(s,index,delta).balances[..index], [increase_balance(s,index,delta).balances[index]]);

            distBalancesProp(increase_balance(s,index,delta).balances[..index]+[increase_balance(s,index,delta).balances[index]], increase_balance(s,index,delta).balances[(index+1)..]);

            assert s.balances == s.balances[..index] + [s.balances[index]] + s.balances[(index+1)..];

            distBalancesProp(s.balances[..index], [s.balances[index]]);

            distBalancesProp(s.balances[..index]+[s.balances[index]], s.balances[(index+1)..]);

        }
        else {

            assert increase_balance(s,index,delta).balances == increase_balance(s,index,delta).balances[..index] + [increase_balance(s,index,delta).balances[index]];
                                                                
            distBalancesProp(increase_balance(s,index,delta).balances[..index], [increase_balance(s,index,delta).balances[index]]);

            assert s.balances == s.balances[..index] + [s.balances[index]] ;

            distBalancesProp(s.balances[..index], [s.balances[index]]);
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
            assert sb[1..] == sb1[1..] + sb2;
            assert total_balances(sb) == sb[0] as int + total_balances(sb[1..]);
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
            assert sd[..|sd|-1] == sd1 + sd2[..|sd2|-1] ;
            assert total_deposits(sd) == total_deposits(sd[..|sd|-1]) + sd2[|sd2|-1].data.amount as int;
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
            assert deposits == deposits[..i] + deposits[i..];
            assert total_deposits(deposits) == total_deposits(deposits[..i] + deposits[i..]);
            distDepositsProp(deposits[..i], deposits[i..]);
        }
    }

}