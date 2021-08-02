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
include "ProcessOperations.s.dfy"

/**
 * State transition function for the Beacon Chain.
 */
module ProcessOperations {
    
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
    import opened ProcessOperationsSpec
    

    /**
     *  Process the operations defined by a block body.
     *  
     *  @param  s   A state.
     *  @param  bb  A block body.
     *  @returns    The state obtained after applying the operations of `bb` to `s`.
     */
    method process_operations(s: BeaconState, bb: BeaconBlockBody)  returns (s' : BeaconState) 
        requires s.eth1_deposit_index as int +  |bb.deposits| < 0x10000000000000000 
        requires |s.validators| + |bb.deposits| <= VALIDATOR_REGISTRY_LIMIT as int
        requires |s.validators| == |s.balances|
        requires total_balances(s.balances) + total_deposits(bb.deposits) < 0x10000000000000000 
        
        //ensures |s'.validators| == |s'.balances|
        ensures s' == updateDeposits(s, bb.deposits)
        ensures s'.slot == s.slot
        ensures s'.latest_block_header == s.latest_block_header
    {
        //  process deposits in the beacon block body.
        s':= s;

        var i := 0;
        assert s' == updateDeposits(s, bb.deposits[..i]);
        assert total_balances(s'.balances) + total_deposits(bb.deposits[..i]) < 0x10000000000000000 ;
        
        while i < |bb.deposits| 
            decreases |bb.deposits| - i

            invariant 0 <= i <= |bb.deposits|
            invariant s'.eth1_deposit_index == s.eth1_deposit_index + i as uint64
            
            invariant total_balances(s.balances) + total_deposits(bb.deposits[..i]) < 0x10000000000000000 

            invariant s' == updateDeposits(s, bb.deposits[..i])
            invariant s'.slot == s.slot
            invariant s'.latest_block_header == s.latest_block_header
        {
            assert bb.deposits[..i+1] == bb.deposits[..i] + [bb.deposits[i]];

            subsetDepositSumProp(bb.deposits, i+1);
            
            s':= process_deposit(s', bb.deposits[i]); 
            i := i+1;

        }
        assert bb.deposits[..i] == bb.deposits;
    }

    /**
     *  Process a deposit operation.
     *
     *  @param  s   A state.
     *  @param  d   A deposit.  
     *  @returns    The state obtained depositing of `d` to `s`.
     *  @todo       Finish implementation of this function.
     */
    method process_deposit(s: BeaconState, d : Deposit)  returns (s' : BeaconState)  
        requires |s.validators| + 1 <= VALIDATOR_REGISTRY_LIMIT as int
        requires s.eth1_deposit_index as int + 1 < 0x10000000000000000 
        requires |s.validators| == |s.balances|
        requires total_balances(s.balances) + d.data.amount as int < 0x10000000000000000

        ensures s'.eth1_deposit_index == s.eth1_deposit_index + 1
        ensures s' == updateDeposit(s,d)

    {
        // note that it is assumed that all new validator deposits are verified
        // ie the step # Verify the deposit signature (proof of possession) which is not checked by the deposit contract
        // is not performed
        var pk := seqKeysInValidators(s.validators);
        s' := s.(
                eth1_deposit_index := (s.eth1_deposit_index as int + 1) as uint64,
                validators := if d.data.pubkey in pk then 
                                    s.validators // unchanged validator members
                                else 
                                    (s.validators + [get_validator_from_deposit(d)]),
                balances := if d.data.pubkey in pk then 
                                    individualBalanceBoundMaintained(s.balances,d);
                                    increase_balance(s,get_validator_index(pk, d.data.pubkey),d.data.amount).balances
                                else 
                                    s.balances + [d.data.amount]
        );
    }

}