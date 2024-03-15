include "../../utils/Eth2Types.dfy"
include "../../utils/MathHelpers.dfy"
include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../Helpers.dfy"
include "../Helpers.s.dfy"
include "../Helpers.cap.dfy"
include "../validators/Validators.dfy"
include "StateTransition.s.dfy"
include "EpochProcessing.dfy"
include "ProcessOperations.dfy"
include "ProcessOperations.s.dfy"



module  StateTransitionCapella {

    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened MathHelpers
    import opened Constants
    import opened BeaconChainTypes
    import opened BeaconHelpers
    import opened BeaconHelperSpec
    import opened BeaconHelpersCapella
    import opened Validators
    import opened StateTransitionSpec
    import opened EpochProcessing
    import opened ProcessOperations
    import opened ProcessOperationsSpec


    method get_expected_withdrawals(s: BeaconState) returns (withdrawals: seq<Withdrawal>)
        requires |s.balances| <= VALIDATOR_REGISTRY_LIMIT as int;
        requires |s.validators| <= VALIDATOR_REGISTRY_LIMIT as int;
        requires 0 <= s.next_withdrawal_validator_index as int < |s.validators|;
        requires 0 <= s.next_withdrawal_validator_index as int < |s.balances|;
        requires 0 <= s.next_withdrawal_index as int < 0x10000000000000000;
    
    {
        var epoch := get_current_epoch(s);
        // var withdrawal_index := s.next_withdrawal_index;
        // var validator_index := s.next_withdrawal_validator_index;
        withdrawals := [];
        var bound := min(|s.validators|, MAX_VALIDATORS_PER_WITHDRAWAL_SWEEP as nat) as int;
        var i: nat;

        for i := 1 to bound + 1{
            var validator := s.validators[s.next_withdrawal_validator_index];
            var balance := s.balances[s.next_withdrawal_validator_index];
            var newNextWithdrawalValidatorIndex := s.next_withdrawal_validator_index as int;

            if 0 <= s.next_withdrawal_validator_index as int < |s.validators| && 0 <= s.next_withdrawal_validator_index as int < |s.balances| {
                if is_fully_withdrawable_validator(validator, balance, epoch) {
                var withdrawal := Withdrawal(
                    index := s.next_withdrawal_validator_index,
                    validator_index := s.next_withdrawal_validator_index,
                    address := validator.execution_address,
                    amount := balance
                );
                withdrawals := withdrawals + [withdrawal];
                // s.next_withdrawal_validator_index := s.next_withdrawal_validator_index + 1;
                newNextWithdrawalValidatorIndex := s.next_withdrawal_validator_index as int + 1;
            } else if is_partially_withdrawable_validator(validator, balance, epoch) {
                var withdrawal := Withdrawal(
                    index := s.next_withdrawal_validator_index,
                    validator_index := s.next_withdrawal_validator_index,
                    address := validator.execution_address,
                    amount := balance - (min(balance as nat, MAX_EFFECTIVE_BALANCE as nat) as Gwei)
                );
                withdrawals := withdrawals + [withdrawal];
                // s.next_withdrawal_validator_index := s.next_withdrawal_validator_index + 1;
                newNextWithdrawalValidatorIndex := s.next_withdrawal_validator_index as int + 1;
            }

            if |withdrawals| == MAX_WITHDRAWALS_PER_PAYLOAD as int {
                break;
            }

            // s.next_withdrawal_validator_index := (s.next_withdrawal_validator_index + 1) % |s.validators|;
            newNextWithdrawalValidatorIndex := (newNextWithdrawalValidatorIndex + 1) % |s.validators|;
            }   

        }
    }


    predicate method is_valid_withdrawal(state: BeaconState, payload: ExecutionPayload)
    {   
        // Ensure that the withdrawal index is valid
        // Ensure that the withdrawal validator index is valid
        (state.next_withdrawal_index <= 0xFFFFFFFFFFFFFFFF) && (state.next_withdrawal_validator_index as int <= |state.validators|)
    }


    method process_withdrawals(state: BeaconState, payload: ExecutionPayload)
        requires |state.validators| > 0;
        requires |payload.withdrawals| as nat <= MAX_WITHDRAWALS_PER_PAYLOAD as nat <= 0xFFFFFFFFFFFFFFFF;

        requires |payload.withdrawals| > 0;

        requires state.next_withdrawal_validator_index as int < |state.validators|;
        requires 0 <= state.next_withdrawal_validator_index as int < |state.balances|;

        requires state.next_withdrawal_index as int < 0x10000000000000000;
        // requires |state.balances| >= state.withdrawal_index as int;

        requires is_valid_withdrawal(state, payload);

        requires is_valid_number_active_validators(|state.validators|);

        requires |state.validators| <= VALIDATOR_REGISTRY_LIMIT as int;

        // ensures (state.next_withdrawal_index as int) == old(state.next_withdrawal_index) as int + |payload.withdrawals|;
        ensures state.next_withdrawal_validator_index >= old(state.next_withdrawal_validator_index) && state.next_withdrawal_validator_index as int < |state.validators|;
        
    {
        var expected_withdrawals := get_expected_withdrawals(state);


        var newNextWithdrawalIndex := (state.next_withdrawal_index) as int;
        var newNextValidatorIndex := (state.next_withdrawal_validator_index) as int;

        // Updated loop to process withdrawals with validation
        for i := 0 to |expected_withdrawals| {
            var expected_withdrawal := expected_withdrawals[i];

            // Validate that the validator's index has a corresponding balance
            if expected_withdrawal.validator_index as int < |state.balances| {
            
            var state := decrease_balance(state, expected_withdrawal.validator_index, expected_withdrawal.amount);

            }
            // This withdrawal cannot be processed due to inconsistency; skip
        }

        // Update the next withdrawal index if this block contained withdrawals
        if |expected_withdrawals| != 0 {
            var latest_withdrawal := expected_withdrawals[|expected_withdrawals| - 1];
            newNextWithdrawalIndex := ((latest_withdrawal.index as int) + 1) as int;
        }

        // Update the next validator index to start the next withdrawal sweep
        if |expected_withdrawals| == MAX_WITHDRAWALS_PER_PAYLOAD as int {
            // Next sweep starts after the latest withdrawal's validator index
            var next_validator_index := ((expected_withdrawals[|expected_withdrawals| - 1].validator_index as int) + 1) as int % |state.validators|;
            newNextValidatorIndex := next_validator_index;
        } else {
            // Advance sweep by the max length of the sweep if there was not a full set of withdrawals
            var next_index := (state.next_withdrawal_validator_index + MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP) as int;
            var next_validator_index := next_index % |state.validators|;
            newNextValidatorIndex := next_validator_index; 
        }
    }



    method process_bls_to_execution_change(state: BeaconState, signed_address_change: SignedBLSToExecutionChange)
    requires |state.validators| > 0
    requires signed_address_change.message.validator_index as int < |state.validators|
    requires state.validators[signed_address_change.message.validator_index].withdrawal_credentials == hash(signed_address_change.message.from_bls_pubkey)
    
    // modifies state.validators[signed_address_change.message.validator_index].withdrawal_credentials as seq<object>

    {
        var address_change := signed_address_change.message;
        assert address_change.validator_index as int < |state.validators|;

        var validator := state.validators[address_change.validator_index];

        // assert validator.withdrawal_credentials.bs[0] as int == BLS_WITHDRAWAL_PREFIX;
        assert validator.withdrawal_credentials.bs[1..32] == hash(address_change.from_bls_pubkey).bs[1..32];

        // Fork-agnostic domain since address changes are valid across forks part is assumed in my simpler version of the spec

        // var ghost_withdrawal_credentials: Hash := BLS_WITHDRAWAL_PREFIX + seq<byte>(11, 0) + address_change.to_execution_address;


        if validator.withdrawal_credentials.bs[0] as int == BLS_WITHDRAWAL_PREFIX {
            // (validator.withdrawal_credentials as Bytes32):= BLS_WITHDRAWAL_PREFIX + seq<byte>(11, 0) + address_change.to_execution_address;
        } 
    }

}