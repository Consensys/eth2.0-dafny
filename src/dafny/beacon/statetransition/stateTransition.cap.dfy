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
            requires |s.validators| == |s.balances|
            requires minimumActiveValidators(s)
            requires s.next_withdrawal_validator_index as int < |s.validators|

            {
                var epoch := get_current_epoch(s);
                // var withdrawal_index := s.next_withdrawal_index;
                // var validator_index := s.next_withdrawal_validator_index;
                withdrawals := [];
                var bound := min(|s.validators|, MAX_VALIDATORS_PER_WITHDRAWAL_SWEEP as nat) as nat;
                var i: int;

                for i := 0 to bound - 1 {
                    var validator := s.validators[s.next_withdrawal_validator_index];
                    var balance := s.balances[s.next_withdrawal_validator_index];
                    // var addressBytes := validator.withdrawal_credentials.bs[12..32];
                    // var address: ExecutionAddress := addressBytes;
                    var newNextWithdrawalValidatorIndex := s.next_withdrawal_validator_index as int;
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
                            amount := balance - MAX_EFFECTIVE_BALANCE
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


    
        
    // method process_withdrawals(state: BeaconState, payload: ExecutionPayload)
    // {
    //     var expected_withdrawals := get_expected_withdrawals(state);
    //     assert |payload.withdrawals| == |expected_withdrawals|;

    //     var newNextWithdrawalIndex := state.next_withdrawal_index;
    //     var newNextValidatorIndex := state.next_withdrawal_validator_index;


    //     for i := 0 to |expected_withdrawals| - 1 {
    //         var expected_withdrawal := expected_withdrawals[i];
    //         var withdrawal := payload.withdrawals[i];
    //         assert withdrawal == expected_withdrawal; // Verify that elements match

    //         // Call decrease_balance method with state, withdrawal.validator_index, and withdrawal.amount
    //         BeaconState() := decrease_balance(state, expected_withdrawal.validator_index, expected_withdrawal.amount);
    //     }

    //     // Update the next withdrawal index if this block contained withdrawals
    //     if |expected_withdrawals| != 0 {
    //         var latest_withdrawal := expected_withdrawals[|expected_withdrawals| - 1];
    //         newNextWithdrawalIndex := latest_withdrawal.index + 1;
    //     }

    //     // Update the next validator index to start the next withdrawal sweep
    //     if |expected_withdrawals| == MAX_WITHDRAWALS_PER_PAYLOAD as int {
    //         // Next sweep starts after the latest withdrawal's validator index
    //         var next_validator_index := (expected_withdrawals[|expected_withdrawals| - 1].validator_index + 1) % |state.validators|;
    //         newNextValidatorIndex := next_validator_index;
    //     } else {
    //         // Advance sweep by the max length of the sweep if there was not a full set of withdrawals
    //         var next_index := (state.next_withdrawal_validator_index + MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP) as int;
    //         var next_validator_index := next_index % |state.validators|;
    //         newNextValidatorIndex := next_validator_index; 
    //     }
    // }


    // method process_

}
    