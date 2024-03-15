// include some essential dependencies
include "../utils/Eth2Types.dfy"
include "../utils/MathHelpers.dfy"
include "../utils/NativeTypes.dfy"
include "../utils/SetHelpers.dfy"
include "../utils/SeqHelpers.dfy"
include "../utils/Helpers.dfy"
include "../ssz/Constants.dfy"

include "BeaconChainTypes.dfy"
include "Helpers.s.dfy"
include "Helpers.p.dfy"
include "ActiveValidatorBounds.p.dfy"
include "attestations/AttestationsTypes.dfy"
include "validators/Validators.dfy"


module BeaconHelpersCapella {

    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened MathHelpers
    import opened NativeTypes
    import opened SetHelpers
    import opened SeqHelpers
    import opened Helpers
    import opened Constants

    import opened BeaconChainTypes
    import opened BeaconHelperSpec
    import opened BeaconHelperProofs
    import opened ActiveValidatorBounds
    import opened AttestationsTypes
    import opened Validators


    /**
     * Check if ``validator`` has an 0x01 prefixed "eth1" withdrawal credential.
     *
     * @param  validator                A validator.
     * @return                          True if the validator has an 0x01 prefixed "eth1"
     */
    // Define a method to check if a validator has an 0x01 prefixed "eth1" withdrawal credential
    predicate method has_eth1_withdrawal_credential(validator: Validator)

    {
        // Check if the first byte of withdrawal_credentials is equal to the ETH1_ADDRESS_WITHDRAWAL_PREFIX
        validator.withdrawal_credentials.bs[0] == ETH1_ADDRESS_WITHDRAWAL_PREFIX
    }


    /**
     * Check if ``validator`` is fully withdrawable.
     *
     * @param validator                A validator.
     * @param balance                  A Gwei amount.
     * @param epoch                    An epoch.
     * @return                         True if the validator is fully withdrawable.
     */
    predicate method is_fully_withdrawable_validator(validator: Validator, balance: Gwei, epoch: Epoch)

    // requires has_eth1_withdrawal_credential(validator)

    // //Prevent overflow and underflow
    // requires balance > 0 && balance <= validator.effective_balance

    {
        has_eth1_withdrawal_credential(validator) &&
        validator.withdrawable_epoch <= epoch &&
        balance > 0 &&
        balance <= validator.effective_balance
    }  

    /**
     * Check if ``validator`` is partially withdrawable.
     *
     * @param validator                A validator.
     * @param balance                  A Gwei amount.
     * @param epoch                    An epoch.
     *
     * @return                         True if the validator is partially withdrawable.
     */
    predicate method is_partially_withdrawable_validator(validator: Validator, balance: Gwei, epoch: Epoch)

    {
        has_eth1_withdrawal_credential(validator) &&
        validator.withdrawable_epoch > epoch
    }
}

