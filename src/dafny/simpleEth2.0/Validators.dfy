include "Constants.dfy"
include "NativeTypes.dfy"
include "Types.dfy"
// include "Attestations.dfy"

module Validators {

    //  Import some constants and types
    import opened Eth2Constants
    import opened Native__NativeTypes_s
    import opened Eth2Types
    // import opened Attestations
   
    /**
     *  A Validator.
     *
     *  @param  pubkey                          BLSPubkey.
     *  @param  withdrawal_credentials          Commitment to pubkey for withdrawals.
     *  @param  effective_balance               Balance at stake.
     *  @param  slashed                         Status epochs.    
     *  @param  activation_eligibility_epoch    When criteria for activation were met.
     *  @param  activation_epoch
     *  @param  exit_epoch: Epoch
     *  @param  withdrawable_epoch              When validator can withdraw funds.
     */
    datatype Validator = Validator(
        pubkey: BLSPubkey,
        // withdrawalCredentials: Hash,
        effectiveBalance: Gwei
        // slashed: bool,
        // activationEligibilityEpoch: int,
        // activationEpoch: int,
        // exitEpoch: int,
        // withdrawableEpoch: int
    )
    
     /**
     *  Deposit data.
     *
     *  the [DepositData] submit to the deposit contract to be verified using 
     *  the proof against the state.eth1_data.root.
     *
     *  @param  pubkey                  BLS12-381 pubkey to be used by the validator to sign messages
     *  @param  withdrawal_credentials  BLS_WITHDRAWAL_PREFIX concatenated withthe last 31 
     *                                  bytes of the hash of an offline pubkey to be used to 
     *                                  withdraw staked funds after exiting. This key is 
     *                                  not used actively in validation and can be kept in 
     *                                  cold storage.
     *  @param  amount                  Amount in Gwei that was deposited
     *  @param  signature               Signature of the DepositMessage using the 
     *                                  privkey pair of the pubkey. This is used as a 
     *                                  one-time “proof of possession” required for 
     *                                  securely using BLS keys.
     */
    datatype DepositData = DepositData(
        pubkey: BLSPubkey,
        withdrawal_credentials: Hash,
        amount: Gwei,
        signature: BLSSignature
    )

    /**
     *  Deposit.
     *  
     *  A Deposit represents incoming validator deposits from the eth1 [deposit contract].
     *
     *  @param  proof   The merkle proof against the BeaconState current 
     *                  state.eth1_data.root. Note that the + 1 in the vector 
     *                  length is due to the SSZ length mixed into the root.
     *  @param  data    The [DepositData] submit to the deposit contract to be 
     *                  verified using the proof against the state.eth1_data.root.
     */
    datatype Deposit = Deposit(
        proof: array<Hash>,  
        data: DepositData
    )

    /**
     *  Voluntary Exit.
     *
     *  A VoluntaryExit allows a validator to voluntarily exit validation duties. 
     *  This object is wrapped into a SignedVoluntaryExit which is included on chain.
     *
     * @link{https://notes.ethereum.org/@djrtwo/Bkn3zpwxB?type=view} mentions a 
     * SignedVoluntaryExit but it seems they have been merged into a single object type. 
     *
     *  @param  epoch               Minimum epoch at which this exit can be included on chain. 
     *                              Helps prevent accidental/nefarious use in chain 
     *                              reorgs/forks.
     *  @param  validator_index     The exiting validator’s index within the 
     *                              BeaconState validator registry.
     *  @param  signature           Signature of the VoluntaryExit message included in this 
     *                              object by the pubkey associated with the Validator 
     *                              defined by validator_index.
     */
    datatype VoluntaryExit = VoluntaryExit(
        epoch: int,
        validator_index: ValidatorIndex,
        signature: BLSSignature
    )

}