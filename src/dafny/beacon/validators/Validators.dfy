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
include "../../utils/Eth2Types.dfy"

/**
 *  Provide validator types (and their defaults) used in the Beacon Chain.
 */
module Validators {

    //  Import some constants and types
    import opened Constants
    import opened Eth2Types
   
    // Misc dependencies

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
        withdrawal_credentials: Hash,
        effective_balance: Gwei,
        slashed: bool,
        activation_eligibility_epoch: Epoch,
        activation_epoch: Epoch,
        exitEpoch: Epoch,
        withdrawable_epoch: Epoch
    )
    
    /** The default Validator. */
    const DEFAULT_VALIDATOR := Validator(
        DEFAULT_BYTES48, 0, false, FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH
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
        withdrawal_credentials: Bytes32,
        amount: Gwei
        // signature: BLSSignature
    )


    // Beacon operations

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
        // proof: array<Hash>,  
        data: DepositData
    )


    /**
     *  Withdraw.
     *  
     *  A Withdraw represents a validator withdrawal request.
     *
     *  @param  index               The index of the validator in the validator registry.
     *  @param  validator_index     The index of the validator in the validator registry.
     *  @param  address             The address of the validator.
     *  @param  amount              The amount of the withdrawal.
     */
    datatype Withdraw = Withdraw(
        index: WithdrawalIndex,
        validator_index: ValidatorIndex,
        address: ExecutionAddress,
        amount: Gwei
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
        epoch: Epoch,
        validator_index: ValidatorIndex,
        signature: BLSSignature
    )

    /**
    * The SyncAggregate type.
    *
    * @link{https://eth2book.info/capella/part3/containers/operations/}
    * The SyncAggregate is a structure used within the Ethereum consensus layer to
    * aggregate signatures from the sync committee members. This aggregate is used
    * to prove that a significant portion of the sync committee attests to the same
    * source of truth for the state of the chain during a sync committee period.
    *
    * @param sync_committee_bits       A bitvector indicating which members of the sync committee
    *                                  have contributed to the signature.
    * @param sync_committee_signature  The aggregate BLS signature from the sync committee members
    *                                  that have been set to true in the sync_committee_bits.
    *
    * This datatype is critical for light client synchronization and contributes to the overall
    * security and finality of the chain by ensuring that a quorum of the sync committee
    * has attested to the same chain data.
    */
    datatype SyncAggregate = SyncAggregate(
        sync_committee_bits: Bitvector<SYNC_COMMITTEE_SIZE>,
        sync_committee_signature: BLSSignature
    )

    /**
    * The BLSToExecutionChange type.
    *
    * @link{https://eth2book.info/capella/part3/containers/operations/}
    * The BLSToExecutionChange is a structure representing a change of the execution layer
    * address associated with a validator's BLS public key. This change is necessary when a
    * validator wishes to update the execution address where their rewards are paid out or
    * for other operational reasons.
    *
    * @param validator_index       The index of the validator requesting the change.
    * @param from_bls_pubkey       The current BLS public key of the validator.
    * @param to_execution_address  The new execution layer address to which the validator
    *                              wishes to direct their rewards and operations.
    *
    * This datatype is part of the mechanism that allows validators to update their execution
    * layer credentials without compromising the security or continuity of their validation
    * responsibilities.
    */
    datatype BLSToExecutionChange = BLSToExecutionChange(
        validator_index: ValidatorIndex,
        from_bls_pubkey: BLSPubkey,
        to_execution_address: ExecutionAddress
    )

    /**
    * The SignedBLSToExecutionChange type.
    *
    * @link{https://eth2book.info/capella/part3/containers/operations/}
    * The SignedBLSToExecutionChange is a structure that encapsulates a BLSToExecutionChange
    * message along with its corresponding BLS signature. This signed message is used to
    * authenticate the request for changing a validator's execution layer address associated
    * with their BLS public key.
    *
    * @param message    The BLSToExecutionChange message containing the details of the change.
    * @param signature  The BLS signature over the BLSToExecutionChange message, signed by the
    *                   validator's current BLS public key.
    *
    * This datatype ensures that the request to change the execution layer address is indeed
    * initiated by the rightful validator, thereby providing a secure way to update validator
    * execution layer information.
    */
    datatype SignedBLSToExecutionChange = SignedBLSToExecutionChange(
        message: BLSToExecutionChange,
        signature: BLSSignature
    )

}