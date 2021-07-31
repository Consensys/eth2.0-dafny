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

include "../../utils/Eth2Types.dfy"
include "../../ssz/Constants.dfy"
include "../../utils/Helpers.dfy"
include "../../utils/SetHelpers.dfy"
include "../validators/Validators.dfy"

/**
 *  Provide datatype attestations.
 *
 *  Checkpoints,
 *  AttestationData,
 *  PendingAttestation,
 *  Attestation,
 *  IndexAttestation
 *  
 */
module AttestationsTypes {

    import opened Helpers
    import opened Eth2Types
    import opened Constants
    import opened SetHelpers
    import opened Validators

    // Containers

    /** 
     *  A Checkpoint. 
     *  
     *  Checkpoints have a slot number that is a multiple of
     *  SLOTS_PER_EPOCH and so only the multiplier `epoch` is needed.
     *  As per the Gasper paper, checkpoints are **pairs** consisting of
     *  an epoch and a block (called Epoch Boundary Pairs in the Gasper Paper.)
     *  
     *  @note   The block that is associated with this epoch should probably have a slot
     *          number that is smaller or equal to  epoch * SLOTS_PER_EPOCH (but may
     *          be strictly smaller).
     *  
     *  @link{https://benjaminion.xyz/eth2-annotated-spec/phase0/beacon-chain/#checkpoint}
     *
     *  @param  epoch   An `Epoch` index i.e. slot number multiple of SLOTS_PER_EPOCH.
     *                  This seems to be what is called `attestation epoch` in the Gasper paper.
     *  @param  root    A (hash of a) block that corresponds to this checkpoint.
     *
     *  @note           The epochs slot is not necessarily the same as the (block) root slot.
     *                  It seems reasonable to assume that root.slot <= epoch * SLOTS_PER_EPOCH, 
     *                  although it does not seem to appear anywhere in the specs.
     */
    datatype CheckPoint = CheckPoint(
        epoch: Epoch,   //  aep attestation epoch
        root: Root      //  block root  (ep(B) may be different to epoch)
    )    

    /** Default value for CheckPoint. */
    const DEFAULT_CHECKPOINT := CheckPoint(0 as Epoch, DEFAULT_BYTES32)

    //  Attestations 

    /** 
     *  An AttestationData is (a vote for) a link/checkpoint edge  
     *  source -> target.
     *  
     *  @link{https://benjaminion.xyz/eth2-annotated-spec/phase0/beacon-chain/#attestationdata}
     *
     *  @param  slot                A slot number. The slot in which the validator makes
     *                              the attestation. ep(this) in the Gasper paper.
     *                              Each active validator should be making 
     *                              exactly one attestation per epoch. Validators have an 
     *                              assigned slot for their attestation, and it is recorded here.
     *  @param  beacon_block_root   Block determined to be the head of the chain as per running 
     *                              LMD-GHOST at that slot. This determines the chain (ancestors)
     *                              to be used to update justifications and finalisations.
     *                              The slot of this root should be less than or equal to slot.
     *  @param  source              The source (why should it be justified?) checkpoint (FFG link).
     *                              LJ(this) (latest justified) in the Gasper paper.
     *  @param  target              The target (why should it be justified) checkpoint (FFG link).
     *                              LE(this) the last epoch boundary pair for this.
     *                              This should the last epoch boundary block from *                               this.beacon_block_root i.e.LEBB(beacon_block_root) .
     *
     *  @note                       The `source` and `target` are not independent from the 
     *                              `beacon_block_root`. As specified in the Gasper paper, they 
     *                              must be LJ(this) and LE(this) respectively. 
     *                              LJ(this) is the last (most recent) justified checkpoint in 
     *                              view(beacon_block_root), and LE(this) is the last epoch boundary
     *                              pair in view(beacon_block_root).
     *  @note                       As a consequence We must have this.target.epoch == epoch(slot).
     *
     *  @note                       As (source, target) forms a pair, they should probably be 
     *                              grouped together say as a Link rather than provided separately.
     *                              The pair stands for a `vote` for a link between source and 
     *                              target.
     */
    datatype AttestationData = AttestationData(
        slot: Slot,                 //  ep(alpha) in the Gasper paper
        // index, CommitteeIndex, not used, should be the committee the validator belongs to.
        beacon_block_root: Root,    //  this attestation attest this block_root
        source: CheckPoint,         //  An checkpoint edge source/target
        target: CheckPoint          //    target.epoch == epoch(slot)
    )    

    /**
     *  Default value for AttestationData.
     */
    const DEFAULT_ATTESTATION_DATA := 
        AttestationData(0 as Slot, DEFAULT_BYTES32, DEFAULT_CHECKPOINT, DEFAULT_CHECKPOINT)

    /**
     *  Aggregations bits.
     */
    type AggregationBits = x : seq<bool> | |x| == MAX_VALIDATORS_PER_COMMITTEE witness DEFAULT_AGGREGATION_BITS

    const DEFAULT_AGGREGATION_BITS := timeSeq(false, MAX_VALIDATORS_PER_COMMITTEE)

    /**
     *  A list of validator indices that are all pair-wise different.
     */
    type AggregationValidators = x : seq<ValidatorIndex> | 
        |x| == MAX_VALIDATORS_PER_COMMITTEE 
        && forall i, j :: 0 <= i < j < |x| ==> x[i] != x[j]
    witness DEFAULT_AGGREGATION__VALIDATORS

    /** 
     *  Build a default witness value for AggregationValidators
     */
    function method makeDefaultAggrVal(): (a: seq<ValidatorIndex>)
        ensures |a| == MAX_VALIDATORS_PER_COMMITTEE
        ensures forall i :: 0 <= i < |a| ==> a[i] == i 


    const DEFAULT_AGGREGATION__VALIDATORS := makeDefaultAggrVal()

    /**
     *  A Pending attestation (including a delay slot).
     *  
     *  @param  aggregation_bits        The indices of the validastors attesting this.
     *  @param  data                    The actual data i.e. vote of the attestation.
     *  @param  aggregation_validators  The i-th value is the validator index of the 
     *                                  i-th validator in (the committee) of aggregation_bits.  
     *  @param  proposer_index          The validator index that proposed the attestation.
     *  @todo:  enable other fileds.
     */
    datatype PendingAttestation = PendingAttestation(
        aggregation_bits: AggregationBits,
        data: AttestationData,
        ghost aggregation_validators: AggregationValidators, 
        // inclusion_delay: Slot
        proposer_index: ValidatorIndex  //  uint64
    )

    /**
     *  Default value for PendingAttestation.
     */
    const DEFAULT_PENDING_ATTESTATION := 
        PendingAttestation( DEFAULT_AGGREGATION_BITS, 
                            DEFAULT_ATTESTATION_DATA, 
                            DEFAULT_AGGREGATION__VALIDATORS,
                            0)

    type ListOfAttestations = x : seq<PendingAttestation> | |x| <= MAX_ATTESTATIONS * SLOTS_PER_EPOCH as int witness DEFAULT_LIST_ATTESTATIONS

    /**
     *  Default list of attestations is the empty list.
     */
    const DEFAULT_LIST_ATTESTATIONS : seq<PendingAttestation> := []

    /**
     *  An attestation.
     *  
     *  @param  aggregation_bits    The indices of the validators in the committee 
     *                              attesting this.
     *  @param  data                The actual data i.e. vote of the attestation.
     *  @param  signature           A BLS signature. (not used)
     *
     *  @note:                      If we omit the signature we can use AttestationData 
     *                              in place of Attestation. 
     *  @note                       PendingAttestation are used instead of Attestation in 
     *                              this version of the specs.
     */
    datatype Attestation = Attestation(
        aggregation_bits: AggregationBits,
        data: AttestationData // ,
        // signature: BLSSignature
    )

    /**
     *  Default value for Attestation.
     */
    const DEFAULT_ATTESTATION := 
        Attestation(DEFAULT_AGGREGATION_BITS, DEFAULT_ATTESTATION_DATA)

    /**
     *  List of validators indices.
     */
    type CommitteeListOfValidatorIndices = x : seq<ValidatorIndex> | |x| <= MAX_VALIDATORS_PER_COMMITTEE 

    const DEFAULT_COMMITTEE_LIST_VALIDATORS_INDEX : CommitteeListOfValidatorIndices := []

    /**
     *  An indexed attestation.
     *  
     *  @param  attesting_indices   The validators indices in the current committee
     *                              attesting for this.
     *  @param  data                The actual data i.e. vote of the attestation.
     *  @param  signature           A BLS signature. (not used)
     *
     *  @note:                      If we omit the signature we can use AttestationData 
     *                              in place of Attestation.
     *
     *  @note                       Not used in this version.
     */
    datatype IndexedAttestation = IndexedAttestation(
        attesting_indices: CommitteeListOfValidatorIndices,
        data: AttestationData // ,
        // signature: BLSSignature
    )

    /**
     *  Default value for InxexedAttestation.
     */
    const DEFAULT_INDEXED_ATTESTATION := 
        IndexedAttestation(DEFAULT_COMMITTEE_LIST_VALIDATORS_INDEX, DEFAULT_ATTESTATION_DATA)

}
