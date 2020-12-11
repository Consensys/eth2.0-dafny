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

include "../../utils/Eth2Types.dfy"
include "../../ssz/Constants.dfy"
include "../../utils/Helpers.dfy"
include "../../utils/SetHelpers.dfy"

/**
 *  Provide datatype for fork choice rule (and LMD-GHOST)
 */
module AttestationsTypes {

    import opened Helpers
    import opened Eth2Types
    import opened Constants
    import opened SetHelpers

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
        epoch: Epoch,
        root: Root        
    )    

    /** Default value for CheckPoint. */
    const DEFAULT_CHECKPOINT := CheckPoint(0 as Epoch, DEFAULT_BYTES32)

    /** 
     *  A vote ie. an AttestationData.  
     *  
     *  @link{https://benjaminion.xyz/eth2-annotated-spec/phase0/beacon-chain/#attestationdata}
     *
     *  @param  slot                A slot number. The slot in which the validator makes
     *                              the attestation.
     *  @param  beacon_block_root   Block determined to be the head of the chain as per running 
     *                              LMD-GHOST at that slot. This determines the chain (ancestors)
     *                              to be used to update justifications and finalisations.
     *                              The slot of this root should be less than or equal to slot.
     *  @param  source              The source (why should it be justified?) checkpoint (FFG link).
     *  @param  target              The target (why should it be justified) checkpoint (FFG link).
     *
     *  @note                       The `source` and `target` are not independent from the 
     *                              `beacon_block_root`. As specified in the Gasper paper, they 
     *                              must be LJ(-) and LE(-) respectively. 
     *                              LJ(-) is the last (most recent) justified checkpoint in 
     *                              view(beacon_block_root), and LE(-) is the last epoch boundary
     *                              pair in view(beacon_block_root).
     *
     *  @note                       We must have target.epoch == epoch(slot).
     *
     *
     *  @note   As (source, target) forms a pair, they should probably be grouped together
     *          say as a Link rather than provided separately. 
     *          The pair stands for a `vote` for a link between source and target.
     */
    datatype AttestationData = AttestationData(
        slot: Slot,
        // index, CommitteeIndex, not used, should be the committee the validator belongs to.
        beacon_block_root: Root, 
        source: CheckPoint,
        target: CheckPoint        //    target.epoch == epoch(slot)
    )    

    /**
     *  Default value for AttestationData.
     */
    const DEFAULT_ATTESTATION_DATA := 
        AttestationData(0 as Slot,  DEFAULT_BYTES32, DEFAULT_CHECKPOINT, DEFAULT_CHECKPOINT)

    // datatype AggregationBits 
    type AggregationBits = x : seq<bool> | |x| == MAX_VALIDATORS_PER_COMMITTEE witness DEFAULT_AGGREGATION_BITS

    const DEFAULT_AGGREGATION_BITS := timeSeq(false, MAX_VALIDATORS_PER_COMMITTEE)

    /**
     *  A Pending attestation (including a delay slot).
     *  
     *  @param  data    The actual data i.e. vote of the attestation.
     *  @todo:  enable other fileds.
     */
    datatype PendingAttestation = PendingAttestation(
        aggregation_bits: AggregationBits,
        data: AttestationData
        // inclusion_delay: Slot
        // proposer_index: ValidatorIndex
    )

    /**
     *  Default value for PendingAttestation.
     */
    const DEFAULT_PENDING_ATTESTATION := PendingAttestation(DEFAULT_AGGREGATION_BITS, DEFAULT_ATTESTATION_DATA)

    // /**
    //  *  The number of attestations for a pair of checkpoints.
    //  *  
    //  *  @param  xa  The known list of attestations (votes).
    //  *  @param  src A checkpoint.
    //  *  @param  tgt A checkpoint.
    //  *  @returns    The number of votes for src --> tgt in `xa`.
    //  */
    // function method countAttestationsForLink(xa : seq<PendingAttestation>, src : CheckPoint, tgt: CheckPoint) : nat
    //     ensures countAttestationsForLink(xa, src, tgt) <= |xa|
    //     decreases xa
    // {
    //     if |xa| == 0 then 
    //         0
    //     else 
    //         (if xa[0].data.source == src && xa[0].data.target == tgt then 
    //             1

    //         else 
    //             0
    //         ) + countAttestationsForLink(xa[1..], src, tgt)
    // }

    // /**
    //  *  Collect set of indices of validators attesting a link.
    //  *
    //  *  @param  xa      A seq of attestations.
    //  *  @param  src     The source checkpoint of the link.
    //  *  @param  tgt     The target checkpoint of the link.
    //  *  @returns        The set of validators's indices that vote for (src. tgt) in `xa`. 
    //  */
    //  function collectAttestationsForLink(xa : seq<PendingAttestation>, src : CheckPoint, tgt: CheckPoint) : set<nat>
    //     ensures forall e :: e in collectAttestationsForLink(xa, src, tgt) ==>
    //         e < MAX_VALIDATORS_PER_COMMITTEE
    //     ensures |collectAttestationsForLink(xa, src, tgt)| <= MAX_VALIDATORS_PER_COMMITTEE
    //     decreases xa
    // {
    //     if |xa| == 0 then 
    //         { }
    //     else 
    //         unionCardBound(trueBitsCount(xa[0].aggregation_bits),
    //             collectAttestationsForLink(xa[1..], src, tgt), MAX_VALIDATORS_PER_COMMITTEE);
    //         (if xa[0].data.source == src && xa[0].data.target == tgt then 
    //             trueBitsCount(xa[0].aggregation_bits)
    //         else 
    //             {}
    //         ) + collectAttestationsForLink(xa[1..], src, tgt)
    // }

    // /**
    //  *  Collect set of indices of validators attesting a link to a given target.
    //  *
    //  *  @param  xa      A seq of attestations.
    //  *  @param  tgt     The target checkpoint of the link.
    //  *  @returns        The set of validators's indices that vote for (_. tgt) in `xa`. 
    //  */
    // function collectAttestationsForTarget(xa : seq<PendingAttestation>, tgt: CheckPoint) : set<nat>
    //     ensures forall e :: e in collectAttestationsForTarget(xa, tgt) ==>
    //         e < MAX_VALIDATORS_PER_COMMITTEE
    //     ensures |collectAttestationsForTarget(xa, tgt)| <= MAX_VALIDATORS_PER_COMMITTEE
    //     decreases xa
    // {
    //     if |xa| == 0 then 
    //         { }
    //     else 
    //         unionCardBound(trueBitsCount(xa[0].aggregation_bits),
    //             collectAttestationsForTarget(xa[1..], tgt), MAX_VALIDATORS_PER_COMMITTEE);
    //         (if xa[0].data.target == tgt then 
    //             trueBitsCount(xa[0].aggregation_bits)
    //         else 
    //             {}
    //         ) + collectAttestationsForTarget(xa[1..], tgt)
    // }

    // /**
    //  *  Collect the set of indices for which xb[i] is true.
    //  *  
    //  *  @param  xb  A sequence of bools.
    //  *  @returns    The number of elements that are true in `xb`.
    //  */
    // function trueBitsCount(xb : seq<bool>) : set<nat> 
    //     ensures |trueBitsCount(xb)| <= |xb|
    //     ensures forall i :: i in trueBitsCount(xb) <==> 0 <= i < |xb| && xb[i]
    //     decreases xb
    // {
    //     if |xb| == 0 then 
    //         {}
    //     else 
    //         (if xb[|xb| - 1] then { |xb| - 1 } else {}) + trueBitsCount(xb[..|xb| - 1])
    // }

    // /**
    //  *  The set of validators attesting to a target is larger than the set 
    //  *  of validators attesting to a link with that target. 
    //  *
    //  *  @param  xa      A seq of attestations.
    //  *  @param  src     The source checkpoint of the link.
    //  *  @param  tgt     The target checkpoint of the link.
    //  */
    // lemma {:induction xa} attForTgtLargerThanLinks(xa : seq<PendingAttestation>, src : CheckPoint, tgt: CheckPoint)
    //     ensures collectAttestationsForLink(xa, src, tgt) <= collectAttestationsForTarget(xa, tgt) 
    //     ensures |collectAttestationsForLink(xa, src, tgt)| <= |collectAttestationsForTarget(xa, tgt)| 
    // {
    //     assert(collectAttestationsForLink(xa, src, tgt) <= collectAttestationsForTarget(xa, tgt) );
    //     cardIsMonotonic(collectAttestationsForLink(xa, src, tgt), collectAttestationsForTarget(xa, tgt));
    // }
   
}
