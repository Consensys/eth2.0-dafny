include "Constants.dfy"
include "NativeTypes.dfy"
include "Types.dfy"

/**
 * An Attestation is the primary message type that validators create for consensus. 
 * Although beacon blocks are only created by one validator per slot, all validators 
 * have a chance to create one attestation each epoch through their assignment to a 
 * Beacon Committee. In the optimal case, all active validators create and have an 
 * attestation included into a block during each epoch.
 */
module Attestations {

     //  Import the constants declarations
    import opened Eth2Constants
    import opened Native__NativeTypes_s
    import opened Eth2Types

    /**
     *  Attestation data
     *
     *  The primary component that is committed to by each validator.
     *
     *  @param  slot                Slot that the validator/committee is assigned to attest to
     *  @param  index               The index of the committee making the attestation 
     *                              (committee indices are mapped to shards in Phase 1)
     *  @param  beacon_block_root   Block root of the beacon block seen as the head of 
     *                              the chain during the assigned slot .
     *  @param  source              The most recent justified Checkpoint in the 
     *                              BeaconState during the assigned slot
     *  @param  target              The Checkpoint the attesters are attempting to 
     *                              justify (the current epoch and epoch boundary block)
     */
    class AttestationData {
        var slot: int
        var index: int
        var beacon_block_root: Hash
        // var source: CheckPoint
        // var target: CheckPoint

        /** Generate a hash tree root.  */
        function hash_tree_root() : HashTreeRoot {
            None
        }
    }

    /**
     *  AttestationData and custody bit (what is that?)
     *  
     *  @param  data            The data.
     *  @param  custody_bit     Challengeable bit (SSZ-bool, 1 byte) for the custody 
     *                          of sharddata.
     */
    datatype AttestationDataAndCustodyBit =  AttestationDataAndCustodyBit(
        data: AttestationData,
        custody_bit: bool
    )

    /**
     *  Indexed Attestation data. Should probably be inheriting from attestation data ...
     *
     *  @param  custody_bit_0_indices   Indices with custody bit equal to 0.
     *  @param  custody_bit_1_indices:  Indices with custody bit equal to 1.
     *  @param  data
     *  @param  signature               the aggregate BLS signature of the attestation.
     */
    datatype IndexedAttestation = IndexedAttestation(
        custody_bit_0_indices: seq<ValidatorIndex>,
        custody_bit_1_indices: seq<ValidatorIndex>,
        data: AttestationData,
        signature: BLSSignature
    )

    /**
     *  Pending attestation (What is that?).
     *
     *  @param  aggregation_bits    Stores a single bit for each member of the committee 
     *                              assigning a value of 1 to each validator that 
     *                              participated in this aggregate signature. These 
     *                              bits are ordered by the sort of the associated 
     *                              crosslink committee.
     *  @param  data                AttestationData that was signed by the validator 
     *                              or collection of validators.
     *  @param  inclusion_delay
     *  @param  proposer_index
     */
    datatype PendingAttestation = PendingAttestation(
        aggregation_bits: seq<bool>,
        data: AttestationData,
        inclusion_delay: int,
        proposer_index: ValidatorIndex
    )    

    /**
     *  Attester slashing. 
     *  An AttesterSlashing is used to police potentially nefarious validator attestation 
     *  activity that might lead to finalizing two conflicting chains. Validators can be 
     *  slashed if they sign two conflicting attestations where conflicting is defined by 
     *  [is_slashable_attestation_data] which checks for the Casper FFG 
     *  “double” and “surround” vote conditions.
     *
     *  This does not seem to contain the culprit validator (the proposerSlashing does).
     *  I guess the attestations are the witnesses that some validator attested two
     *  two different blocks?
     *  
     *  @param  attestation_1
     *  @param  attestation_2
     */
    datatype AttesterSlashing = AttesterSlashing(
        attestation_1: IndexedAttestation,
        attestation_2: IndexedAttestation
    )

    /**
     * Attestation.
     *
     *  @param  aggregation_bits
     *  @param  data
     *  @param  custody_bits
     *  @param  signature
     */
    datatype Attestation = Attestation(
        aggregation_bits: seq<bool>,
        data: AttestationData,
        custody_bits: seq<bool>,
        signature: BLSSignature
    )

    /**
     *  Aggregate and proof (what is that?).
     *
     *  @param  index
     *  @param  selection_proof
     *  @param  aggregate
     */  
    datatype AggregateAndProof = AggregateAndProof(
        index: ValidatorIndex,
        selection_proof: BLSSignature,
        aggregate: Attestation
    )

}
