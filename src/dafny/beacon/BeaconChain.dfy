/*
 * Copyright 2020 ConsenSys AG.
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

include "../ssz/Constants.dfy"
include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"
// include "Attestations.dfy"
include "Validators.dfy"

module BeaconChain {

    //  Import some constants and types
    import opened Constants
    import opened NativeTypes
    import opened Eth2Types
    // import opened Attestations
    import opened Validators
    
     /**
     *  Beacon chain block header.
     *  Is it used?? Not mentioned in 
     *  @link{https://notes.ethereum.org/@djrtwo/Bkn3zpwxB?type=view} 
     *  NOT USED and duplicate of BeaconBlock (see further down)
     *
     *  @param  slot
     *  @param  parent_root
     *  @param  state_root
     *  @param  body_root
     *  @param  signature
     */
    datatype BeaconBlockHeader = BeaconBlockHeader(
        slot: int,
        parent_root: Hash,
        state_root: Hash,
        body_root: Hash,
        signature: BLSSignature
    )

    /**
     *  Beacon block body.
     *
     *  @param  randao_reveal
     *  @param  eth1_data           Eth1 data vote 
     *  @param  graffiti            Arbitrary data
     *  @param  proposer_slashings  
     *                              The proposers that are slashed.
     *  @param  attester_slashings
     *  @param  attestations
     *  @param  deposits
     *  @param  voluntary_exits
     */
    datatype BeaconBlockBody = BeaconBlockBody(
        randao_reveal: BLSSignature,
        eth1_data: Eth1Data,
        graffiti: uint32,                          //  In K: Bytes32
        // proposer_slashings: seq<ProposerSlashing>,
        // attester_slashings: seq<AttesterSlashing>,
        // attestations: seq<Attestation>,
        deposits: seq<Deposit>,
        voluntary_exits: seq<VoluntaryExit>
    )

    /**
     *  Beacon block.
     * 
     *  BeaconBlock is the primary component of the beacon chain. Each block contains a 
     *  reference (parent_root) to the block root of its parent forming a chain of 
     *  ancestors ending with the parent-less genesis block. A BeaconBlock is composed 
     *  of an outer container with a limited set of “header” fields and a BeaconBlockBody 
     *  which contains fields specific to the action of the block on state. In optimal 
     *  operation, a single BeaconBlock is proposed during each slot by the selected 
     *  proposer from the current epoch’s active validator set.
     *
     *  Seems signed beacon block has merged into this one.
     *  Where is the message?
     *
     *  @note: Note that hash_tree_root(BeaconBlock) == hash_tree_root(BeaconBlockHeader) 
     *  and thus signatures of each are equivalent.
     *
     *  @param  slot        The slot for which this block is proposed for. Must be greater 
     *                      than the slot of the block defined by parent_root
     *  @param  parent_root The block root of the parent block, forming a block chain
     *  @param  state_root  The hash root of the post state of running the state 
     *                      transition through this block
     *  @param  body        A BeaconBlockBody which contains fields for each of the 
     *                      [beacon operation] objects as well as a few proposer input fields
     *  @param  signature   Signature of the BeaconBlock message included in this object 
     *                      by the pubkey of the proposer for the given slot
     */  
    datatype BeaconBlock = BeaconBlock(
        slot: int,
        parent_root: Hash,
        state_root: Hash,
        body: BeaconBlockBody,
        signature: BLSSignature
    )  

    /**
     *  A ProposerSlashing is used to police potentially 
     *  nefarious validator block proposal activity. This 
     *  makes duplicate block proposals “expensive” to 
     *  disincentivize activity that might lead to forking 
     *  and conflicting views of the canonical chain. 
     *  Validators can be slashed if they signed two 
     *  different beacon blocks for the same slot.
     *
     *  The headers seem to correspond to different witness blocks signed 
     *  by the proposer_index which makes them slashable.
     * 
     *  @param  proposer_index  index of the validator to be slashed for double proposing
     *  @param  header_1        The signed header of the first of the two slashable beacon blocks 
     *  @param  header_2        The signed header of the second of the two slashable beacon blocks
     *  
     */ 
    datatype ProposerSlashing = ProposerSlashing(
        proposer_index: ValidatorIndex,
        header_1: BeaconBlockHeader,
        header_2: BeaconBlockHeader
    )

     /**
     *  Eth1Data2.
     */
    datatype Eth1Data = Eth1Data(
        deposit_root: Hash,
        deposit_count: uint64,
        block_hash: Hash
    )

    /**
     * Historical Batch.
     * 
     *  @param      block_roots
     *  @paran      state_roots
     */
    datatype HistoricalBatch = HistoricalBatch(
        block_roots: array<Hash>,
        state_roots: array<Hash>
    )

      
 }