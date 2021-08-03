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
include "../../utils/NativeTypes.dfy"
include "../BeaconChainTypes.dfy"
include "../attestations/AttestationsTypes.dfy"

/**
 *  Provide datatype for fork choice rule (and LMD-GHOST)
 */
module ForkChoiceTypes {

    import opened Eth2Types
    import opened NativeTypes
    import opened BeaconChainTypes
    import opened AttestationsTypes


     /**
     *  The store (memory) recording the blocks and the states.
     *  
     *  @param  time                    Current time?
     *  @param  genesis_time            Genesis time of the genesis_state. 
     *  @param  justified_checkpoint    Latest epoch boundary block that is justified.
     *  @param  finalised_checkpoint    Latest epoch boundary block that is finalised.
     *  @param  blocks                  The map (dictionary) from hash to blocks.
     *  @param  block_states            The map (dictionary) from hash to block states.
     *
     *  @param  threshold               Not in the store as per eth2.0 specs but
     *                                  used here as the constant numebr of validators.
     *
     *  @note                   From the spec 
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/fork-choice.md#on_block}           
     *  @todo                   It seems that blocks and block_states should have the same
     *                          keys at any time. This is proved in invariant0.
     */
    datatype Store = Store (
        time: uint64,
        genesis_time: uint64,
        justified_checkpoint : CheckPoint,
        finalised_checkpoint: CheckPoint,
        // best_justified_checkpoint: CheckPoint,
        blocks : map<Root, BeaconBlock>,
        block_states : map<Root, BeaconState>,
        threshold: nat,
        ghost attestations : ListOfAttestations //  attestations received so far
        // checkpoint_states: map<CheckPoint, BeaconState>
        // latest_messages: Dict[ValidatorIndex, LatestMessage]
    )



}
