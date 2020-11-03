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

include "../utils/Eth2Types.dfy"

/**
 *  Provide datatype for fork choice rule (and LMD-GHOST)
 */
module ForkChoiceTypes {

    import opened Eth2Types

    // Containers

    /** 
     *  A Checkpoint. 
     *  
     *  Checkpoints have a slot number that is a multiple of
     *  SLOTS_PER_EPOCH and so only the multiplier `epoch` is needed.
     *  The block that is associated with this epoch should have a slot
     *  number that is epoch * SLOTS_PER_EPOCH.
     *  
     *  @link{https://benjaminion.xyz/eth2-annotated-spec/phase0/beacon-chain/#checkpoint}
     *
     *  @param  epoch   An `Epoch` index i.e. slot number multiple of SLOTS_PER_EPOCH.
     *  @param  root    A (hash of a) block. 
     */
    datatype CheckPoint = CheckPoint(
        epoch: Epoch,
        root: Root        
    )    

     /** 
     *  A vote ie. an AttestationData.  
     *  
     *  @link{https://benjaminion.xyz/eth2-annotated-spec/phase0/beacon-chain/#attestationdata}
     *
     *  @param  slot                A slot number.
     *  @param  beacon_block_root   Block determined to be the head of the chain as per running 
     *                              LMD-GHOST at that slot. 
     *  @param  source              The source (why should it be justified?) checkpoint (FFG link).
     *  @param  target              The target (why should it be justified) checkpoint (FFG link).
     *
     *  @note   As (source, target) forms a pair, they should probably be grouped together
     *          say as a Link rather than provided separately. 
     */
    datatype AttestationData = AttestationData(
        slot: Slot,
        // index, CommitteeIndex, not used, should be the committee the validator belongs to.
        // beacon_block_root: Root, 
        source: CheckPoint,
        target: CheckPoint        
    )    

}
