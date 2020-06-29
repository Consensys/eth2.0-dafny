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
 
include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "../ssz/Constants.dfy"
include "../merkle/Merkleise.dfy"
include "../ssz/Eth2TypeDependentConstants.dfy"

module BeaconConstants {
    import opened Eth2Types
    import opened Helpers
    import opened Constants
    import opened SSZ_Merkleise
    import opened Eth2TypeDependentConstants

    /** The historical roots type.  */
    const EMPTY_HIST_ROOTS := Vector(timeSeq<Bytes32>(EMPTY_BYTES32, SLOTS_PER_HISTORICAL_ROOT as int))

    const EMPTY_BLOCK_HEADER: Serialisable := BeaconBlockHeader(Uint64(0), EMPTY_BYTES32, EMPTY_BYTES32)
    
    /**
     *  Genesis (initial) beacon state.
     *  
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#genesis-state}
     */
    const GENESIS_STATE: BeaconState := BeaconState(Uint64(0), EMPTY_BLOCK_HEADER, EMPTY_HIST_ROOTS, EMPTY_HIST_ROOTS)

    /**
     *  Genesis block (header).
     *
     *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#genesis-block}
     *  @note   In this simplified version blocks are same as headers.
     */
    const GENESIS_BLOCK_HEADER: BeaconBlockHeader := BeaconBlockHeader(
        Uint64(0),  
        EMPTY_BYTES32 , 
        getHashTreeRootBytes32(GENESIS_STATE)
    )

}