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

include "../../ssz/Constants.dfy"
include "../../utils/SetHelpers.dfy"
include "../../utils/MathHelpers.dfy"
include "../../utils/NativeTypes.dfy"
include "AttestationsTypes.dfy"
include "../../utils/Eth2Types.dfy"
include "../BeaconChainTypes.dfy"
include "../Helpers.dfy"

/**
 *  Provide datatype for fork choice rule (and LMD-GHOST).
 *
 *  Some properties of validators/attestations
 *  P1: attestations must be well-formed (see ForkChoiceHelpers, isValidAttestarions)
 *  P2: each validator is assigned to one committee per epoch
 *  P3: each HONEST validator attests at most oncd per epoch.
 */
module AttestationsHelpers {

    import opened Constants
    import opened Eth2Types
    import opened NativeTypes
    import opened SetHelpers
    import opened MathHelpers
    import opened AttestationsTypes
    import opened BeaconChainTypes
    import opened BeaconHelpers


       
}
