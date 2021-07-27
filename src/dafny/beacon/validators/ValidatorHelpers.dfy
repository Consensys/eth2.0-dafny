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
include "../../utils/MathHelpers.dfy"
include "../../utils/NativeTypes.dfy"
include "../../ssz/Constants.dfy"

include "../BeaconChainTypes.dfy"
include "Validators.dfy"
include "../attestations/AttestationsTypes.dfy"
//include "../Helpers.dfy"

/**
 *  Beacon chain helper functional specifications.
 */
module ValidatorHelpers {

    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened MathHelpers
    import opened NativeTypes
    import opened Constants

    import opened BeaconChainTypes
    import opened Validators
    import opened AttestationsTypes
    //import opened BeaconHelpers

    
    
}