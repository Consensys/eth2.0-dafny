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
include "../ssz/Constants.dfy"

/**
 * Misc helpers.
 */
module BeaconHelpers {

    import opened Eth2Types
    import opened Constants

    /**
     *  The epoch of a slot.
     */
    function method compute_epoch_at_slot(slot: Slot) : Epoch
    {
        (slot / SLOTS_PER_EPOCH) as Epoch
    }

}