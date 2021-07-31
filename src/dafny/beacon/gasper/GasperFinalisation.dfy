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

include "../../ssz/Constants.dfy"
include "../../utils/Eth2Types.dfy"
include "../../utils/NativeTypes.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../BeaconChainTypes.dfy"
include "../Helpers.dfy"
include "../forkchoice/ForkChoiceTypes.dfy"
include "./GasperEBBs.dfy"
include "./GasperJustification.dfy"

/**
 *  Provide definitions finalisation for check poits.
 *  
 *  More precisely 1-finalisation and 2-finalisation.
 */
module GasperFinalisation {
    
    import opened Constants
    import opened Eth2Types
    import opened NativeTypes
    import opened BeaconChainTypes
    import opened BeaconHelpers
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened ForkChoiceTypes
    import opened GasperEBBs
    import opened GasperJustification

    //  Finalisation definition.   
            
    /**
     *  One finalisation.
     *
     *  @param  cp      A check point.
     *  @param  store   A store.
     *  @returns        True iff the cp is finalised in the store.
     */
    predicate isOneFinalised(cp: CheckPoint, store: Store) 
        /** The block root must in the store.  */
        requires cp.root in store.blocks.Keys      
        requires 0 <= cp.epoch as nat + 1 <= MAX_UINT64 
   
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  
    {
        //  cp is justified
        isJustified(cp, store)
        //  it justifies a checkpoint at epoch cp.epoch + 1
        && exists cp2 : CheckPoint ::
            cp2.epoch == cp.epoch + 1
            && cp2.root in store.blocks.Keys 
            && cp.root in chainRoots(cp2.root, store)
            && |collectValidatorsAttestatingForLink(store.rcvdAttestations, cp, cp2)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1   
    }

    /**
     *  Two finalisation.
     *
     *  @param  cp      A check point.
     *  @param  store   A store.
     *  @returns        True iff the cp is 2-finalised in the store.
     *
     *  @note           This new definition has not been used in the proofs.
     *                  It is not guaranteed that it is correct but can easily be fixed if not.
     */
    predicate isTwoFinalised(cp: CheckPoint, store: Store) 
        /** The block root must in the store.  */
        requires cp.root in store.blocks.Keys      
        requires 0 <= cp.epoch as nat + 2 <= MAX_UINT64 
   
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  
    {
        //  cp is justified
        isJustified(cp, store)
        //  it justifies a checkpoint at epoch cp.epoch + 2
        && exists cp2 : CheckPoint ::
            cp2.epoch == cp.epoch + 2
            && cp2.root in store.blocks.Keys 
            && cp.root in chainRoots(cp2.root, store)
            && |collectValidatorsAttestatingForLink(store.rcvdAttestations, cp, cp2)| >= (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1   
        && exists cp1 : CheckPoint ::
            cp1.epoch == cp.epoch + 2
            && cp1.root in store.blocks.Keys 
            && cp.root in chainRoots(cp1.root, store)
            && isJustified(cp1, store)
    }
}
