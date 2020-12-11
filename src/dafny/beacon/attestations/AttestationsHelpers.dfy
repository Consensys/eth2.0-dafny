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
include "AttestationsTypes.dfy"

/**
 *  Provide datatype for fork choice rule (and LMD-GHOST)
 */
module AttestationsHelpers {

    import opened Constants
    import opened SetHelpers
    import opened AttestationsTypes
    
    /**
     *  The number of attestations for a pair of checkpoints.
     *  
     *  @param  xa  The known list of attestations (votes).
     *  @param  src A checkpoint.
     *  @param  tgt A checkpoint.
     *  @returns    The number of votes for src --> tgt in `xa`.
     */
    function method countAttestationsForLink(xa : seq<PendingAttestation>, src : CheckPoint, tgt: CheckPoint) : nat
        ensures countAttestationsForLink(xa, src, tgt) <= |xa|
        decreases xa
    {
        if |xa| == 0 then 
            0
        else 
            (if xa[0].data.source == src && xa[0].data.target == tgt then 
                1

            else 
                0
            ) + countAttestationsForLink(xa[1..], src, tgt)
    }

    /**
     *  Collect set of indices of validators attesting a link.
     *
     *  @param  xa      A seq of attestations.
     *  @param  src     The source checkpoint of the link.
     *  @param  tgt     The target checkpoint of the link.
     *  @returns        The set of validators's indices that vote for (src. tgt) in `xa`. 
     */
     function collectAttestationsForLink(xa : seq<PendingAttestation>, src : CheckPoint, tgt: CheckPoint) : set<nat>
        ensures forall e :: e in collectAttestationsForLink(xa, src, tgt) ==>
            e < MAX_VALIDATORS_PER_COMMITTEE
        ensures |collectAttestationsForLink(xa, src, tgt)| <= MAX_VALIDATORS_PER_COMMITTEE
        decreases xa
    {
        if |xa| == 0 then 
            { }
        else 
            unionCardBound(trueBitsCount(xa[0].aggregation_bits),
                collectAttestationsForLink(xa[1..], src, tgt), MAX_VALIDATORS_PER_COMMITTEE);
            (if xa[0].data.source == src && xa[0].data.target == tgt then 
                trueBitsCount(xa[0].aggregation_bits)
            else 
                {}
            ) + collectAttestationsForLink(xa[1..], src, tgt)
    }

    /**
     *  Collect set of indices of validators attesting a link to a given target.
     *
     *  @param  xa      A seq of attestations.
     *  @param  tgt     The target checkpoint of the link.
     *  @returns        The set of validators's indices that vote for (_. tgt) in `xa`. 
     */
    function collectAttestationsForTarget(xa : seq<PendingAttestation>, tgt: CheckPoint) : set<nat>
        ensures forall e :: e in collectAttestationsForTarget(xa, tgt) ==>
            e < MAX_VALIDATORS_PER_COMMITTEE
        ensures |collectAttestationsForTarget(xa, tgt)| <= MAX_VALIDATORS_PER_COMMITTEE
        decreases xa
    {
        if |xa| == 0 then 
            { }
        else 
            unionCardBound(trueBitsCount(xa[0].aggregation_bits),
                collectAttestationsForTarget(xa[1..], tgt), MAX_VALIDATORS_PER_COMMITTEE);
            (if xa[0].data.target == tgt then 
                trueBitsCount(xa[0].aggregation_bits)
            else 
                {}
            ) + collectAttestationsForTarget(xa[1..], tgt)
    }

    /**
     *  Collect the set of indices for which xb[i] is true.
     *  
     *  @param  xb  A sequence of bools.
     *  @returns    The number of elements that are true in `xb`.
     */
    function trueBitsCount(xb : seq<bool>) : set<nat> 
        ensures |trueBitsCount(xb)| <= |xb|
        ensures forall i :: i in trueBitsCount(xb) <==> 0 <= i < |xb| && xb[i]
        decreases xb
    {
        if |xb| == 0 then 
            {}
        else 
            (if xb[|xb| - 1] then { |xb| - 1 } else {}) + trueBitsCount(xb[..|xb| - 1])
    }

    /**
     *  The set of validators attesting to a target is larger than the set 
     *  of validators attesting to a link with that target. 
     *
     *  @param  xa      A seq of attestations.
     *  @param  src     The source checkpoint of the link.
     *  @param  tgt     The target checkpoint of the link.
     */
    lemma {:induction xa} attForTgtLargerThanLinks(xa : seq<PendingAttestation>, src : CheckPoint, tgt: CheckPoint)
        ensures collectAttestationsForLink(xa, src, tgt) <= collectAttestationsForTarget(xa, tgt) 
        ensures |collectAttestationsForLink(xa, src, tgt)| <= |collectAttestationsForTarget(xa, tgt)| 
    {
        assert(collectAttestationsForLink(xa, src, tgt) <= collectAttestationsForTarget(xa, tgt) );
        cardIsMonotonic(collectAttestationsForLink(xa, src, tgt), collectAttestationsForTarget(xa, tgt));
    }
   
}
