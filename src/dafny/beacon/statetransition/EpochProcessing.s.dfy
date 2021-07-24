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

//  @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /trace /noCheating:1 /vcsMaxKeepGoingSplits:10 /vcsCores:12 /vcsMaxCost:1000 /vcsKeepGoingTimeout:8  /verifySeparately 


include "../../ssz/Constants.dfy"
include "../BeaconChainTypes.dfy"
include "../attestations/AttestationsTypes.dfy"
include "../attestations/AttestationsHelpers.dfy"
include "../Helpers.dfy"
include "../forkchoice/ForkChoiceTypes.dfy"
include "../gasper/GasperJustification.dfy"
include "../../utils/SetHelpers.dfy"

/**
 *  Provide a functional specification for Epoch processing.
 */
module EpochProcessingSpec {
    
    //  Import some constants, types and beacon chain helpers.
    import opened Constants
    import opened BeaconChainTypes
    import opened AttestationsTypes
    import opened AttestationsHelpers
    import opened BeaconHelpers
    import opened ForkChoiceTypes
    import opened GasperJustification
    import opened SetHelpers

    //  Specifications of justification and finalisation of a state and forward to future slot.

    predicate {:opaque} blockRootsValid(s: BeaconState, store: Store) 
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        requires get_current_epoch(s) * SLOTS_PER_EPOCH < s.slot  

        /** The block root at previous epoch is in the store. */
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys

    {
        forall br :: br in chainRoots(get_block_root(s, get_previous_epoch(s)), store)
            ==> br in chainRoots(get_block_root(s, get_current_epoch(s)), store)
    }

    /**
     *  Archive justification results on current epoch in previous epoch's record.
     *
     *  @param  s   A beacon state the slot of which is just before an Epoch boundary. 
     *  @returns    The new state with justification of CP before LEBB updated.
     *
     *  Example.
     *  epoch   0            1            2            3            4            5  
     *  CP      (b5,0)      (b5,1)        (b5,2)       (b2,3)       (b1,4)
     *          |............|............|............|............|..........s|....
     *          |............|............|............|............|..........s|s'...
     *  block   b5----------->b4---------->b3---->b2------>b1------->b0      
     *  slot    0             64           129    191      213       264
     *  bits(s) b3=1          b2=1         b1=1       b0=0                        s
     *  bits(s')              b3'0         b2'=1      b1'            b0'            s'
     *                        =======prevAttest=======>
     *
     *  assume current state is such that s.current_justified_checkpoint == (b5, 2)
     *  where epoch(s) == 4.
     *  The next state s' is the first one at the next epoch and 
     *  will have a slot that corresponds to epoch 5.
     *  Then s'.previous_justified_checkpoint is the CP justified at the previous 
     *  epoch for s' (5 - 1) and is defined by s.current_justified_checkpoint i.e.(b5, 2).
     *  The previous attestations (prevAttest) must attest from the previous checkpoint to 
     *  the LEBB(s). In the example assuming the previous checkpoint is (b5,1), 
     *  the attestations must have as target the checkpoint at previous epoch i.e. (b2, 3).
     *
     *  @note   It is assumed that the LEBB(s) cannot be justified yet.
     *
     *  If the link prevAttest is a supermajority link, then (b2,3) becomes justified.
     *  In the code below, prevAttest is get_matching_target_attestations(s, get_previous_epoch(s))
     *  and there is a supermajority if b1 is true.
     *  As for the justification bits, there are shifted in s'.
     *  The first (right to left) bit b0' is not know yet and set to default false value.
     *  The second (from the right) b1' is set to reflect the new status of the CP at 
     *  the previous epoch (3): if it becomes justified, the bit is set to 1 otherwise
     *  left to its previous value.
     *  
     */
    function updateJustificationPrevEpoch(s: BeaconState, store: Store): (s': BeaconState) 
        /** State's slot is just before an Epoch boundary. */
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0

        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        /** Slot of s is larger than slot at previous epoch. */
        // requires get_previous_epoch(s) * SLOTS_PER_EPOCH < s.slot  
        requires get_previous_epoch(s) * SLOTS_PER_EPOCH < s.slot  

        /** The block root at previous epoch is in the store. */
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys

        requires blockRootsValid(s, store)

        // requires get_block_root(s, get_previous_epoch(s)) in chainRoots(get_block_root(s, get_current_epoch(s)), store)
        // requires get_block_root(s, get_current_epoch(s)) in chainRoots(get_block_root(s, get_current_epoch(s)), store)

        /**  The previous checkpoint root is an ancestor of the root at previous epoch. */
        requires s.current_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store) 
        requires s.previous_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store) 
        requires s.previous_justified_checkpoint.epoch < get_previous_epoch(s)
        /** The attestations at previous epoch are valid. */
        requires validPrevAttestations(s, store)

        /** The justified checkpoints in s are indeed justified ands the root is in store. */
        requires s.previous_justified_checkpoint.root in store.blocks.Keys 
        requires s.current_justified_checkpoint.root in store.blocks.Keys 
        
        requires isJustified(s.previous_justified_checkpoint, store)
        requires isJustified(s.current_justified_checkpoint, store)

        /** Justification bit are right-shifted and last two are not modified.
            Bit0 (new checkpoint) is set to false, and Bit1 (previous checkpoint) 
            may be updated.
         */
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            s'.justification_bits[2..] == 
                (s.justification_bits)[1..|s.justification_bits| - 1]
            && s'.justification_bits[0] == false

        /** The updated justified checkpoints roots are in the store.   */
        ensures s'.previous_justified_checkpoint.root in store.blocks.Keys 
        ensures s'.current_justified_checkpoint.root in store.blocks.Keys  

        /** The updated justified checkpoints values are indeed justified. */
        ensures isJustified(s'.previous_justified_checkpoint, store) 
        ensures isJustified(s'.current_justified_checkpoint, store) 

        ensures s'.slot == s.slot 
        ensures s'.current_epoch_attestations == s.current_epoch_attestations
        ensures s'.previous_epoch_attestations == s.previous_epoch_attestations

        ensures s'.block_roots == s.block_roots 
        ensures get_previous_epoch(s') ==  get_previous_epoch(s)
        ensures get_block_root(s', get_previous_epoch(s')) == get_block_root(s, get_previous_epoch(s))

        ensures get_block_root(s', get_previous_epoch(s')) in store.blocks.Keys
        ensures chainRoots(get_block_root(s', get_previous_epoch(s')), store) ==
            chainRoots(get_block_root(s, get_previous_epoch(s)), store) 
        ensures s'.current_justified_checkpoint.root in chainRoots(get_block_root(s', get_previous_epoch(s')), store) 
        
        ensures get_current_epoch(s') ==  get_current_epoch(s)
        ensures get_block_root(s', get_current_epoch(s')) == get_block_root(s, get_current_epoch(s))
        ensures get_block_root(s', get_current_epoch(s')) in store.blocks.Keys

        ensures s'.current_justified_checkpoint.root in chainRoots(get_block_root(s', get_current_epoch(s')), store) 
        ensures s'.previous_justified_checkpoint == s.current_justified_checkpoint

    {
        //  This functon is opaque and we need its definition for the post-condition proof.
        reveal_blockRootsValid();
        //  The definition.
        if  get_current_epoch(s) <= GENESIS_EPOCH + 1 then 
            s 
        else 
            assert get_previous_epoch(s) >= 1 ; 
            //  Right shift justification_bits and prepend false
            var newJustBits:= [false] + (s.justification_bits)[..JUSTIFICATION_BITS_LENGTH - 1];
            //  Previous epoch checkpoint status update
            //  get attestations from previous justified to previous epoch checkpoint
            var matching_target_attestations := 
                get_matching_target_attestations(s, get_previous_epoch(s), store);
            //  Supermajority status
            var b1 := get_attesting_balance(s, matching_target_attestations) as nat * 3 
                        > get_total_active_balance(s) as nat * 2;
            var s1 := 
            s.(
                current_justified_checkpoint := 
                    if b1 then 
                        //  Checkpoint at previous epoch
                        var cp := CheckPoint(get_previous_epoch(s), get_block_root(s, get_previous_epoch(s)));
                        //  Use lemma to prove cp is justified.
                        prevEpochJustificationProof(s, store);
                        assert(isJustified(cp, store));
                        assert(cp.root == get_block_root(s, get_previous_epoch(s)));
                        assert(cp.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store));
                        assert(cp.root in chainRoots(get_block_root(s, get_current_epoch(s)), store));
                        cp 
                    else 
                        s.current_justified_checkpoint,
                previous_justified_checkpoint := s.current_justified_checkpoint,
                justification_bits := 
                    if b1 then newJustBits[1 := true] else newJustBits
            );
            s1
    }

    
    
    /**
     *  Collecting attesting validators in monotomnic wrt attestations. 
     */
    lemma collectAttestingValidatorsMonotonic(xa: seq<PendingAttestation>, xb : seq<PendingAttestation>, src: CheckPoint, tgt: CheckPoint)
        /** xa included (as list) in xb. */
        requires forall a :: a in xa ==> a in xb 
        ensures collectValidatorsAttestatingForLink(xa, src, tgt) <= 
            collectValidatorsAttestatingForLink(xb, src, tgt)
        ensures collectValidatorsIndicesAttestatingForTarget(xa, tgt) <= 
            collectValidatorsIndicesAttestatingForTarget(xb, tgt)
    {   //  Thanks Dafny
    }

    lemma prevEpochJustificationProof(s: BeaconState, store: Store)
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        /** The previous checkpoint must be valid. */
        requires get_previous_epoch(s) * SLOTS_PER_EPOCH < s.slot  
        requires get_previous_epoch(s) >= 1
        requires s.previous_justified_checkpoint.epoch < get_previous_epoch(s)
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys
        requires s.previous_justified_checkpoint.root in store.blocks.Keys 
        requires s.previous_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store)
        requires isJustified(s.previous_justified_checkpoint, store)

        /** The previous attestations must be valid. */
        requires validPrevAttestations(s, store)

        /** There must enough votes for the target. */
        requires 
            var matching_target_attestations := 
                get_matching_target_attestations(s, get_previous_epoch(s), store);
            get_attesting_balance(s, matching_target_attestations) as nat * 3 
                        > get_total_active_balance(s) as nat * 2;

        /** In that case the EBB at previous epoch is justified. */
        ensures
            var cp := CheckPoint(get_previous_epoch(s), get_block_root(s, get_previous_epoch(s)));
            isJustified(cp, store);
    {
        reveal_isJustified();
        var cp := CheckPoint(get_previous_epoch(s), get_block_root(s, get_previous_epoch(s)));
        //  Sanity check that a fixed set of validators is used
        assert(get_total_active_balance(s) as nat == MAX_VALIDATORS_PER_COMMITTEE);
         
        //  To prove that cp is justified from the previous justified
        //  checkpoint we must establish the following facts:
        assert(s.previous_justified_checkpoint.epoch < get_previous_epoch(s));
        assert(s.previous_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store));
        assert(isJustified(s.previous_justified_checkpoint, store));
        var matching_target_attestations := 
                get_matching_target_attestations(s, get_previous_epoch(s), store);

        assert(forall a :: a in matching_target_attestations ==> a in store.rcvdAttestations);
        assert(forall a :: a in matching_target_attestations ==> 
            a.data.source == s.previous_justified_checkpoint
            && a.data.target == cp);

        //  as attestations have same source and target
        calc == {
            |collectValidatorsAttestatingForLink(matching_target_attestations, s.previous_justified_checkpoint, cp)|;
            calc == {
                collectValidatorsAttestatingForLink(matching_target_attestations, s.previous_justified_checkpoint, cp);
                { sameSrcSameTgtEquiv(
                    matching_target_attestations, s.previous_justified_checkpoint, cp);}
                collectValidatorsIndices(matching_target_attestations);
            }
            |collectValidatorsIndices(matching_target_attestations)|;
            get_attesting_balance(s, matching_target_attestations) as nat;
        }
    
        // Arithmetic lemma
        assert(
                get_attesting_balance(s, matching_target_attestations) as nat * 3 
                        > get_total_active_balance(s) as nat * 2 ==>
                get_attesting_balance(s, matching_target_attestations) as nat 
                        >= (get_total_active_balance(s) as nat * 2) / 3 + 1
        );

        collectAttestingValidatorsMonotonic(matching_target_attestations, store.rcvdAttestations,
        s.previous_justified_checkpoint, cp);
        assert(
           collectValidatorsAttestatingForLink(matching_target_attestations, s.previous_justified_checkpoint, cp)
            <= collectValidatorsAttestatingForLink(store.rcvdAttestations, s.previous_justified_checkpoint, cp)
        );

        //  Monotonicity
        cardIsMonotonic(collectValidatorsAttestatingForLink(
                matching_target_attestations, s.previous_justified_checkpoint, cp),
                collectValidatorsAttestatingForLink(
                store.rcvdAttestations, s.previous_justified_checkpoint, cp));
        assert( |collectValidatorsAttestatingForLink(
                store.rcvdAttestations, s.previous_justified_checkpoint, cp)|
                >= |collectValidatorsAttestatingForLink(
                matching_target_attestations, s.previous_justified_checkpoint, cp)|);

        assert(
            |collectValidatorsAttestatingForLink(
                store.rcvdAttestations, s.previous_justified_checkpoint, cp)| >= 
                (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1 );
        //  The conditions for justification of cp are met 
        assert(isJustified(cp, store));
    }

    /**
     *  Determine justification for current epoch in next state.
     *
     *  @param  s   A beacon state the slot of which is just before an Epoch boundary. 
     *  @returns    The new state with justification of LEBB checkpoint updated.
     *
     *  Example.
     *  epoch   0            1            2            3            4            5  
     *  CP      (b5,0)      (b5,1)        (b5,2)       (b2,3)       (b1,4)
     *          |............|............|............|............|..........s|....
     *          |............|............|............|............|..........s|s'...
     *  block   b5----------->b4---------->b3---->b2------>b1------->b0      
     *  slot    0             64           129    191      213       264
     *  bits(s) b3=1          b2=1         b1=1       b0=0                        s
     *  bits(s')              b3'0         b2'=1      b1'            b0'            s'
     *                        =======prevAttest=======>
     *                                      =====currentAttest=======>
     *
     *  assume current state is such that s.current_justified_checkpoint == (b5, 2)
     *  where epoch(s) == 4.
     *  The next state s' is the first one at the next epoch and 
     *  will have a slot that corresponds to epoch 5.
     *  Then s'.previous_justified_checkpoint is the CP justified at the previous 
     *  epoch for s' (5 - 1) and is defined by s.current_justified_checkpoint i.e.(b5, 2).
     *  The previous attestations (prevAttest) must attest from the previous checkpoint to 
     *  the LEBB(s). In the example assuming the previous checkpoint is (b5,1), 
     *  the attestations must have as target the checkpoint at previous epoch i.e. (b2, 3).
     *
     *  @note   It is assumed that the LEBB(s) cannot be justified yet.
     *
     *  If the link prevAttest is a supermajority link, then (b2,3) becomes justified
     *  and this is processed in `updateJustificationPrevEpoch`.
     *  In the code below, we check the LEBB(s) is justified, and if yes
     *  advance the current_justified_checkpoint for the next state to that
     *  checkpoint, overriding the update previously made in `updateJustificationPrevEpoch`
     *  (except the justification bit at that epoch).
     *  currentAttest is get_matching_target_attestations(s, get_current_epoch(s))
     *  and there is a supermajority if b1 is true.
     *  As for the justification bits, there are shifted in s'.
     *  The first (right to left) bit b0' is set to reflect the new status of the CP at 
     *  the current epoch (4): if it becomes justified, the bit is set to 1 otherwise
     *  left to its previous value (default 0).
     *
     *  @note   The previous discussion shows that s.current_justified_checkpoint and
     *          s.previous_justified_checkpoint are not necessarily the two latest justified CPs.
     *          s.current_justified_checkpoint is the LJ, but there could be another CP (eg. at epcoh 3)
     *          that is determined justified between s.current_justified_checkpoint and
     *          s.previous_justified_checkpoint.
     *  
     */
    function updateJustificationCurrentEpoch(s: BeaconState, store: Store): (s': BeaconState) 
        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        /** State's slot is just before an Epoch boundary. */
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0

        /** Block root at current epoc is in store. */
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys

        /** Current justified checkpoint is justified and root in store. */
        requires s.current_justified_checkpoint.root in store.blocks.Keys 
        requires isJustified(s.current_justified_checkpoint, store)
        requires s.current_justified_checkpoint.epoch < get_current_epoch(s)
        requires s.current_justified_checkpoint.root in chainRoots(get_block_root(s, get_current_epoch(s)), store)
        /** Attestations to current epoch are valid. */
        requires validCurrentAttestations(s, store)
        /** First justification bit must not be already set. */
        requires s.justification_bits[0] == false 

        /** Only bit 0 can be modified, and it should be false initially. */
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            s'.justification_bits[1..] == 
                (s.justification_bits)[1..|s.justification_bits|]

        /** New current justified checkpoint is indeed justified. */
        ensures s'.current_justified_checkpoint.root in store.blocks.Keys 
        ensures isJustified(s'.current_justified_checkpoint, store)
    {
        if  get_current_epoch(s) <= GENESIS_EPOCH + 1 then 
            s 
        else 
            //  Current epoch checkpoint status update
            //  get attestations from current justified to LEBB
            var matching_target_attestations := 
                get_matching_target_attestations(s, get_current_epoch(s), store);
            //  Supermajority status
            var b1 := get_attesting_balance(s, matching_target_attestations) as nat * 3 
                        > get_total_active_balance(s) as nat * 2;
            s.(
                current_justified_checkpoint := 
                    if b1 then 
                        var cp := CheckPoint(get_current_epoch(s),get_block_root(s, get_current_epoch(s)));
                        currentEpochJustificationProof(s, store);
                        assert(isJustified(cp, store));
                        cp
                    else 
                        s.current_justified_checkpoint,
                justification_bits := 
                    if b1 then s.justification_bits[0 := true] 
                    else s.justification_bits
            )
    }

    lemma currentEpochJustificationProof(s: BeaconState, store: Store)
        /** The store is well-formed, each block with slot != 0 has a parent
            which is itself in the store. */
        requires isClosedUnderParent(store)
        requires isSlotDecreasing(store)  

        /** The previous checkpoint must be valid. */
        requires get_current_epoch(s) * SLOTS_PER_EPOCH < s.slot  
        requires 1 <= get_previous_epoch(s) 
        // requires <= get_current_epoch(state)
        requires s.current_justified_checkpoint.epoch < get_current_epoch(s)
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires s.current_justified_checkpoint.root in store.blocks.Keys 
        requires s.current_justified_checkpoint.root in chainRoots(get_block_root(s, get_current_epoch(s)), store)
        requires isJustified(s.current_justified_checkpoint, store)

        /** The previous attestations must be valid. */
        requires validCurrentAttestations(s, store)

        /** There must enough votes fopr the target. */
        requires 
            var matching_target_attestations := 
                get_matching_target_attestations(s, get_current_epoch(s), store);
            get_attesting_balance(s, matching_target_attestations) as nat * 3 
                        > get_total_active_balance(s) as nat * 2;

        /** In that case the EBB at current epoch is justified. */
        ensures
            var cp := CheckPoint(get_current_epoch(s), get_block_root(s, get_current_epoch(s)));
            isJustified(cp, store);
    {
        reveal_isJustified();
        var cp := CheckPoint(get_current_epoch(s), get_block_root(s, get_current_epoch(s)));
        //  Sanity check that a fixed set of validators is used
        assert(get_total_active_balance(s) as nat == MAX_VALIDATORS_PER_COMMITTEE);
         
        //  To prove that cp is justified from the current justified
        //  checkpoint we must establish the following facts:
        assert(s.current_justified_checkpoint.epoch < get_current_epoch(s));
        assert(s.current_justified_checkpoint.root in chainRoots(get_block_root(s, get_current_epoch(s)), store));
        assert(isJustified(s.current_justified_checkpoint, store));
        var matching_target_attestations := 
                get_matching_target_attestations(s, get_current_epoch(s), store);

        assert(forall a :: a in matching_target_attestations ==> a in store.rcvdAttestations);
        assert(forall a :: a in matching_target_attestations ==> 
            a.data.source == s.current_justified_checkpoint
            && a.data.target == cp);

        //  as attestations have same source and target
        calc == {
            |collectValidatorsAttestatingForLink(matching_target_attestations, s.current_justified_checkpoint, cp)|;
            calc == {
                collectValidatorsAttestatingForLink(matching_target_attestations, s.current_justified_checkpoint, cp);
                { sameSrcSameTgtEquiv(
                    matching_target_attestations, s.current_justified_checkpoint, cp);}
                collectValidatorsIndices(matching_target_attestations);
            }
            |collectValidatorsIndices(matching_target_attestations)|;
            get_attesting_balance(s, matching_target_attestations) as nat;
        }
    
        // Arithmetic lemma
        assert(
                get_attesting_balance(s, matching_target_attestations) as nat * 3 
                        > get_total_active_balance(s) as nat * 2 ==>
                get_attesting_balance(s, matching_target_attestations) as nat 
                        >= (get_total_active_balance(s) as nat * 2) / 3 + 1
        );

        collectAttestingValidatorsMonotonic(matching_target_attestations, store.rcvdAttestations,
        s.current_justified_checkpoint, cp);
        assert(
           collectValidatorsAttestatingForLink(matching_target_attestations, s.current_justified_checkpoint, cp)
            <= collectValidatorsAttestatingForLink(store.rcvdAttestations, s.current_justified_checkpoint, cp)
        );

        cardIsMonotonic(collectValidatorsAttestatingForLink(
                matching_target_attestations, s.current_justified_checkpoint, cp),
                collectValidatorsAttestatingForLink(
                store.rcvdAttestations, s.current_justified_checkpoint, cp));
        assert( |collectValidatorsAttestatingForLink(
                store.rcvdAttestations, s.current_justified_checkpoint, cp)|
                >= |collectValidatorsAttestatingForLink(
                matching_target_attestations, s.current_justified_checkpoint, cp)|);

        assert(
            |collectValidatorsAttestatingForLink(
                store.rcvdAttestations, s.current_justified_checkpoint, cp)| >= 
                (2 * MAX_VALIDATORS_PER_COMMITTEE) / 3 + 1 );
        //
        assert(isJustified(cp, store));
    }


    /**
     *  Update justification is the result of the composition of 
     *  updating previous epoch justification status and current epoch justification status.
     *
     *  @param  s   A beacon state.
     *  @returns    The state s with the checkpoints statuses updated and justification
     *              bits set accordingly. 
     */
    function updateJustification(s: BeaconState, store: Store): (s': BeaconState)
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0

        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        /** Slot of s is larger than slot at previous epoch. */
        requires get_current_epoch(s) * SLOTS_PER_EPOCH < s.slot  
        requires get_previous_epoch(s) * SLOTS_PER_EPOCH < s.slot  

        /** Block root at current epoc is in store. */
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys

        requires blockRootsValid(s, store)

        /** Current justified checkpoint is justified and root in store. */ 
        requires s.current_justified_checkpoint.root in store.blocks.Keys 
        requires isJustified(s.current_justified_checkpoint, store)
        requires s.current_justified_checkpoint.epoch < get_current_epoch(s)
        requires s.current_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store)
       
        /** The block root at previous epoch is in the store. */
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys

        requires s.previous_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store) 
        requires s.previous_justified_checkpoint.epoch < get_previous_epoch(s)
        /** The attestations at previous epoch are valid. */
        requires validPrevAttestations(s, store)

        /** The justified checkpoints in s are indeed justified ands the root is in store. */
        requires s.previous_justified_checkpoint.root in store.blocks.Keys 
        requires s.current_justified_checkpoint.root in store.blocks.Keys 
        
        requires isJustified(s.previous_justified_checkpoint, store)
        requires isJustified(s.current_justified_checkpoint, store)

         /** Attestations to current epoch are valid. */
        requires validCurrentAttestations(updateJustificationPrevEpoch(s, store), store)

        //  The last two bits are copied from the two middle bits of s.justification_bits
        ensures get_current_epoch(s) > GENESIS_EPOCH + 1 ==> 
            s'.justification_bits[2..] == 
                (s.justification_bits)[1..|s.justification_bits| - 1]
        
        /** The update should preserve the follwing properties: */
        ensures s'.previous_justified_checkpoint.root in store.blocks.Keys
        ensures s'.current_justified_checkpoint.root in store.blocks.Keys
        ensures isJustified(s'.previous_justified_checkpoint, store)
        ensures isJustified(s'.current_justified_checkpoint, store)

        /** And leve unchanged some other fields of the state. */
        ensures 
            && s'.genesis_time == s.genesis_time
            && s'.slot == s.slot
            && s'.latest_block_header == s.latest_block_header
            && s'.block_roots == s.block_roots
            && s'.state_roots == s.state_roots
            && s'.eth1_data == s.eth1_data
            && s'.eth1_data_votes == s.eth1_data_votes
            && s'.eth1_deposit_index == s.eth1_deposit_index
            && s'.validators == s.validators
            && s'.previous_epoch_attestations == s.previous_epoch_attestations
            && s'.current_epoch_attestations == s.current_epoch_attestations
    {
        if get_current_epoch(s) > GENESIS_EPOCH + 1 then 
            var k := updateJustificationPrevEpoch(s, store);
            // foo202(k, store);
            assert k.current_justified_checkpoint.root in chainRoots(get_block_root(k, get_current_epoch(k)), store) ;
            var k' := updateJustificationCurrentEpoch(k, store);
            k'
        else 
            s
    }

    /**
     *  Compute the finalised checkpoint of the first state at a new epoch.
     *
     *  @param  s       A state s.
     *  @param  s'      A state that s' == updateJustification(s)
     *  @returns        The new state after updating the status of finalised_checkpoint.
     *
     *  Example.
     *                                                           LEBB(s)                         
     *  epoch   0            1            2            3            4            5  
     *  CP      (B5,0)      (B5,1)        (B5,2)       (B2,3)       (B1,4)
     *          |............|............|............|............|..........s|....
     *          |............|............|............|............|..........s|s'...
     *  block   B5----------->B4---------->B3---->B2------>B1------->B0      
     *  slot    0             64           129    191      213       264
     *  bits(s) b3=1          b2=1         b1=1       b0=0                        s
     *  bits(s')              b3'0         b2'=1      b1'            b0'            s'
     *                        =======prevAttest=======>
     *                                      LJ(s)===currentAttest===>LEBB(s)
     *
     *  @note   In the diagram above, s' is depicted as the first state in epoch 5,
     *          but in the updates, the slot (and hence epoch) of s' has njot been 
     *          incremented yet.
     *  @todo   Fix the diagram and use s'' = s'(slot := s.slot) 
     *
     *  assume current state is such that s.current_justified_checkpoint == (B5, 2)
     *  where epoch(s) == 4.
     *  After the justification updates, the justification bits have been updated.
     *  In this example we assume: 
     *  - LJ(s) == (B5,2)
     *  - LEBB(s) = (B1,4)
     *  It follows that:
     *  - s'.previous_justified_checkpoint == s.current_justified_checkpoint
     *  - s'.current_justified_checkpoint is:
     *      a) s.current_justified_checkpoint if neither prevAttest or currentAttest
     *      are supermajorities
     *      b) (B1, 4) (LEBB(s)) if currentAttest is a supermajority 
     *      c) (B2, 3) (LEBB(prevEpoch(s))) if prevAttest is a supermajority and 
     *      currentAttest is not
     *
     *  The justification bits are as as follows:
     *      b' = [isSuper(currentAttest), isSuper(PrevAttest) or b0, b1, b2].
     *
     *  @note   If b0 was already true (a supermajority from some CP), then it 
     *          remains true (justified) and in that case it must have been the LJ(s).
     *
     *  To update the status of a CP from justified to finalised, Gasper relies on 
     *  k-finalisation, with k = 1, 2.
     *  The k-finalisation definition is as follow:
     *  A checkpoint (B0, ep0) is k-finalised, k >= 1  iff:
     *  - it is the genesis block/epoch
     *  - or
     *      c1 (B0, ep0) --> (B1, ep0 + 1) --> ... -> (Bk, ep0 + k) is a chain from (B0, ep0)
     *      c2 (B0,ep0), (B1, ep0 + 1)...(Bk-1, ep0 + k - 1) are justified
     *      c3 (B0,ep0) ===Supermajority===> (Bk, ep0 + k).
     *
     *  For k = 1, A checkpoint (B0, ep0) is 1-finalised, k >= 1:
     *      c1 (B0, ep0) --> (B1, ep0 + 1) is a chain from (B0, ep0)
     *      c2 (B0,ep0) is justified
     *      c3 (B0,ep0) ===Supermajority===> (B2, ep0 + 2).
     *      
     *  For k = 2, which is what is used in the Eth2.0 specs:
     *      c1 (B0, ep0) --> (B1, ep0 + 1) --> (Bk, ep0 + 2) is a chain from (B0, ep0)
     *      c2 (B0,ep0), (B1, ep0 + 1) are justified
     *      c3 (B0,ep0) ===Supermajority===> (Bk, ep0 + 2)
     *
     *  To determine the next and most recent finalised checkpoint, we check in order the 
     *  following conditions:
     *      H4.  s.current_justified_checkpoint is at epoch - 1 and is 1-finalised
     *      H3.  s.current_justified_checkpoint is at epoch - 2 and is 2-finalised 
     *      H2.  s.previous_justified_checkpoint is at epoch - 2 and is 1-finalised 
     *      H1.  s.previous_justified_checkpoint is at epoch - 3 and is 2-finalised
     *
     *  For k = 2 and considering the last four epochs justification bits in b', this yields:
     *
     *      H1: s.previous_justified_checkpoint is at epoch 1 (epoch(s) - 3), say (B5,1) is 2-finalised iff:
     *       c1 (B5,1) --> (B5,2) --> (B2,3) is a chain [OK]
     *       c2 (B5,1), (B5,2) are justified
     *       c3 (B5,1)  ===Supermajority===> (B2,3).
     *      c1 is satisfied by construction of the chain, c2 can be determined by bits b2, b1 i.e.
     *      b3', b2'. 
     *      There is a supermajority link L from s.previous_justified_checkpoint at epoch - 3 <==> 
     *          { attestations are well formed }
     *      L = s.previous_justified_checkpoint ===Supermajority===> previous LEBB <==>
     *      (B2,3) is justified <==>
     *      b0 is true <==>
     *      b1' is true.
     *      Overall, s.previous_justified_checkpoint at epoch - 3 is 2-finalised iff b3'=b2'=b1'=true.
     *
     *      H2: s.previous_justified_checkpoint is at epoch 2 (epoch(s) - 2) is 1-finalised iff:
     *       c1 (B5,2) --> (B2,3)is a chain [OK]
     *       c2 (B5,2) is justified
     *       c3 (B5,2) ===Supermajority===> (B2,3).
     *      c2 is satisfied iff b2'=true.
     *      For c3:
     *      There is a supermajority link L from  s.previous_justified_checkpoint at epoch - 2 <==>
     *           {attestations are well-formed }
     *      L = s.previous_justified_checkpoint ===Supermajority===> previous LEBB <==>
     *      previous LEBB is (B2,3) is justified <==>
     *      b1'=true
     *      Overall, s.previous_justified_checkpoint at epoch - 2 is 1-finalised iff b2'=b1'=true.
     *      
     *  Now we check whether the current justified checkpoint can be finalised (it is at an epoch >= 
     *  previous justified.)
     *      H3: s.current_justified_checkpoint is at epoch - 2 (2) is 2-finalised iff:
     *       c1 (B5,2) --> (B2,3) --> (B1,4) is a chain [OK]
     *       c2 (B5,2), (B2,3) are justified
     *       c3 (B5,2)  ===Supermajority===> (B1,4).
     *      c2 is equivalent to b2'=b1'=true. 
     *      There is a supermajority link L from s.current_justified_checkpoint at epoch - 2 <==>
     *           {attestations are well-formed }
     *      L = s.current_justified_checkpoint ===Supermajority===> LEBB(s) <==>
     *      LEBB(s) is (B1,4) <==>
     *      (B1,4) is justified <==>
     *      b0'=true
     *  Overall, s.current_justified_checkpoint at epoch - 2 is finalised iff b2'=b1'=b0'=true.
     *
     *      H4: s.current_justified_checkpoint is at epoch - 1 (3) is 1-finalised iff:
     *       c1 (B2,3) --> (B1,4)  is a chain [OK]
     *       c2 (B2,3) is justified
     *       c3 (B2,3)  ===Supermajority===> (B1,4).
     *      c2 is equivalent to b1'==true
     *      For c3:
     *      There is a supermajority link L from  s.current_justified_checkpoint at epoch - 1 <==>
     *           {attestations are well-formed }
     *      L = s.current_justified_checkpoint ===Supermajority===> previous LEBB <==>
     *      previous LEBB is (B1,4) is justified <==>
     *      b0'=true
     *      Overall, s.current_justified_checkpoint at epoch - 1 is 1-finalised iff b0'=b1'=true.
     *      
     *  
     *  epoch   0            1            2            3            4            5  
     *  CP      (B5,0)      (B5,1)        (B5,2)       (B2,3)       (B1,4)
     *          |............|............|............|............|..........s|....
     *          |............|............|............|............|..........s|s'...
     *  block   B5----------->B4---------->B3---->B2------>B1------->B0      
     *  slot    0             64           129    191      213       264
     *  bits(s) b3=1          b2=1         b1=1       b0=0                        s
     *  bits(s')              b3'0         b2'=1      b1'            b0'            s'
     *                        =======prevAttest=======>
     *                                      LJ(s)===currentAttest===>LEBB(s)
     *
     *  @note   Python array slice a[k:l] means elements from k to l - 1 [a[k] ... a[l -1]]
     */
    function updateFinalisedCheckpoint(s': BeaconState, s: BeaconState, store: Store) : BeaconState
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0

        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        /** Slot of s is larger than slot at previous epoch. */
        requires get_current_epoch(s) * SLOTS_PER_EPOCH < s.slot  
        requires get_previous_epoch(s) * SLOTS_PER_EPOCH < s.slot  

        /** Block root at current epoc is in store. */
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys

        requires blockRootsValid(s, store)

        /** Current justified checkpoint is justified and root in store. */ 
        requires s.current_justified_checkpoint.root in store.blocks.Keys 
        requires isJustified(s.current_justified_checkpoint, store)
        requires s.current_justified_checkpoint.epoch < get_current_epoch(s)
        requires s.current_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store)
       
        /** The block root at previous epoch is in the store. */
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys

        requires s.previous_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store) 
        requires s.previous_justified_checkpoint.epoch < get_previous_epoch(s)
        /** The attestations at previous epoch are valid. */
        requires validPrevAttestations(s, store)

        /** The justified checkpoints in s are indeed justified ands the root is in store. */
        requires s.previous_justified_checkpoint.root in store.blocks.Keys 
        requires s.current_justified_checkpoint.root in store.blocks.Keys 
        
        requires isJustified(s.previous_justified_checkpoint, store)
        requires isJustified(s.current_justified_checkpoint, store)

         /** Attestations to current epoch are valid. */
        requires validCurrentAttestations(updateJustificationPrevEpoch(s, store), store)

        requires s' == updateJustification(s, store)

        ensures updateFinalisedCheckpoint(s', s, store).slot == s.slot == s'.slot
    {
        if get_current_epoch(s) <= GENESIS_EPOCH + 1 then 
            s
        else 
            //  The finalisation bits have been updated 
            var bits : seq<bool> := s'.justification_bits;
            var current_epoch := get_current_epoch(s');
            assert(get_current_epoch(s') == get_current_epoch(s));

            //  Determine next finalised checkpoint
            if (all(bits[0..2]) && s.current_justified_checkpoint.epoch == current_epoch - 1) then 
                //  H4
                // The 1st/2nd most recent epochs are justified, the 1st using the 2nd as source
                s'.(finalised_checkpoint := s.current_justified_checkpoint) 
            else if (all(bits[0..3]) && s.current_justified_checkpoint.epoch == current_epoch - 2) then 
                //  H3
                // The 1st/2nd/3rd most recent epochs are justified, the 1st using the 3rd as source
                s'.(finalised_checkpoint := s.current_justified_checkpoint) 
            else if (all(bits[1..3]) && s.previous_justified_checkpoint.epoch == current_epoch - 2) then 
                //  H2
                // The 2nd/3rd most recent epochs are justified, the 2nd using the 3rd as source
                s'.(finalised_checkpoint := s.previous_justified_checkpoint) 
            else if (all(bits[1..4]) && current_epoch >= 3 && s.previous_justified_checkpoint.epoch  == current_epoch - 3) then 
                //  H1
                //  The 2nd/3rd/4th most recent epochs are justified, the 2nd using the 4th as source
                s'.(finalised_checkpoint := s.previous_justified_checkpoint) 
            else
                s' 
    } 

    /**
     *  Combined effect of updating justification and finalisation statuses.
     *
     *  @param  s   A beacon state.
     *  @returns    The state obtained after updating the justification statuses, bits
     *              and finalisation statuses.
     */
    function updateJustificationAndFinalisation(s: BeaconState, store: Store) : BeaconState
        requires (s.slot as nat + 1) % SLOTS_PER_EPOCH as nat == 0

        /** Store is well-formed. */
        requires isClosedUnderParent(store)
        /**  The decreasing property guarantees that this function terminates. */
        requires isSlotDecreasing(store)

        /** Slot of s is larger than slot at previous epoch. */
        requires get_current_epoch(s) * SLOTS_PER_EPOCH < s.slot  
        // requires get_previous_epoch(s) * SLOTS_PER_EPOCH < s.slot  

        /** Block root at current epoc is in store. */
        requires get_block_root(s, get_current_epoch(s)) in store.blocks.Keys
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys

        requires blockRootsValid(s, store)

        /** Current justified checkpoint is justified and root in store. */ 
        requires s.current_justified_checkpoint.root in store.blocks.Keys 
        requires isJustified(s.current_justified_checkpoint, store)
        requires s.current_justified_checkpoint.epoch < get_current_epoch(s)
        requires s.current_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store)
       
        /** The block root at previous epoch is in the store. */
        requires get_block_root(s, get_previous_epoch(s)) in store.blocks.Keys

        requires s.previous_justified_checkpoint.root in chainRoots(get_block_root(s, get_previous_epoch(s)), store) 
        requires s.previous_justified_checkpoint.epoch < get_previous_epoch(s)
        /** The attestations at previous epoch are valid. */
        requires validPrevAttestations(s, store)

        /** The justified checkpoints in s are indeed justified ands the root is in store. */
        requires s.previous_justified_checkpoint.root in store.blocks.Keys 
        requires s.current_justified_checkpoint.root in store.blocks.Keys 
        
        requires isJustified(s.previous_justified_checkpoint, store)
        requires isJustified(s.current_justified_checkpoint, store)

         /** Attestations to current epoch are valid. */
        requires validCurrentAttestations(updateJustificationPrevEpoch(s, store), store)

    {
        updateFinalisedCheckpoint(updateJustification(s, store), s, store)
    }

    /**
     *  Final section of process_final_updates where attestations are rotated.
     *
     *  @param  s   A beacon state.
     *  @returns    `s` with the attestations rotated.
     */
    function finalUpdates(s: BeaconState, store: Store) : BeaconState
    {
        //  rotate the attestations and start with new empty set for current.
        s.(
            previous_epoch_attestations := s.current_epoch_attestations,
            current_epoch_attestations := []
        )
    }

}