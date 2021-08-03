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

//  @dafny /dafnyVerify:1 /compile:0 /tracePOs /traceTimes /timeLimit:100 /noCheating:1


include "../utils/Eth2Types.dfy"
include "../utils/MathHelpers.dfy"
include "BeaconChainTypes.dfy"
include "../ssz/Constants.dfy"
include "validators/Validators.dfy"
include "attestations/AttestationsTypes.dfy"
include "Helpers.s.dfy"

/**
 *  Proofs relating to the beacon chain helpers.
 */
module BeaconHelperProofs {

    //  Import some constants, types and beacon chain helpers.
    import opened Eth2Types
    import opened MathHelpers
    import opened BeaconChainTypes
    import opened Constants
    import opened Validators
    import opened AttestationsTypes
    import opened BeaconHelperSpec

    /**
     *  A proof that there exists a minimum element of the set.
     *
     *  @param  s   A set of validator indices. 
     *  @return     A proof that there exists a minimum element of the set.
     *
     *  @note       This  proof is used in PickIndex (Helpers.dfy)
     *  @note       Could be changed to support a general type T and moved
     *              to SetHelpers.dfy.
     *  @link{https://stackoverflow.com/questions/51207795/the-hilbert-epsilon-operator}
     */
    lemma HasMinimum(s: set<ValidatorIndex>)
        requires s != {}
        ensures exists z :: z in s && forall y :: y in s ==> z <= y
    {
        var z :| z in s;
        if s == {z} {
            // the mimimum of a singleton set is its only element
        } else if forall y :: y in s ==> z <= y {
            // we happened to pick the minimum of s
        } else {
            // s-{z} is a smaller, nonempty set and it has a minimum
            var s' := s - {z};
            HasMinimum(s');
            var z' :| z' in s' && forall y :: y in s' ==> z' <= y;
            // the minimum of s' is the same as the miminum of s
            forall y | y in s
            ensures z' <= y
            {
            if
            case y in s' =>
                assert z' <= y;  // because z' in minimum in s'
            case y == z =>
                var k :| k in s && k < z;  // because z is not minimum in s
                assert k in s';  // because k != z
            }
        }
    }

    /**
     *  A proof that an amount (as a nat) doesn't cause a Gwei overflow.
     *
     *  @param  i   A positive integer. 
     *  @return     A proof that i < 0x10000000000000000.
     *
     *  @note       This proof is assumed.
     *  @note       A proof could be constructed on the basis of the total amount
     *              of Eth in existence.
     */
    lemma {:axiom } AssumeNoGweiOverflow(i: nat)
        ensures i < 0x10000000000000000
    // {}

    /**
     *  A proof that an amount (as a nat) added to each balance doesn't cause a Gwei overflow.
     *
     *  @param  s   A beacon state. 
     *  @param  r   A sqeuence of amounts. 
     *  @return     A proof that s.balances[i] + r[i] < 0x10000000000000000.
     *
     *  @note       This proof is assumed.
     *  @note       A proof could be constructed on the basis of the total amount
     *              of Eth in existence.
     */
    lemma {:axiom } AssumeNoGweiOverflowToAddRewards(s: BeaconState, r: seq<Gwei>)
        requires |r| <= |s.balances| 
        ensures forall i :: 0 <= i < |r| ==> s.balances[i] as nat + r[i] as nat < 0x10000000000000000
    // {}

    /**
     *  A proof that an amount (as a nat) added to each balance doesn't cause a Gwei overflow.
     *
     *  @param  sv      A sequence of validators. 
     *  @param  adj     A positive integer. 
     *  @param  total   A positive integer. 
     *  @return         A proof that  s.validators[i].effective_balance as nat * adj / total
     *                  < 0x10000000000000000.
     *
     *  @note           This proof is assumed.
     *  @note           A proof could be constructed on the basis of the total amount
     *                  of Eth in existence.
     */
    lemma {:axiom } AssumeNoGweiOverflowToUpdateSlashings(sv: seq<Validator>, adj: nat, total: nat)
        requires total > 0
        ensures forall i :: 0 <= i < |sv| 
                ==> 0 <= sv[i].effective_balance as nat * adj / total < 0x10000000000000000
    // {}

    /**
     *  A proof that a min relative to each balance doesn't cause a Gwei overflow.
     *
     *  @param  sv      A sequence of validators. 
     *  @param  adj     A positive integer. 
     *  @param  total   A positive integer. 
     *  @return         A proof that min((s.balances[v] - s.balances[v] % EFFECTIVE_BALANCE_INCREMENT) as nat, 
     *                  MAX_EFFECTIVE_BALANCE as nat)
     *                  < 0x10000000000000000.
     *
     *  @note           This proof is assumed.
     *  @note           A proof could be constructed on the basis of the total amount
     *                  of Eth in existence.
     */
    lemma {:axiom } AssumeNoGweiOverflowToUpdateEffectiveBalance(sb: seq<Gwei>)
        ensures forall i :: 0 <= i < |sb| 
                ==> min((sb[i] - sb[i] % EFFECTIVE_BALANCE_INCREMENT) as nat, 
                         MAX_EFFECTIVE_BALANCE as nat
                       ) as nat 
                    < 0x10000000000000000
    // {}

    /**
     *  A proof that an epoch calculation (as a nat) doesn't cause an overflow.
     *
     *  @param  e   A positive integer. 
     *  @return     A proof that e < 0x10000000000000000.
     *
     *  @note       This proof is assumed.
     *  @note       This axiom is best left as an assumption, however it should
     *              be used carefully to make sure that it isn't applied to a
     *              spurious calculation.
     */
    lemma {:axiom } AssumeNoEpochOverflow(e: nat)
        ensures e < 0x10000000000000000
    // {}

    /**
     *  A proof that the finalised checkpoint epoch is before the current epoch.
     *
     *  @param  s   A beacon state. 
     *  @param  pe  The previous epoch
     *  @return     A proof that s.finalised_checkpoint.epoch <= get_previous_epoch(s).
     *
     *  @note       This proof is assumed.
     *  @note       A strategy to remove use of this axiom would be show that it is
     *              true at the time s.finalised_checkpoint.epoch is set or changed,
     *              and then thus that it remains invariant.
     */
    lemma {:axiom } AssumeFinalisedCheckpointBeforeCurrentEpoch(s: BeaconState, pe: Epoch)
        ensures s.finalised_checkpoint.epoch <= pe
    // {}

    /**
     *  A proof that an attestation inclusion delay is greater than zero.
     *
     *  @param  a   A pending attestation. 
     *  @return     A proof that a.inclusion_delay > 0.
     *
     *  @note       This proof is assumed.
     *  @note       A strategy to remove use of this axiom would be show that it is
     *              true at the time a.inclusion_delay is set or changed,
     *              and then thus that it remains invariant.
     */
    lemma {:axiom } AssumeAttesttionInclusionDelayGreaterThanZero(a: PendingAttestation)
        ensures a.inclusion_delay > 0
    // {}


    /**
     *  A proof that if the total balance of sequence ``sb`` plus an amount d maintain the
     *  uint64 bound then each element in ``sb`` plus d would also maintain that bound.
     *
     *  @param  a   A pending attestation. 
     *  @return     A proof that forall i :: 0 <= i < |sb| 
     *              ==> sb[i] as int + d.data.amount as int < 0x10000000000000000.
     */
    lemma individualBalanceBoundMaintained(sb: seq<Gwei>, d: Deposit)
        requires total_balances(sb) + d.data.amount as int < 0x10000000000000000
        ensures forall i :: 0 <= i < |sb| ==> sb[i] as int + d.data.amount as int < 0x10000000000000000
    {
        if |sb| == 0 {
            // Thanks Dafny
        }
        else {
            assert total_balances(sb) == sb[0] as int + total_balances(sb[1..]);
            assert sb[0] as int + d.data.amount as int < 0x10000000000000000;
            assert total_balances(sb[1..]) + d.data.amount as int < 0x10000000000000000;
            individualBalanceBoundMaintained(sb[1..],d);
        }
    } 
    
    /**
     *  A proof of the distributive property of total_balances.
     *
     *  @param  sb1     A sequence of gwei. 
     *  @param  sb2     A sequence of gwei. 
     *  @return         A proof that total_balances(sb1 + sb2) 
     *                  == total_balances(sb1) + total_balances(sb2) .
     */
    lemma distBalancesProp(sb1: seq<Gwei>, sb2: seq<Gwei>)
        ensures total_balances(sb1 + sb2) == total_balances(sb1) + total_balances(sb2) 
    {
        if |sb1| == 0 {
            assert sb1 + sb2 == sb2;
        }
        else {
            var sb := sb1 + sb2;
            //assert sb == [sb1[0]] +  sb1[1..] + sb2;
            assert sb[1..] == sb1[1..] + sb2;
            assert total_balances(sb) == sb[0] as int + total_balances(sb[1..]);
            //assert total_balances(sb1 + sb2) 
            //          == sb[0] as int + total_balances(sb1[1..] + sb2);
            distBalancesProp(sb1[1..],sb2);
        }
    }

    /**
     *  A proof of the distributive property of total_depositss.
     *
     *  @param  sd1     A sequence of deposits. 
     *  @param  sd2     A sequence of deposits. 
     *  @return         A proof that total_deposits(sd1 + sd2) 
     *                  == total_deposits(sd1) + total_balances(sd2) .
     */
    lemma distDepositsProp(sd1: seq<Deposit>, sd2: seq<Deposit>)
        ensures total_deposits(sd1 + sd2) == total_deposits(sd1) + total_deposits(sd2) 
    {
        if |sd2| == 0 {
            assert sd1 + sd2 == sd1;
        }
        else {
            var sd := sd1 + sd2;
            //assert sd == sd1 + sd2[..|sd2|-1] +  [sd2[|sd2|-1]];
            assert sd[..|sd|-1] == sd1 + sd2[..|sd2|-1] ;
            assert total_deposits(sd) 
                    == total_deposits(sd[..|sd|-1]) + sd2[|sd2|-1].data.amount as int;
            //assert total_deposits(sd1 + sd2) 
            //      == total_deposits(sd1 + sd2[..|sd2|-1] 
            //          + sd2[|sd2|-1].data.amount as int;
            distDepositsProp(sd1, sd2[..|sd2|-1] );
        }
    }
    
    /**
     *  A proof of the subset propoerty of total_depositss.
     *
     *  @param  s       A sequence of deposits. 
     *  @param  i       A positive integer. 
     *  @return         A proof that total_deposits(deposits[..i]) 
     *                  <= total_deposits(deposits).
     */
    lemma subsetDepositSumProp(deposits: seq<Deposit>, i: nat)
        requires i <= |deposits|
        ensures total_deposits(deposits[..i]) <= total_deposits(deposits);
    {
        if i == |deposits| {
            assert deposits[..i] == deposits;
        }
        else {
            //assert i < |deposits|;
            assert deposits == deposits[..i] + deposits[i..];
            assert total_deposits(deposits) 
                    == total_deposits(deposits[..i] + deposits[i..]);
            distDepositsProp(deposits[..i], deposits[i..]);
            //assert total_deposits(deposits[..i] + deposits[i..]) 
            //      == total_deposits(deposits[..i]) + total_deposits(deposits[i..]); 
        }
    }

    /**
     *   A proof to  assist with the function method get_beacon_committee.
     *
     *  @param  len_indices     A positive integer representing the number of active validators. 
     *  @param  CPS             A positive integer representing the number of committees per slot. 
     *  @param  slot            A positive integer representing the slot. 
     *  @param  cIndex          A positive integer representing the committee index. 
     *  @return                 A proof that  
     *                          len_indices * ((slot * CPS + cIndex) + 1)/ (CPS * SLOTS_PER_EPOCH as nat) 
     *                          > len_indices * (slot * CPS + cIndex) / (CPS * SLOTS_PER_EPOCH as nat).
     */
    lemma getBeaconCommitteeLemma2(len_indices: nat, CPS: nat, slot: nat, cIndex: nat)
        requires TWO_UP_5 as nat <= len_indices 
        requires CPS == max(1, 
                            min(MAX_COMMITTEES_PER_SLOT as nat, 
                                len_indices/ SLOTS_PER_EPOCH  as nat/ TARGET_COMMITTEE_SIZE as nat
                                ) as nat
                            )
        requires 0 <= slot < SLOTS_PER_EPOCH as nat // i.e. slot % SPE
        requires 0 <= cIndex < CPS

        ensures len_indices * ((slot * CPS + cIndex) + 1) / (CPS * SLOTS_PER_EPOCH as nat) 
                    > len_indices * (slot * CPS + cIndex) / (CPS * SLOTS_PER_EPOCH as nat);
    {
        natRatioRule(len_indices * ((slot * CPS + cIndex) + 1), 
                     len_indices * (slot * CPS + cIndex) , 
                     (CPS * SLOTS_PER_EPOCH as nat));

        assert len_indices * ((slot * CPS + cIndex) + 1) - len_indices  * (slot * CPS + cIndex) 
                    >=  (CPS  * SLOTS_PER_EPOCH as nat) 
                ==> len_indices * ((slot * CPS + cIndex) + 1) / (CPS  * SLOTS_PER_EPOCH as nat) 
                    > len_indices * (slot * CPS + cIndex) / (CPS * SLOTS_PER_EPOCH as nat);

        calc {
            len_indices * ((slot * CPS + cIndex) + 1) - len_indices * (slot * CPS + cIndex);
            {natExpansion(len_indices as nat, (slot * CPS + cIndex));} 
            len_indices * (slot * CPS + cIndex) + len_indices - len_indices * (slot * CPS + cIndex);
            len_indices as nat;
        }
        assert len_indices 
                == len_indices * ((slot * CPS + cIndex) + 1) - len_indices * (slot * CPS + cIndex);

        assert len_indices >= (CPS * SLOTS_PER_EPOCH as nat) 
                <==> len_indices * ((slot * CPS + cIndex) + 1) - len_indices * (slot * CPS + cIndex) 
                    >=  (CPS * SLOTS_PER_EPOCH as nat);

        assert  TWO_UP_5 as nat <= len_indices 
            ==> len_indices >= (CPS * SLOTS_PER_EPOCH as nat) 
            ==> len_indices * ((slot * CPS + cIndex) + 1) / (CPS * SLOTS_PER_EPOCH as nat) 
                > len_indices * (slot * CPS + cIndex) / (CPS * SLOTS_PER_EPOCH as nat);
    }


}