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

include "../../../../src/dafny/utils/Helpers.dfy"
include "../../../../src/dafny/utils/Eth2Types.dfy"

module {:extern "thirdpartymerkleisation"} ThirdPartyMerkleisation {
    import opened Eth2Types
    import opened NativeTypes
    function method {:extern} BitlistRoot(rbl: seq<bool>, brbl:seq<byte>, limit:nat): hash32
    function method {:extern} BitvectorRoot(rbv: seq<bool>, brbv:seq<byte>): hash32
    function method {:extern} BytesRoot(bs: seq<byte>): hash32
    
    function method {:extern} ListUint64Root(l: seq<nat>, limit:nat): hash32
    requires forall i |  0 <= i < |l| :: l[i] < 0x10000000000000000

    function method {:extern} ListBytes32Root(l: seq<seq<byte>>, limit:nat): hash32
    requires forall i |  0 <= i < |l| :: |l[i]| == 32

    function method {:extern} BeaconStateRoot(s:BeaconState): hash32
}