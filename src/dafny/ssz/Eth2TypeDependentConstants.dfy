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

module Eth2TypeDependentConstants {
    import opened Eth2Types
    import opened Helpers

  /** An empty chunk, all 32 bytes set to zero */
  const EMPTY_CHUNK:seq<byte> := [0, 0, 0, 0,
                                  0, 0, 0, 0,
                                  0, 0, 0, 0,
                                  0, 0, 0, 0,
                                  0, 0, 0, 0,
                                  0, 0, 0, 0,
                                  0, 0, 0, 0,
                                  0, 0, 0, 0]

    /** The default zeroed Bytes32.  */
  const SEQ_EMPTY_32_BYTES := timeSeq<byte>(0,32)   

  /**
    *  The default (empty) Bytes32
    */
  const EMPTY_BYTES32 : Bytes32 := Bytes(SEQ_EMPTY_32_BYTES)
}