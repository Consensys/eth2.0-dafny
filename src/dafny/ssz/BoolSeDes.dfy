/*
 * Copyright 2020 ConsenSys AG.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 */

include "../utils/NativeTypes.dfy"
include "../utils/Eth2Types.dfy"

/**
 *  Boolean serialisation, desrialisation.
 *
 */
module BoolSeDes {

    import opened NativeTypes
    import opened Eth2Types

    /**
     *  Convert a bool into a byte.
     */
    function method boolToBytes(b: bool) : seq<Byte> 
        ensures | boolToBytes(b) | == 1 
    {
        if b then 
            [1 as Byte]
        else 
            [0 as Byte]
    }

    /** 
     *  Convert a sequence of one Byte into a bool.
     */
    function method bytesToBool(xs: seq<Byte>) : bool
        requires | xs | == 1 
    {
       (xs[0] as nat) > 0
    }

}