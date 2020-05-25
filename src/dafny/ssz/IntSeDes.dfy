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

include "../utils/NativeTypes.dfy"
include "../utils/NonNativeTypes.dfy"
include "../utils/Eth2Types.dfy"
include "../utils/MathHelpers.dfy"
include "../utils/Helpers.dfy"

/**
 *  Integers serialisation, desrialisation.
 *
 */
module IntSeDes {

    import opened NativeTypes
    import opened NonNativeTypes
    import opened Eth2Types
    import opened MathHelpers
    import opened Helpers

    //  Uintk serialisation and deserielisation.

    /** Uint8. */
    function method uint8ToBytes(n: uint8) : seq<byte> 
        ensures |uint8ToBytes(n)| == 1
    {
        [n as byte]
    }
 
    function method byteToUint8(b: byte) : uint8
    {
        (b as uint8)
    }

    /** Encode/decode Uint8 yields Identity. */
    lemma uint8AsBytesInvolutive(n : uint8) 
        ensures byteToUint8(uint8ToBytes(n)[0]) == n
    {   //  Thanks Dafny
    }

}