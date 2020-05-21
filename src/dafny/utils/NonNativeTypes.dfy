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

 include "../utils/MathHelpers.dfy"
 include "NativeTypes.dfy"

 module NonNativeTypes {

    import opened MathHelpers
    import opened NativeTypes

    /** The type `uint128` correspond to the restriction of the `int` type to
     * positive numbers that can be expressed in binary form with no more than 128
     * bits 
     */
    newtype uint128 = i:int | 0 <= i < power2(128)

    /** The type `uint256` correspond to the restriction of the `int` type to
    * positive numbers that can be expressed in binary form with no more than 256
    * bits 
    */
    newtype uint256 = i:int | 0 <= i < power2(256)     


    // The foollowing functions and lemmas are used by the Eth2Types module and
    // are probably only requried because we currently define uint128 and
    // uint256 uisng power2
    function method castUin64ToUint256(x:uint64): uint256
    ensures castUin64ToUint256(x) as nat < 0x10000000000000000
    ensures castUin64ToUint256(x) as uint64 == x
    {
        UpperBoundForUint64(x);
        lemmaPower2IsMonotnoic(64,256);
        x as uint256
    }

    lemma UpperBoundForUint64(x:uint64)
    ensures x as nat < power2(64)
    {
        calc ==>
        {
            0x100000000 == power2(32); 
            0x10000000000000000 == power2(64);  
        }
    }

    function method castUin128ToUint256(x:uint128): uint256
    ensures castUin128ToUint256(x) as nat < power2(128)
    ensures castUin128ToUint256(x) as uint128 == x    
    {
        UpperBoundForUint128(x);
        lemmaPower2IsMonotnoic(128,256);
        x as uint256
    }   

    lemma UpperBoundForUint128(x:uint128)
    ensures x as nat < power2(128)
    {
        calc ==>
        {
            0x100000000 == power2(32); 
            0x10000000000000000 == power2(64);  
                { productRulePower2(64,64); }
            0x100000000000000000000000000000000 == power2(128);
        }
    }     
 }