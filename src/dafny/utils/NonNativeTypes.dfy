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
 }