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
include "../utils/Helpers.dfy"
include "IntSeDes.dfy"
include "BoolSeDes.dfy"

/**
 *  SSZ library.
 *
 *  Serialise, deserialise
 */
 module SSZ {

    import opened NativeTypes
    import opened Eth2Types
    import opened IntSeDes
    import opened BoolSeDes
    import opened Helpers

    /** Encode/decode Uint8 yields Identity. */
    lemma uint8AsBytesInvolutive(n : uint8) 
        ensures bytesToUint8(uint8ToBytes(n)) == n
    {}

    /** SizeOf.
     *
     *  @param  s   A serialisable object of type uintN or bool.
     *  @returns    The number of bytes used by a serialised form of this type.
     */
    function method sizeOf(s: Serialisable): nat
        requires wellTyped(s) && s.tipe in {Uint8_, Bool_}
        ensures 1 <= sizeOf(s) <= 32 && sizeOf(s) == |serialise(s)|
    {
        match s
            case Bool(_,_) => 1
            case Uint8(_,_) => 1  
    }

    /** Serialise.
     *
     *  @param  s   The object to serialise.
     *  @returns    A sequence of bytes encoding `s`.
     */
    function method serialise(s : Serialisable) : seq<Byte> 
    {
        match s 
            case Bool(b, _) => boolToBytes(b)

            case Uint8(n, _) => uint8ToBytes(n)
    }

    /** Deserialise. 
     *  
     *  @param  xs  A sequence of bytes.
     *  @param  s   A target type for the deserialised object.
     *  @returns    Either a Success if `xs` could be deserialised
     *              in an object of type s or a Failure oytherwise.
     *  
     *  @note       It would probabaly be good to return the suffix of `xs`
     *              that has not been used in the deserialisation as well.
     */
    function method deserialise(xs : seq<Byte>, s : Tipe) : Try<Serialisable>
    {
        match s
            case Bool_ => if |xs| == 1 then
                                Success(Bool(bytesToBool(xs), Bool_))
                            else 
                                Failure
                            
            case Uint8_ => if |xs| == 1 then
                                Success(Uint8(bytesToUint8(xs[0..1]), Uint8_))
                             else 
                                Failure
    }


    //  Specifications and Proofs
    
    /** 
     * Well typed deserialisation does fail. 
     */
    lemma wellTypedDesNotFailure(s : Serialisable) 
        requires wellTyped(s)
        ensures deserialise(serialise(s), s.tipe) != Failure {
            //  Thanks Dafny.
        }
    
    /** 
     * Deserialise(seriliase()) = Identity for well typed objects.
     */
    lemma seDesInvolutive(s : Serialisable, t: Tipe) 
        requires wellTyped(s)
        ensures deserialise(serialise(s), s.tipe) == Success(s) {
            //  thanks Dafny.
        }
 }