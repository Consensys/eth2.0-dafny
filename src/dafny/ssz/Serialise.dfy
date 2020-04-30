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
include "../utils/Eth2Types.dfy"
include "../utils/Helpers.dfy"
include "IntSeDes.dfy"
include "BoolSeDes.dfy"
include "BitListSeDes.dfy"

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
    import opened BitListSeDes
    import opened Helpers

    /** SizeOf.
     *
     *  @param  s   A serialisable object of type uintN or bool.
     *  @returns    The number of bytes used by a serialised form of this type.
     *
     *  @note       This function needs only to be defined for basic types
     *              i.e. uintN or bool.
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

            case Bitlist(xl , _ ) => fromBitlistToBytes(xl)
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
                                Success(Bool(byteToBool(xs[0]), Bool_))
                            else 
                                Failure
                            
            case Uint8_ => if |xs| == 1 then
                                Success(Uint8(byteToUint8(xs[0]), Uint8_))
                             else 
                                Failure
                                
            case Bitlist_ => if (|xs| >= 1 && xs[|xs| - 1] >= 1) then
                                Success(Bitlist(fromBytesToBitList(xs), Bitlist_))
                            else
                                Failure
    }


    //  Specifications and Proofs
    
    /** 
     * Well typed deserialisation does not fail. 
     */
    lemma wellTypedDoesNotFail(s : Serialisable) 
        requires wellTyped(s)
        ensures deserialise(serialise(s), s.tipe) != Failure 
    {   //  Thanks Dafny.
    }
    
    /** 
     * Deserialise(serialise(-)) = Identity for well typed objects.
     */
    lemma seDesInvolutive(s : Serialisable) 
        requires wellTyped(s)
        ensures deserialise(serialise(s), s.tipe) == Success(s) 
        {   //  thanks Dafny.
            match s 
                case Bitlist(xl, Bitlist_) => 
                    calc {
                        deserialise(serialise(s), s.tipe);
                        ==
                        deserialise(serialise(Bitlist(xl, Bitlist_)), Bitlist_);
                        == 
                        deserialise(fromBitlistToBytes(xl), Bitlist_);
                        == 
                        Success(Bitlist(fromBytesToBitList(fromBitlistToBytes(xl)), Bitlist_));
                        == { bitlistDecodeEncodeIsIdentity(xl); } 
                        Success(Bitlist(xl, Bitlist_));
                    }

                case Bool(_, _) =>  //  Thanks Dafny

                case Uint8(_, _) => //  Thanks Dafny
            
        }

    /**
     *  Serialise is injective.
     */
    lemma {:induction s1, s2} serialiseIsInjective(s1: Serialisable, s2 : Serialisable)
        requires wellTyped(s1) 
        requires wellTyped(s2) 
        ensures s1.tipe == s2.tipe ==> 
                serialise(s1) == serialise(s2) ==> s1 == s2 
    {
        //  The proof follows from involution
        if (s1.tipe == s2.tipe) {
            if ( serialise(s1) == serialise(s2) ) {
                //  Show that success(s1) == success(s2) which implies s1 == s2
                calc {
                    Success(s1) ;
                    == { seDesInvolutive(s1); }
                    deserialise(serialise(s1), s1.tipe);
                    ==
                    deserialise(serialise(s2), s2.tipe);
                    == { seDesInvolutive(s2); }
                    Success(s2);
                }
            }
        }
    }
}