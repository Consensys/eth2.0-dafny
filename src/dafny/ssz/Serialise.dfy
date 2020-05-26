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
include "Constants.dfy"

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
    import opened Constants    

    /** SizeOf.
     *
     *  @param  s   A serialisable object of type uintN or bool.
     *  @returns    The number of bytes used by a serialised form of this type.
     *
     *  @note       This function needs only to be defined for basic types
     *              i.e. uintN or bool.
     */
    function method sizeOf(s: Serialisable): nat
        requires typeOf(s) in {Uint8_, Bool_}
        ensures 1 <= sizeOf(s) <= 32 && sizeOf(s) == |serialise(s)|
    {
        match s
            case Bool(_) => 1
            case Uint8(_) => 1  
    }

    /** default.
     *
     *  @param  t   Serialisable tipe.
     *  @returns    The default serialisable for this tipe.
     *
    */
    function method default(t : Tipe) : Serialisable 
    requires  !(t.Container_? || t.List_?)
    requires  t.Bytes_? ==> match t case Bytes_(n) => n > 0
    {
            match t 
                case Bool_ => Bool(false)
        
                case Uint8_ => Uint8(0)

                case Bitlist_(limit) => Bitlist([],limit)

                case Bytes_(len) => Bytes(timeSeq(0,len))
    }

    /** Serialise.
     *
     *  @param  s   The object to serialise.
     *  @returns    A sequence of bytes encoding `s`.
     */
    function method serialise(s : Serialisable) : seq<byte> 
    requires  typeOf(s) != Container_
    requires s.List? ==> match s case List(_,t,_) => isBasicTipe(t)
    {
        match s
            case Bool(b) => boolToBytes(b)

            case Uint8(n) => uint8ToBytes(n)

            case Bitlist(xl,limit) => fromBitlistToBytes(xl)

            case Bytes(bs) => bs

            case List(l,_,_) => serialiseSeqOfBasics(l)
    }

    /**
     * Serialise a sequence of basic `Serialisable` values
     * 
     * @param  s Sequence of basic `Serialisable` values
     * @returns  A sequence of bytes encoding `s`.
     */
    function method serialiseSeqOfBasics(s: seq<Serialisable>): seq<byte>
    requires forall i | 0 <= i < |s| :: isBasicTipe(typeOf(s[i]))
    ensures |s| == 0 ==> |serialiseSeqOfBasics(s)| == 0
    ensures |s| > 0  ==>|serialiseSeqOfBasics(s)| == |s| * |serialise(s[0])|
    {
        if |s| == 0 then
            []
        else
            serialise(s[0]) + 
            serialiseSeqOfBasics(s[1..])
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
    function method deserialise(xs : seq<byte>, s : Tipe) : Try<Serialisable>
    requires !(s.Container_? || s.List_?)
    {
        match s
            case Bool_ => if |xs| == 1 then
                                Success(castToSerialisable(Bool(byteToBool(xs[0]))))
                            else 
                                Failure
                            
            case Uint8_ => if |xs| == 1 then
                                Success(castToSerialisable(
                                    Uint8(byteToUint8(xs[0]))))
                             else 
                                Failure
                                
            case Bitlist_(limit) => if (|xs| >= 1 && xs[|xs| - 1] >= 1) then
                                        var desBl := fromBytesToBitList(xs);
                                        if |desBl| <= limit then
                                            Success(castToSerialisable(Bitlist(desBl,limit)))
                                        else
                                            Failure
                                    else
                                        Failure

            case Bytes_(len) => if 0 < |xs| == len then
                                  Success(castToSerialisable(Bytes(xs)))
                                else Failure
    }

    //  Specifications and Proofs
    
    /** 
     * Well typed deserialisation does not fail. 
     */
    lemma wellTypedDoesNotFail(s : Serialisable) 
        requires !(s.Container? || s.List?)
        ensures deserialise(serialise(s), typeOf(s)) != Failure 
    {
         match s
            case Bool(b) => 

            case Uint8(n) => 

            case Bitlist(xl,limit) => bitlistDecodeEncodeIsIdentity(xl); 

            case Bytes(bs) => 
    }

    /** 
     * Deserialise(serialise(-)) = Identity for well typed objects.
     */
    lemma seDesInvolutive(s : Serialisable) 
        requires !(s.Container? || s.List?)
        ensures deserialise(serialise(s), typeOf(s)) == Success(s) 
        {   //  thanks Dafny.
            match s 
                case Bitlist(xl,limit) => 
                    calc {
                        deserialise(serialise(s), typeOf(s));
                        ==
                        deserialise(serialise(Bitlist(xl,limit)), Bitlist_(limit));
                        == 
                        deserialise(fromBitlistToBytes(xl), Bitlist_(limit));
                        == { bitlistDecodeEncodeIsIdentity(xl); } 
                        Success(castToSerialisable(Bitlist(fromBytesToBitList(fromBitlistToBytes(xl)),limit)));
                        == { bitlistDecodeEncodeIsIdentity(xl); } 
                        Success(castToSerialisable(Bitlist(xl,limit)));
                    }

                case Bool(_) =>  //  Thanks Dafny

                case Uint8(_) => //  Thanks Dafny

                case Bytes(_) => // Thanks Dafny
            
        }

    /**
     *  Serialise is injective.
     */
    lemma {:induction s1, s2} serialiseIsInjective(s1: Serialisable, s2 : Serialisable)
        requires !(s1.Container? || s1.List?)
        ensures typeOf(s1) == typeOf(s2) ==> 
                    serialise(s1) == serialise(s2) ==> s1 == s2 
    {
        //  The proof follows from involution
        if ( typeOf(s1) ==  typeOf(s2)) {
            if ( serialise(s1) == serialise(s2) ) {
                //  Show that success(s1) == success(s2) which implies s1 == s2
                calc {
                    Success(s1) ;
                    == { seDesInvolutive(s1); }
                    deserialise(serialise(s1), typeOf(s1));
                    ==
                    deserialise(serialise(s2), typeOf(s2));
                    == { seDesInvolutive(s2); }
                    Success(s2);
                }
            }
        }
    }
}