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
include "../utils/Helpers.dfy"
include "IntSeDes.dfy"
include "BoolSeDes.dfy"
include "BitListSeDes.dfy"
include "BitVectorSeDes.dfy"
include "Constants.dfy"

/**
 *  SSZ library.
 *
 *  Serialise, deserialise
 */
module SSZ {

    import opened NativeTypes
    import opened NonNativeTypes
    import opened Eth2Types
    import opened IntSeDes
    import opened BoolSeDes
    import opened BitListSeDes
    import opened BitVectorSeDes
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
        requires isBasicTipe(typeOf(s))
        ensures 1 <= sizeOf(s) <= 32 && sizeOf(s) == |serialise(s)|
    {
        match s
            case Bool(_) => 1
            case Uint8(_) => 1  
            case Uint16(_) => 2 
            case Uint32(_) => 4 
            case Uint64(_) => 8
            case Uint128(_) => 16 
            case Uint256(_) => 32
    }

    /** default.
     *
     *  @param  t   Serialisable tipe.
     *  @returns    The default serialisable for this tipe.
     *
    */
    function method default(t : Tipe) : Serialisable 
        requires  !(t.Container_? || t.List_? || t.Vector_?)
        requires  t.Bytes_? || t.Bitvector_? ==> 
                match t
                    case Bytes_(n) => n > 0
                    case Bitvector_(n) => n > 0
    {
            match t 
                case Bool_ => Bool(false)
        
                case Uint8_ => Uint8(0)
               
                case Uint16_ => Uint16(0)

                case Uint32_ => Uint32(0)

                case Uint64_ => Uint64(0)

                case Uint128_ => Uint128(0)

                case Uint256_ => Uint256(0)

                case Bitlist_(limit) => Bitlist([],limit)

                case Bitvector_(len) => Bitvector(timeSeq(false,len))

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
        requires s.Vector? ==> match s case Vector(v) => isBasicTipe(typeOf(v[0]))
    {
        //  Equalities between upper bounds of uintk types and powers of two 
        constAsPowersOfTwo();

        match s
            case Bool(b) => boolToBytes(b)

            case Uint8(n) =>  uintSe(n as nat, 1)

            case Uint16(n) => uintSe(n as nat, 2)

            case Uint32(n) => uintSe(n as nat, 4)

            case Uint64(n) => uintSe(n as nat, 8)

            case Uint128(n) => uintSe(n as nat, 16)

            case Uint256(n) => uintSe(n as nat, 32)

            case Bitlist(xl,limit) => fromBitlistToBytes(xl)

            case Bitvector(xl) => fromBitvectorToBytes(xl)

            case Bytes(bs) => bs

            case List(l,_,_) => serialiseSeqOfBasics(l)

            case Vector(v) => serialiseSeqOfBasics(v)
    }

    /**
     * Serialise a sequence of basic `Serialisable` values
     * 
     * @param  s Sequence of basic `Serialisable` values
     * @returns  A sequence of bytes encoding `s`.
     */
    function method serialiseSeqOfBasics(s: seq<Serialisable>): seq<byte>
        requires forall i | 0 <= i < |s| :: isBasicTipe(typeOf(s[i]))
        requires forall i,j | 0 <= i < |s| && 0 <= j < |s| :: typeOf(s[i]) == typeOf(s[j])
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
        requires !(s.Container_? || s.List_? || s.Vector_?)
        ensures match deserialise(xs, s) 
            case Success(r) => wellTyped(r)
            case Failure => true 
    {
        match s
            case Bool_ => if |xs| == 1 && 0 <= xs[0] <= 1 then
                                var r : Serialisable := Bool(byteToBool(xs));
                                Success(r)
                            else 
                                Failure
                            
            case Uint8_ => if |xs| == 1 then
                                var r : Serialisable := Uint8(uintDes(xs));
                                Success(r)
                             else 
                                Failure

            case Uint16_ => if |xs| == 2 then
                                //  Verify wellTyped before casting to Serialisable
                                assert(wellTyped(Uint16(uintDes(xs))));
                                var r : Serialisable := Uint16(uintDes(xs));
                                Success(r)                               
                            else 
                                Failure
            
            case Uint32_ => if |xs| == 4 then
                                assert(wellTyped(Uint32(uintDes(xs))));
                                var r : Serialisable := Uint32(uintDes(xs));
                                Success(r)                               
                            else 
                                Failure

            case Uint64_ => if |xs| == 8 then
                                assert(wellTyped(Uint64(uintDes(xs))));
                                var r : Serialisable := Uint64(uintDes(xs));
                                Success(r)  
                             else 
                                Failure

            case Uint128_ => if |xs| == 16 then
                                constAsPowersOfTwo();
                                assert(wellTyped(Uint128(uintDes(xs))));
                                var r : Serialisable := Uint128(uintDes(xs));
                                Success(r)  
                             else 
                                Failure

            case Uint256_ => if |xs| == 32 then
                                constAsPowersOfTwo();
                                assert(wellTyped(Uint256(uintDes(xs))));
                                var r : Serialisable := Uint256(uintDes(xs));
                                Success(r)                              
                            else 
                                Failure
                                
            case Bitlist_(limit) => if (|xs| >= 1 && xs[|xs| - 1] >= 1) then
                                        //  Check that the decoded bitlist can fit within limit.
                                        var desBl := fromBytesToBitList(xs);
                                        if |desBl| <= limit then
                                            var r : Serialisable := Bitlist(desBl,limit);
                                            Success(r)
                                        else
                                            Failure
                                    else
                                        Failure

            case Bitvector_(len) => if |xs| > 0 && len <= |xs| * BITS_PER_BYTE < len + BITS_PER_BYTE then
                                        var r : Serialisable := Bitvector(fromBytesToBitVector(xs,len));
                                        Success(r)
                                    else
                                        Failure

            case Bytes_(len) => if 0 < |xs| == len then
                                  var r : Serialisable := Bytes(xs);
                                  Success(r)
                                else Failure
    }

    //  Specifications and Proofs
    
    /** 
     * Well typed deserialisation does not fail. 
     */
    lemma wellTypedDoesNotFail(s : Serialisable) 
        requires !(s.Container? || s.List? || s.Vector?)
        ensures deserialise(serialise(s), typeOf(s)) != Failure 
    {
         match s
            case Bool(b) => 

            case Uint8(n) => 

            case Uint16(n) =>

            case Uint32(n) =>

            case Uint64(n) =>

            case Uint128(n) =>

            case Uint256(n) =>

            case Bitlist(xl,limit) => bitlistDecodeEncodeIsIdentity(xl); 

            case Bitvector(xl) =>

            case Bytes(bs) => 
    }


    // lemma foo(xs : seq<byte>, s : Tipe) 
    //     requires deserialise(xs, s) != Failure
    //     ensures 

    /** 
     * Deserialise(serialise(-)) = Identity for well typed objects.
     */
    lemma seDesInvolutive(s : Serialisable) 
        requires !(s.Container? || s.List? || s.Vector?)
        ensures deserialise(serialise(s), typeOf(s)) == Success(s) 
    {   
        //  Proofs on equalities between upper bounds of uintk types and powers of two 
        constAsPowersOfTwo();

        match s 
            case Bitlist(xl,limit) => 
                bitlistDecodeEncodeIsIdentity(xl);

            case Bitvector(xl) =>
                bitvectorDecodeEncodeIsIdentity(xl); 

            case Bool(_) =>  //  Thanks Dafny

            case Uint8(n) => involution(n as nat, 1);

            case Uint16(n) => involution(n as nat, 2);

            case Uint32(n) => involution(n as nat, 4);

            case Uint64(n) => involution(n as nat, 8);

            case Uint128(n) =>  involution(n as nat, 16);

            case Uint256(n) =>  involution(n as nat, 32);

            case Bytes(_) => // Thanks Dafny
        
    }

    /**
     *  Serialise is injective.
     */
    lemma {:induction s1, s2} serialiseIsInjective(s1: Serialisable, s2 : Serialisable)
        requires !(s1.Container? || s1.List? || s1.Vector?)
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