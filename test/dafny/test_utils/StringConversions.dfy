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
 
include "../../../src/dafny/utils/NativeTypes.dfy"
include "../../../src/dafny/utils/Eth2Types.dfy"
include "../../../src/dafny/utils/Helpers.dfy"
include "../../../src/dafny/ssz/BytesAndBits.dfy"
include "../../../src/dafny/ssz/BitListSeDes.dfy"

module StringConversions
{
    import opened NativeTypes
    import opened Eth2Types
    import opened BitListSeDes

    /**
     * Converts a nibble to char
     * 
     * @param n Nibble
     * @returns Hex char representation of `n`
     */
    function method nibbleToString(n:bv4):char
    {
        ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F'][n as nat]
    }

    /**
     * The nibble to char conversion is correct
     */
    lemma nibbleToStringIsInjective(n1:bv4, n2:bv4)
    ensures n1 != n2 ==> nibbleToString(n1) != nibbleToString(n2)
    ensures n1 < n2 ==> nibbleToString(n1) < nibbleToString(n2)
    ensures n1 <= 9 ==> (nibbleToString(n1) - '0') as nat as bv4 == n1
    ensures 10 <= n1 <= 15 ==> (nibbleToString(n1) - 'A') as nat as bv4 == n1 - 10
    {}

    /**
     * Converts a byte to its character based hex representation
     * 
     * @param b  byte to convert
     * @returns   String representing the hex value of `b1
     * 
     * @example ByteToHexString(0)  == "00"
     *          ByteToHexString(16) == "10"
     */
    function method ByteToHexStringCompressed(b:byte): string
    ensures  |ByteToHexStringCompressed(b)| == 2
    {
        [nibbleToString(((b as bv8) >> 4) as bv4)]  + 
        [nibbleToString(((b as bv8) & 0x0F) as bv4)]
    }    

    /**
     * Converts a byte to its character based hex representation with "0x" 
     * prepended to it
     * 
     * @param b  byte to convert
     * @return  String representing the hex value of `b1 with "0x" prepended 
     *          to it
     * 
     * @example ByteToHexString(0)  == "0x00"
     *          ByteToHexString(16) == "0x10"
     */
    function method ByteToHexString(b:byte): string
    ensures  |ByteToHexString(b)| == 4
    ensures  ByteToHexString(b)[0..2] == "0x"
    {
        "0x" + 
        ByteToHexStringCompressed(b)
    }

    /**
     * Converts a sequence of Bytes to a sequence of hex strings representing
     * the sequence of Bytes
     *
     * @param bs  Sequence of Bytes
     * @returns Sequence of strings corresponding to the hex representation of
     * the sequence of Bytes
     */
    function method ByteSeqToHexSeqCompressed(bs:seq<byte>): seq<string>
    ensures |ByteSeqToHexSeq(bs)| == |bs|
    ensures forall i | 0 <= i < |bs| :: ByteSeqToHexSeq(bs)[i] == ByteToHexString(bs[i])
    {
        if(|bs|==0) then
            []
        else
            [ByteToHexStringCompressed(bs[0])] + ByteSeqToHexSeqCompressed(bs[1..])
    } 

    /**
     * Converts a sequence of Bytes to a sequence of "0x"-prefixed hex strings 
     * representing the sequence of Bytes 
     *
     * @param bs  Sequence of Bytes
     * @returns Sequence of "0x"-prefixed strings corresponding to the hex 
     *          representation of the sequence of Bytes
     */
    function method ByteSeqToHexSeq(bs:seq<byte>): seq<string>
    ensures |ByteSeqToHexSeq(bs)| == |bs|
    ensures forall i | 0 <= i < |bs| :: ByteSeqToHexSeq(bs)[i] == ByteToHexString(bs[i])
    {
        if(|bs|==0) then
            []
        else
            [ByteToHexString(bs[0])] + ByteSeqToHexSeq(bs[1..])
    }

    /**
     * Validates a string representation of a bitlist
     * 
     * @param s string representing a bit list
     * @returns `true` if `s` is a correct encoding
     * 
     * @example validBitListRepresentation("") == true
     *          validBitListRepresentation("100011") == true
     *          validBitListRepresentation("121") == false
     */
    predicate method validBitListRepresentation(s:string)
    {
        forall i | 0 <= i < |s| :: s[i] in {'0','1'}
    }

    /**
     * Conversion for the string representation of a bit list to a bit list
     * represented by a sequence of booleans
     * 
     * @param s String representing a bit list
     * @reutrns Sequence of booleans corresponding to the bitlist represented by `s`
     */
    function method BitListStringToBitListSeq(s:string):seq<bool>
    requires validBitListRepresentation(s)
    ensures |s| == |BitListStringToBitListSeq(s)|
    ensures forall i | 0 <= i < |s| :: && s[i] == '0' ==> BitListStringToBitListSeq(s)[i] == false
                                       && s[i] == '1' ==> BitListStringToBitListSeq(s)[i] == true 
    { 
        if |s| == 0 then
            []
        else
            (if s[0] == '0' then [false]  else [true]) +
            BitListStringToBitListSeq(s[1..]) 
    }

    /**
     * Converts a string representing a bit list to a sequence of strings
     * representing the hex value of the byte encoding of the input bit list
     *
     * @param s String representing a bit list
     * @returns Sequence of strings corresponding to the hex representation of
     * the byte econding of the `s` or ["Wrong input format"] if `s` is not a
     * proper string representation of a bit list     
     */
    function method FromBitListStringToEncodedBitListByteSeq(s:string) :seq<string>
    
    {
        if validBitListRepresentation(s) then
            ByteSeqToHexSeq(fromBitlistToBytes(BitListStringToBitListSeq(s)))
        else        
            ["Wrong input format"]   
    }

    /**
     * Converts a string representing a bit list to a sequence of strings
     * representing the hex value of the byte encoding of the input bit list and
     * prints this sequence of strings to the stdout
     * 
     * @param s String representing a bit list
     */
    method PrintBitListStringToEncodedBitListByteSeq(s:string)
    {
        print FromBitListStringToEncodedBitListByteSeq(s), "\n";
    }

    /**
     * @param bl Bitlist to convert to string
     * 
     * @returns String representation of `bl`
     */
    function method bitlistToString(bl:seq<bool>): string
    ensures |bitlistToString(bl)| == |bl|
    ensures forall i | 0 <= i < |bl| :: 
            if bl[i] then bitlistToString(bl)[i] == '1' 
            else bitlistToString(bl)[i] == '0'
    {
        if |bl| == 0 then 
            ""
        else
            [(if bl[0] then '1' else '0')] + bitlistToString(bl[1..])   
    } 

    /**
     * @param c character
     * @returns True iff `c` is a character representation of a digit
     */
    predicate method isDigit(c:char)
    {
        '0' <= c  <= '9'
    }

    /**
     * @param s String 
     * @returns True iff `s` is not empty and it is a string representation of
     * decimal number
     */
    predicate method isNumber(s:string)
    {
        |s| > 0 &&
        forall i | 0 <= i < |s| :: isDigit(s[i])
    }

    /**
     * @param s String
     * @returns Conversion of `s` to a natural number
     */
    function method atoi(s:string): nat
    requires isNumber(s)
    {
        atoir(s,0)
    }

    /**
     * Helper function for `atoi`
     * 
     * @param s String
     * @param prec Number converted so far
     * 
     * @returns The converted number
     */
    function method atoir(s:string, prec:nat): nat
    requires forall i | 0 <= i < |s| :: isDigit(s[i])
    {
        if |s| == 0 then
            prec
        else
            atoir(s[1..],prec * 10 + (s[0]-'0') as nat)
    }

    /**
     * @param n Natural number between 0 and 9 included
     * @returns Character representation of `n`
     */
    function method dtoc(n:nat):char
    requires 0 <= n <= 9
    {
        '0' + n as char
    }

    /**
     * @param n Natural number
     * @returns String representation of `n`
     */
    function method itos(n:nat):string
    {
        if n==0 then
           "0"
        else
            itosrec(n)
    }

    /** Helper for `itos`
     * @param n Natural number
     * @returns If `n > 0` then the string representation of `n` else the empty
     *          string
     */
    function method itosrec(n:nat):string
    {
        if n==0 then
           ""
        else
            itosrec(n/10) + [dtoc(n%10)]
    }

    /** Join all items of a sequence of String into a String
     *
     * @param s The sequence of String
     * @param sep The String that separate any two consecutive items
     * @returns A String composed of all the items of `s` joined by `sep`
     */
    function method join(s: seq<string>, sep:string): string
    {
        if |s| == 0 then []
        else s[0] + 
        (if |s| > 1 then sep else "")
        +
        join(s[1..],sep)
    }        

}

