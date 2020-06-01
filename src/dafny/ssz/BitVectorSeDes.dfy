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
include "../utils/MathHelpers.dfy"
include "../utils/SeqHelpers.dfy"
include "BytesAndBits.dfy"
include "Constants.dfy"

/**
 *  vector<Boolean> serialisation, desrialisation.
 *
 */
 module BitVectorSeDes {

    import opened NativeTypes
    import opened Eth2Types
    import opened BytesAndBits
    import opened Helpers
    import opened MathHelpers
    import opened SeqHelpers
    import opened Constants


    /**
     *  Encode a vector of bits into a sequence of bytes.
     *
     *  This is the inductive specification of serialise for bitvector.
     *  The `method` attribute makes it executable.
     *  This recursive function always terninates (decreases l).
     *
     *  The algorithm to encode a vector of bits works as follows:
     *  1. given a vector of bits l, 
     *  2. if |l| * 8 is not 0, append 8 - |l| % 8 zeros to l 
     *     to obtain a list of size multiplw of 8
     *     let l' = l + possibly some [0]
     *     This ensures that |l'| % 8 == 0 and can be seen as a sequence of Bytes
     *  3. Encode l' with the `list8BitsToByte` algorithm.
     *
     *  @example: l = [0,1,0,0] yields l' = [0,1,0,0] + [0,0,0,0]
     *  (add 4 0es to ensure the size of l' is multiple of 8).
     *  l' is a byte and is encoded as a uint8 `n` as follows: the bitvector 
     *  representation of n is reverse(l'). `n` in hexadecimal is thus: 0000.0010 
     *  which is the uint8 0x02.
     *  
     */
    function method {:induction l} fromBitvectorToBytes(l : seq<bool>) : seq<byte> 
        requires |l| > 0
        ensures | fromBitvectorToBytes(l) | == ceil( |l|, BITS_PER_BYTE)
        ensures | fromBitvectorToBytes(l) | > 0
        ensures (|l| % BITS_PER_BYTE) != 0 
                    ==>
                        fromBitvectorToBytes(l)[|fromBitvectorToBytes(l)|-1] as nat < power2(|l|% BITS_PER_BYTE);        
        decreases l
    {
        if ( |l| <= BITS_PER_BYTE ) then
            [ list8BitsToByte( l + timeSeq(false,BITS_PER_BYTE - |l|)) ]
        else  
            //  Encode first 8 bits and recursively encode the rest.
            [ list8BitsToByte(l[..BITS_PER_BYTE]) ] + fromBitvectorToBytes(l[BITS_PER_BYTE..])
    }


}