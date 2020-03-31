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
include "../ssz/Serialise.dfy"
include "../ssz/IntSeDes.dfy"
include "../ssz/BoolSeDes.dfy"

/**
 *  SSZ_Merkleise library.
 *
 *  size_of, chunk_count, pack, merkleise, get_hash_tree_root
 */
 module SSZ_Merkleise {

    import opened NativeTypes
    import opened Eth2Types
    import opened IntSeDes
    import opened BoolSeDes
    import opened SSZ
    import opened Helpers

    predicate is32BytesChunk(c : chunk) 
    {
        |c| == 32
    }

    /** chunkCount.
     *
     *  @param  s   A serialisable object.
     *  @returns    The number of chunks (32-bytes) used by a serialised form of this type.
     *
     *  @note       For composite types and containers, a helper function may be required
     *              to complete the calculation?
     */
    function method chunkCount(s: Serialisable): nat
        requires wellTyped(s)
        ensures 1 <= chunkCount(s) && chunkCount(s) == |pack([serialise(s)])|
    {
        match s
            case Bool(_,_) => 1
            case Uint8(_, _) => 1
    } 

    
    type Bytes = seq<Byte> // i.e. the output of serialisation
    //type serialisedElement = seq<Byte> // i.e. the output of serialisation
    // bounds? should be at least 1 byte (if representing serialised output)
    // maybe call serialisedBytes or serialisedElement?

    type chunk = seq<Byte> // set size to 32 bytes

    const EMPTY_CHUNK := [0 as Byte, 0 as Byte, 0 as Byte, 0 as Byte, 
                            0 as Byte,0 as Byte,0 as Byte,0 as Byte, 
                            0 as Byte,0 as Byte,0 as Byte,0 as Byte, 
                            0 as Byte,0 as Byte,0 as Byte,0 as Byte, 
                            0 as Byte,0 as Byte,0 as Byte,0 as Byte,
                            0 as Byte,0 as Byte,0 as Byte,0 as Byte,
                            0 as Byte,0 as Byte,0 as Byte,0 as Byte, 
                            0 as Byte,0 as Byte,0 as Byte,0 as Byte]

    /** 
     *  Properties of empty chunk.
     */
    lemma emptyChunkIs32BytesOfZeros()
        ensures is32BytesChunk(EMPTY_CHUNK) 
        ensures forall i :: 0 <= i < |EMPTY_CHUNK| ==> EMPTY_CHUNK[i]== 0 as Byte 
    {   //  Thanks Dafny
    }

    /** rightPadZeros.
     *
     *  @param  b   A sequence of bytes.
     *  @returns    The sequence of bytes right padded with zero bytes to form a 32-byte chunk.
     *
     */
    function method rightPadZeros(b: Bytes): chunk
        requires |b| < 32
        ensures is32BytesChunk(rightPadZeros(b)) 
    {
        b + EMPTY_CHUNK[|b|..]
    }

    /** toChunks.
     *
     *  @param  b   A sequence of bytes i.e. a Bytes object.
     *  @returns    A sequence of 32-byte chunks, right padded with zero bytes if b % 32 != 0 
     *
     *  @note       This version of toChunks is suggested as an alternative to the in py-ssz,
     *              as this version ensures that even if |b| == 0 an EMPTY CHUNK will still 
     *              be returned. It also satisfies the toChunksProp1 and toChunksProp2 lemmas.
     *
     */
    function toChunks(b: Bytes): seq<chunk>
        ensures |toChunks(b)| > 0
        ensures forall i :: 0 <= i < |toChunks(b)| ==> is32BytesChunk(toChunks(b)[i]) 
        decreases b
    {
        if |b| < 32 then [rightPadZeros(b)]
        else    if |b| == 32 then [b] 
                else [b[..32]] + toChunks(b[32..])
    }    


    /** toChunks (py-ssz version).
     *
     *  @param  b   A sequence of bytes i.e. a Bytes object.
     *  @returns    A sequence of 32-byte chunks, right padded with zero bytes if b % 32 != 0 
     *
     *  @note       The py-ssz implementation can result in a 0 chunk output (empty seq)
     *              and therefore 
     *              doesn't satisfy the toChunksProp1 and toChunksProp2 lemmas. It also causes
     *              an error in the Pack function, which should reutrn at least one chunk.
     */
    // function toChunks(b: Bytes): seq<chunk>
    //     //ensures |toChunks(b)| > 0
    // {
    //     var full_chunks := |b| / BYTES_PER_CHUNK;
    //     if |b| == 0 then []
    //     else if |b| % BYTES_PER_CHUNK == 0 then [b[..32]] + toChunks(b[32..])
    //         else toChunks(b[..(full_chunks*BYTES_PER_CHUNK)]) + [rightPadZeros(b[(full_chunks*BYTES_PER_CHUNK)..])]
    // }   
    
    lemma {:induction b} toChunksProp1(b: Bytes)
        requires |b| == 0
        ensures |toChunks(b)| == 1
    {
    }

    lemma  {:induction b} toChunksProp2(b: Bytes)
        requires |b| > 0
        ensures 0 <= |toChunks(b)| == ceil(|b|, 32) 
    {
    }

    /** Pack.
     *
     *  @param  s   A sequence of serialised objects (seq<Byte>).
     *  @returns    A sequence of 32-byte chunks, the final chunk is right padded with zero 
     *              bytes if necessary. It is implied that at least one chunk is returned???
     *
     *  @note       The pack function isn't type based.
     *  @note       The spec ... 
     *  @note       The py-ssz implementation checks for |seq<Bytes>| == 0 for which it returns
     *              the EMPTY_CHUNK.
     *  @note       The py-ssz implementation doesn't allow for a single serialised object of 0 
     *              bytes. Q: Is this possible? i.e. look to default values. Q: Should EMPTY_CHUNK
     *              be returned in this case?            
     */
     
     function pack(s: seq<Bytes>) : seq<chunk>
        // no upper bound on length of any individual serialised element???
        ensures |pack(s)| >= 1 
        ensures forall i :: 0 <= i < |pack(s)| ==> is32BytesChunk(pack(s)[i])
    {
        if |s| == 0 then [EMPTY_CHUNK]
        // else toChunks(concatSerialisedElements(s))  
        else toChunks(flatten(s))  
    }


    /** merkleiseBool
     *
     *  @param  b   A sequence of bytes representing the packed from of a serialised Bool.
     *  @returns    The root of the merkle tree.
     *
     */
    function merkleiseBool(c: seq<chunk>): chunk
        requires |c| == 1 && |c[0]| == 32
        ensures is32BytesChunk(merkleiseBool(c))
    {
        c[0]
    }
    
    /** merkleiseUint8 
     *
     *  @param  b   A sequence of bytes representing the packed from of a serialised Uint8.
     *  @returns    The root of the merkle tree.
     *
     */
    function method merkleiseUint8(c: seq<chunk>): chunk
        requires |c| == 1 && is32BytesChunk(c[0])
        ensures is32BytesChunk(merkleiseUint8(c))
    {
        c[0]
    }

    
    /** getHashTreeRoot.
     *
     *  @param  s   A serialisable object.
     *  @returns    A 32-byte chunk representing the root node of the merkle tree.
     */
    function getHashTreeRoot(s : Serialisable) : chunk
        ensures is32BytesChunk(getHashTreeRoot(s))
    {
        match s 
            case Bool(_, _) => merkleiseBool(pack([serialise(s)]))

            case Uint8(_, _) => merkleiseUint8(pack([serialise(s)]))
    }


 }