/*
 * Copyright 2021 ConsenSys Software Inc.
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
include "../ssz/Constants.dfy"
include "../ssz/Serialise.dfy"
include "../ssz/IntSeDes.dfy"
include "../ssz/BoolSeDes.dfy"
include "../ssz/BitListSeDes.dfy"
include "../ssz/BytesAndBits.dfy"
include "../beacon/helpers/Crypto.dfy"

/**
 *  SSZ_Merkleise library.
 *
 *  Primary reference: [1] https://github.com/ethereum/eth2.0-specs/ssz/simple-serialize.md
 *  Secondary reference: [2] https://github.com/ethereum/py-ssz
 *
 *  This library defines various helper functions for merkleisation, including 
 *  chunk_count, bitfield_bytes, pack, merkleise*, mix_in_length, mix_in_type.
 *
 *  Other helper functions (size_of and next_pow_of_two) are included in other
 *  libraries.
 *
 *  The get_hash_tree_root function is also included in this library.
 */
 module SSZ_Merkleise {

    import opened NativeTypes
    import opened Eth2Types
    import opened Constants
    import opened IntSeDes
    import opened BoolSeDes
    import opened BitListSeDes
    import opened BytesAndBits
    import opened SSZ
    import opened Helpers
    import opened MathHelpers
    import opened Crypto

    /** chunkCount.
     *
     *  @param  s   A serialisable object.
     *  @returns    Calculate the amount of leafs for merkleisation of the type.
     *
     *  @note       A leaf is 256 bits/32-bytes.
     *  @note       The maximum tree depth for a depost contract is 32 
     *              (https://github.com/ethereum/eth2.0-specs/specs/phase0/deposit-contract.md)
     *              however NO general maximum tree depth is specified. Hence there is no
     *              upper bound on the number of chunks.
     *  @note       For the type of Bitlist[N] chunkCount == 0 only if N=0. 
     *              ([2] raises an error for bitlists if N < 0, however for lists N > 0)
     *              Hence, for all other types chunkCount will be at least 1. 
     *              
     */
    function method chunkCount(s: Serialisable): nat
        requires typeOf(s) != Container_
        ensures 0 <= chunkCount(s) // no upper limit is defined in the spec
    {
        match s
            case Bool(b) => 1
            case Uint8(_) => 1
            case Uint16(_) => 1
            case Uint32(_) => 1
            case Uint64(_) => 1
            case Uint128(_) => 1
            case Uint256(_) => 1
            case Bitlist(_,limit) => chunkCountBitlist(limit) 
            case Bitvector(xl) => chunkCountBitvector(xl) 
            case Bytes(bs) => chunkCountBytes(bs)
            case List(l,t,limit) => if isBasicTipe(t) then 
                                        chunkCountSequenceOfBasic(t,limit)
                                    else
                                        limit

            case Vector(v) =>   if isBasicTipe(typeOf(v[0])) then 
                                    chunkCountSequenceOfBasic(typeOf(v[0]),|v|)
                                else
                                    |v|

    } 

    /** 
     * chunkCount helper functions for specific types
     */
    function method chunkCountBitlist(limit: nat): nat
        // (N + 255) // 256 (dividing by chunk size in bits, rounding up) [1]
        // In this case N == limit
        ensures chunkCountBitlist(limit) == ceil(limit, BITS_PER_CHUNK)
    {
        (limit+BITS_PER_CHUNK-1)/BITS_PER_CHUNK
    }

    function method chunkCountBitvector(xl: seq<bool>): nat
        // (N * size_of(B) + 31) // 32 (dividing by chunk size in bytes, rounding up) [1]]
        // In this case N == |xl|
        ensures chunkCountBitvector(xl) == ceil(|xl|, BITS_PER_CHUNK)
    {
        (|xl|+BITS_PER_CHUNK-1)/BITS_PER_CHUNK
    }    

    function method chunkCountBytes(bs: seq<byte>): nat
        // (N * size_of(B) + 31) // 32 (dividing by chunk size in bytes, rounding up) [1]]
        // In this case N == |bs|
        ensures chunkCountBytes(bs) == ceil(|bs|, BYTES_PER_CHUNK)
    {
        var s := default(Uint8_);
        (|bs| * sizeOf(s) + 31) / BYTES_PER_CHUNK
    }

    function method chunkCountSequenceOfBasic(t:Tipe, limit:nat): nat
        // (N * size_of(B) + 31) // 32 (dividing by chunk size in bytes, rounding up) [1]]
        // In this case N == limit
        requires isBasicTipe(t)
        ensures  chunkCountSequenceOfBasic(t, limit) == ceil(limit * sizeOf(default(t)), BYTES_PER_CHUNK)
    {
        var s := default(t);
        (limit * sizeOf(s) + 31) / BYTES_PER_CHUNK
    }    
     
    /** 
     *  Predicate used to check if a byte sequence is a chunk.
     */
    predicate is32BytesChunk(c : chunk) 
        // Test whether a chunk has 32 (BYTES_PER_CHUNK) chunks
    {
        |c| == BYTES_PER_CHUNK
    }

     /** 
     *  Properties of EMPTY_CHUNK.
     */
     lemma emptyChunkIsSeq()
        // Ensure that the defined EMPTY_CHUNK constant is treated by Dafny as a seq.
        ensures EMPTY_CHUNK == timeSeq<byte>(0,32)
    {
        // Thanks Dafny
    }

    lemma emptyChunkIs32BytesOfZeros()
        ensures is32BytesChunk(EMPTY_CHUNK) 
        ensures forall i :: 0 <= i < |EMPTY_CHUNK| ==> EMPTY_CHUNK[i]== 0 //as byte 
    {   //  Thanks Dafny
    }

    /** Pack.
     *
     *  @param  s   A serialised object.
     *  @returns    A sequence of 32-byte chunks, the final chunk is right padded with zero 
     *              bytes if necessary. It is implied by the spec that at least one chunk is 
     *              returned (see note below).
     *
     *  @note       The spec [1] describes the pack function as:
     *              ``pack(value): given ordered objects of the same basic type, serialize them,
     *              pack them into BYTES_PER_CHUNK-byte chunks, right-pad the last chunk with 
     *              zero bytes, and return the chunks.``
     *  @note       However, later in the spec [1] the usage context is ``merkleize(pack(value)) 
     *              if value is a basic object or a vector of basic objects`` implying that the
     *              input to pack, i.e. value, is a single serialisable object rather than a 'series' 
     *              but with the restriction value is a bool, uintN, or vector/list of uintNs.
     *  @note       The py-ssz implementation [2] of the pack function takes an input of already 
     *              serialised values and hence its input is a sequence of serialised values, rather 
     *              than a single serialisable object of type bool, uintN, or vector/list of uintNs.         
     *  @note       This subtle difference between the spec wording [1] and py-ssz [2] shouldn't
     *              result in any difference to the final output. 
     *  @note       So as to align this project with the spec [1] as closely as possible, pack will
     *              take a single serialisable object of type bool, uintN, or vector/list of uintNs
     *              as its input and thus it does indeed take `ordered objects`: if a bool or uintN 
     *              then it is thought of as inputing a sequence of length 1, and if a vector/list  
     *              of uintN then it is thought of as inputing a sequence of possible larger length. 
     *              An empty list, [], is a possible input.          
     */
    function method pack(s: Serialisable): seq<chunk>
        requires !(s.Container? || s.Bitlist?  || s.Bitvector?)
        requires s.List? ==> match s case List(_,t,_) => isBasicTipe(t)
        requires s.Vector? ==> match s case Vector(v) => isBasicTipe(typeOf(v[0]))
         // at least one chunk is always produced, even if the EMPTY_CHUNK for input of an empty list 
        ensures 0 <= |pack(s)|
    {
        match s
            case Bool(b) => toChunks(serialise(Bool(b)))
            case Uint8(_) =>  toChunks(serialise(s))
            case Uint16(_) => toChunks(serialise(s))
            case Uint32(_) => toChunks(serialise(s))
            case Uint64(_) => toChunks(serialise(s))
            case Uint128(_) => toChunks(serialise(s))
            case Uint256(_) => toChunks(serialise(s))
            case Bytes(bs) =>   toChunksProp2(bs);
                                toChunks(serialise(s))
            case List(l,_,limit) => if |l| == 0 then
                                        []
                                    else
                                        toChunks(serialiseSeqOfBasics(l))

            case Vector(v) => toChunks(serialiseSeqOfBasics(v)) 
    } 

    /** 
    *   Properties of pack 
    */
    lemma basicTypesPackToChunkCountChunks(s:Serialisable)
        // basic types, uintN and bool, pack into chunkCount(s) chunks
        requires isBasicTipe(typeOf(s))
        ensures |pack(s)| == chunkCount(s)
    {
        // Thanks Dafny
    }

    lemma byteVectorsPackToChunkCountChunks(s:Serialisable)
        // vectors of uintNs, i.e. fixed length collections, pack into chunkCount(s) chunks
        requires s.Bytes? 
        ensures |pack(s)| == chunkCount(s)
    {
        calc == {
            |pack(s)|;
            ==
            |toChunks(serialise(s))|;
            ==
            |toChunks(s.bs)|;
            ==
                {toChunksProp2(s.bs);} 
            ceil(|s.bs|, BYTES_PER_CHUNK);
            ==
            chunkCount(s);
        }
    }

    lemma basicTypeVectorsPackToChunkCountChunks(s:Serialisable)
        // vectors of uintNs, i.e. fixed length collections, pack into chunkCount(s) chunks
        requires s.Vector? &&  match s case Vector(v) => isBasicTipe(typeOf(v[0]))
        ensures |pack(s)| == chunkCount(s)
    {
        if |s.v| > 0 {
            calc == {
                |pack(s)|;
                ==
                |toChunks(serialise(s))|;
                ==
                |toChunks(serialiseSeqOfBasics(s.v))|;
                ==
                    {toChunksProp2(serialiseSeqOfBasics(s.v));} 
                ceil(|serialiseSeqOfBasics(s.v)|, BYTES_PER_CHUNK);
                ==
                chunkCount(s); // ceil(limit * sizeOf(default(t)), BYTES_PER_CHUNK)
            }
        }
    }

    lemma basicTypeListsPackToChunkCountChunks(s:Serialisable)
        // lists of uintNs, i.e. variable length collections, pack into <= chunkCount(s) chunks
        requires s.List? &&  match s case List(_,t,_) => isBasicTipe(t)
        ensures |pack(s)| <= chunkCount(s)
    {
        if (|s.l| == 0)
        {
            // Thanks Dafny
        }
        else {
            calc == {
                |pack(s)|;
                ==
                |toChunks(serialise(s))|;
                ==
                |toChunks(serialiseSeqOfBasics(s.l))|;
                ==
                    {toChunksProp2(serialiseSeqOfBasics(s.l));} 
                ceil(|serialiseSeqOfBasics(s.l)|, BYTES_PER_CHUNK);
                ==
                ceil(|s.l| * |serialise(s.l[0])|, BYTES_PER_CHUNK);
                ==
                ceil(|s.l| * sizeOf(s.l[0]), BYTES_PER_CHUNK);
                == calc {
                        isBasicTipe(typeOf(s.l[0]));
                        sizeOf(s.l[0]) == sizeOf(default(s.t));
                    }
                ceil(|s.l| * sizeOf(default(s.t)), BYTES_PER_CHUNK);
                <=
                chunkCount(s); // ceil(limit * sizeOf(default(t)), BYTES_PER_CHUNK)
            }
        }
    }

    /** Pack helper functions. */

    /** rightPadZeros.
     *
     *  @param  b   A sequence of bytes.
     *  @returns    The sequence of bytes right padded with zero bytes to form a 32-byte chunk.
     *
     */
    function method rightPadZeros(b: bytes): chunk
        requires |b| < BYTES_PER_CHUNK
        ensures is32BytesChunk(rightPadZeros(b)) 
    {
        b + EMPTY_CHUNK[|b|..]
    }

    /** toChunks.
     *
     *  @param  b   A sequence of bytes.
     *  @returns    A sequence of 32-byte chunks, right padded with zero bytes if b % 32 != 0 
     *
     *  @note       This version of toChunks is suggested as an alternative to the in py-ssz,
     *              as this version ensures that even if |b| == 0 an EMPTY CHUNK will still 
     *              be returned. 
     *  @note       It also satisfies the toChunksProp1 and toChunksProp2 lemmas.
     *
     */
    function method toChunks(b: bytes): seq<chunk>
        ensures |toChunks(b)| > 0
        ensures forall i :: 0 <= i < |toChunks(b)| ==> is32BytesChunk(toChunks(b)[i]) 
        decreases b
    {
        if |b| < BYTES_PER_CHUNK then [rightPadZeros(b)]
        else    if |b| == BYTES_PER_CHUNK then [b] 
                else [b[..BYTES_PER_CHUNK]] + toChunks(b[BYTES_PER_CHUNK..])
    }    


    /** toChunks (py-ssz version).
     *
     *  @param  b   A sequence of bytes.
     *  @returns    A sequence of 32-byte chunks, right padded with zero bytes if b % 32 != 0 
     *
     *  @note       The py-ssz implementation can result in a 0 chunk output (empty seq)
     *              and therefore 
     *              doesn't satisfy the toChunksProp1 and toChunksProp2 lemmas. It also causes
     *              an error in the Pack function, which should reutrn at least one chunk.
     */
    // function method toChunks(b: bytes): seq<chunk>
    //     ensures |toChunks2(b)| >= 0
    // {
    //     var full_chunks := |b| / BYTES_PER_CHUNK;
    //     if |b| == 0 then []
    //     else if |b| % BYTES_PER_CHUNK == 0 then [b[..32]] + toChunks2(b[32..])
    //         else toChunks2(b[..(full_chunks*BYTES_PER_CHUNK)]) + [rightPadZeros(b[(full_chunks*BYTES_PER_CHUNK)..])]
    // }   
    
    /** 
     *  Properties of toChunks.
     */
    lemma {:induction b} toChunksProp1(b: bytes)
        requires |b| == 0
        ensures |toChunks(b)| == 1
    {
        // Thanks Dafny
    }

    lemma  {:induction b} toChunksProp2(b: bytes)
        requires |b| > 0
        ensures 1 <= |toChunks(b)| == ceil(|b|, 32) 
    {
        // Thanks Dafny
    }


    /** pack_bits.
     *
     *  @param  b   A sequence of bits (seq<bool>)
     *  @returns    A sequence of 32-byte chunks, right padded with zero bytes if |b| % 32 != 0
     *
     *  @note       This function is only applicable to a bitlist or bitvector. 
     *
     *  @note       Return the bits of the bitlist or bitvector, packed in bytes, aligned to the start. 
     *              Length-delimiting bit for bitlists is excluded [1].
     *  @note       Not that the spec [1] was updated and the original function of bitfield_bytes was
     *              changed to pack_bits as the specification of bitfield_bytes didn't return chunks.
     *
     *  @note       The spec [1] implies that at least one chunk will be returned, however py-ssz [2] 
     *              has an implementation of to_chunks that will allow [] as output for an empty bitlist.
     *              For the moment the packBits function will mirror the py-ssz [2] strategy.
     */
    function method packBits(b: seq<bool>) : seq<chunk>
        ensures 0 <= |packBits(b)|    
     {        
        if |b| == 0 then []
        else toChunks(fromBitsToBytes(b)) 
    }

    /** 
    *   Property of packBits 
    */
    lemma packBitsToChunkCountProp(xl: seq<bool>, limit: nat)
        requires |xl| <= limit
        ensures |packBits(xl)| <= chunkCountBitlist(limit)
    {
        if (|xl| == 0) {
            calc == {
                // thanks Dafny
            }
        } else {
            calc == {
                |packBits(xl)|;
                ==
                |toChunks(fromBitsToBytes(xl)) |;
                ==
                {toChunksProp2(fromBitsToBytes(xl));} ceil(|fromBitsToBytes(xl)|, BYTES_PER_CHUNK);
                ==
                ceil(|xl|, BITS_PER_BYTE * BYTES_PER_CHUNK);
                ==
                ceil(|xl|, BITS_PER_CHUNK);
                <=
                ceil(limit, BITS_PER_CHUNK);
                ==
                chunkCountBitlist(limit);
            }
        }
    }

    // // TODO: complete once bitvectors are available
    // lemma bitvectorPackBitsToChunkCountProp(s:Serialisable)
    //     requires s.BitVector?
    //     ensures |packBits(s.v)| == chunkCount(s)
    // {
        
    // }

    /** merkleise.
     *
     *  @param chunks   A sequence of chunks (seq<chunk>) representing leaves of a merkle tree.
     *  @param limit    limit == -1 is equivalent to the spec limit=None [1],
     *                  otherwise limit is the maximum number of leaves required.
     *  @returns        The root of the merkle tree, a 32-byte hash.
     *
     *  @note       The spec [1] says ``merkleize(chunks, limit=None): Given ordered BYTES_PER_CHUNK-byte 
     *              chunks, merkleize the chunks, and return the root: The merkleization depends on the 
     *              effective input, which can be padded/limited:
     *                  if no limit: pad the chunks with zeroed chunks to next_pow_of_two(len(chunks)) 
                        (virtually for memory efficiency).
                        if limit > len(chunks), pad the chunks with zeroed chunks to next_pow_of_two(limit) 
                        (virtually for memory efficiency).
                        if limit < len(chunks): do not merkleize, input exceeds limit. Raise an error instead.
                    Then, merkleize the chunks (empty input is padded to 1 zero chunk):
                        If 1 chunk: the root is the chunk itself.
                        If > 1 chunks: merkleize as binary tree..``
     *  @note       The case where limit == len(chunks) is not included in the spec [1]. Our current version
     *              assumes that this case can occur and is the same as limit > len(chunks). 
     *  @note       TODO: raise an issue in [1].
     *  @note       TODO: depending on confirmation of whether a bitlist with N==0 is illegal, review the
     *              specification [1] wording of this function and the py-ssz [2] implenetation of pack, 
     *              pack_bits, pack_bytes and to_chunks and resolve the issue that in py-ssz at least 1 chunk
     *              isn't returned from pack_bits.
     *  @note       TODO: Also then review whether the need to pad an empty chunk to 1 zero chunk is redundant.
     */
     function method merkleise(chunks: seq<chunk>, limit: int): hash32
        requires -1 == limit || |chunks| <= limit
        ensures is32BytesChunk(merkleise(chunks, limit))
    {
        if limit == -1 then 
            nextPow2IsPow2(|chunks|);
            getNextPow2LowerBound(|chunks|);
            merkleiseChunks(padChunks(chunks, get_next_power_of_two(|chunks|)))
        else 
            assert(limit >= 0);
            nextPow2IsPow2(limit);
            getNextPow2LowerBound(limit);
            merkleiseChunks(padChunks(chunks, get_next_power_of_two(limit)))
    }

    /** Helper functions for merkleise. */
    
    // TODO: add documentation
    function method padChunks(chunks: seq<chunk>, padLength: nat): seq<chunk>
        requires 1 <= padLength  // since padLength must be a power of two
        requires 0 <= |chunks| 
        requires |chunks| <= padLength // upper bound as per spec // TODO: change upper to <
        requires isPowerOf2(padLength)
        ensures 1 <= |padChunks(chunks, padLength)| == padLength
        ensures isPowerOf2(|padChunks(chunks, padLength)|)
    {
        if |chunks| == padLength then chunks
        else chunks + timeSeq(EMPTY_CHUNK, padLength-|chunks|)
    }

    // TODO: add documentation
    function method merkleiseChunks(chunks: seq<chunk>): hash32
        requires 1 <= |chunks| 
        requires isPowerOf2(|chunks|)
        ensures is32BytesChunk(merkleiseChunks(chunks))
        decreases chunks
    {
        if |chunks| == 1 then chunks[0]
        else 
            assert(|chunks|>1);
            halfPow2IsPow2(|chunks|);
            hash(merkleiseChunks(chunks[..(|chunks|/2)]) + merkleiseChunks(chunks[|chunks|/2..]))
    }

    
    /** getHashTreeRoot.
     *
     *  @param  s   A serialisable object.
     *  @returns    A 32-byte chunk representing the root node of the merkle tree.
     */
    function method getHashTreeRoot(s : Serialisable) : hash32
        ensures is32BytesChunk(getHashTreeRoot(s))
    {
        match s 
            case Bool(_) => merkleise(pack(s), -1)

            case Uint8(_) => merkleise(pack(s), -1)

            case Uint16(_) => merkleise(pack(s), -1)

            case Uint32(_) => merkleise(pack(s), -1)

            case Uint64(_) => merkleise(pack(s), -1)

            case Uint128(_) => merkleise(pack(s), -1)

            case Uint256(_) => merkleise(pack(s), -1)

            case Bitlist(xl,limit) =>   //bitlistLimit(s,limit);
                                packBitsToChunkCountProp(xl, limit);
                                mixInLength(merkleise(packBits(xl), chunkCount(s)), |xl|)  

            case Bitvector(xl) =>   packBitsToChunkCountProp(xl, |xl|);
                                    merkleise(packBits(xl), chunkCount(s))                                

            case Bytes(_) => merkleise(pack(s), -1)

            case Container(fl) => merkleise(prepareSeqOfSerialisableForMerkleisation(fl),-1)
            // Note: if `seqMap(fl,(f:Serialisable) => getHashTreeRoot(f))` is
            // used in place of `prepareSeqOfSerialisableForMerkleisation(fl)`,
            // like below, then Dafny is unable to prove termination:
            //merkleise(seqMap(fl,(f:Serialisable) => getHashTreeRoot(f)),-1)

            case List(l,t,limit) =>     if isBasicTipe(t) then
                                            //lengthOfSerialisationOfSequenceOfBasics(s);
                                            basicTypeListsPackToChunkCountChunks(s);
                                            mixInLength(
                                                merkleise(pack(s),chunkCount(s)),
                                                |l|)
                                        else
                                            mixInLength(
                                                merkleise(prepareSeqOfSerialisableForMerkleisation(l),chunkCount(s)),
                                                |l|
                                            )

            case Vector(v) =>   if isBasicTipe(typeOf(v[0])) then
                                    merkleise(pack(s), -1)
                                else
                                   merkleise(prepareSeqOfSerialisableForMerkleisation(v),-1)
    }

    /** Helper functions for getHashTreeRoot. */

    /**
     * Prepare a sequence of `Serialisable` objects for merkleisation.
     *
     * @param ss Sequence of `Serialisable` objects
     *
     * @return Sequence of `chunk` to be given in input to the `merkleise`
     *         function to merkleise a container `c` where `ss == c.fl`
     */
    function method prepareSeqOfSerialisableForMerkleisation(ss:seq<Serialisable>): seq<chunk>
    ensures |prepareSeqOfSerialisableForMerkleisation(ss)| == |ss|
    ensures forall i | 0 <= i < |ss| :: prepareSeqOfSerialisableForMerkleisation(ss)[i] == getHashTreeRoot(ss[i])
    {
        if(|ss| == 0) then
            []
        else
            [getHashTreeRoot(ss[0])] +
            prepareSeqOfSerialisableForMerkleisation(ss[1..])
    }   

    // TODO: add documentation
    function method uint256_to_bytes(n: nat) : chunk
        ensures |uint256_to_bytes(n)| == 32
    {
        uint256_to_bytes_helper(n,0)
    }

    // TODO: add documentation
    function method uint256_to_bytes_helper(n: nat, byte_number: nat) : bytes
        requires byte_number <= 32
        decreases 32  - byte_number
        ensures |uint256_to_bytes_helper(n,byte_number)| == 32 - byte_number as int
    {
        if(byte_number == 32) then
            []
        else
            [(n % 256) as uint8] +
            uint256_to_bytes_helper(n / 256, byte_number+1)
    }

    // TODO: add documentation
    function method mixInLength(root: hash32, length: nat) : hash32
        requires is32BytesChunk(root)
        ensures is32BytesChunk(mixInLength(root, length))
    {
        hash(root + uint256_to_bytes(length))
    }  
 }