# Merkleise Library

This section contains notes about the Eth2.0 specifications of Merkleisation and links to the corresponding formal definitions and correctness proofs in **Dafny**.

The Eth2.0 specifications of Merkleisation are spread across two files:

1.  **simple-serialize.md**
2.  **merkle-proofs.md**

The simple-serialize.md file contains a section called _Merkleization_ which includes specification of the `merkleization` function and `hash_tree_root` function, as well as several helper functions.

The merkle-proofs.md file is a work-in-progress document which specifies merkle proof formats, including merkle mulitproofs and several helper functions.

This wiki will focus on the Merkleisation functionality specified within **simple-serialize.md**.

**Disclaimer**: It is not the official SSZ specs.

## Overview

The Merkleise library aims at providing the following functionality:

1.  _hash\_tree\_root_, merkleisation of an SSZ object to yield the root.

Given an object `value`, its hash tree root, `hash_tree_root(value)`, is a `BYTES_PER_CHUNK` byte sequence. 

`BYTES_PER_CHUNK`, 32, is a defined constant to represent the number of bytes per chunk. Hence it is equivalent to refer to the output of `hash_tree_root(O)` as being a single _chunk_.

## Background

**TODO**: Add notes, including: <!-- _merkleize_, return the root of a binary merkle tree representing a serialised data structure, and -->
 1. define a binary merkle tree
 2. note about hashing of leaves
 3. the hash function used in Eth2.0

## Expected Properties of Merkleisation

**TODO**: Add notes, including:
 1. find reference to different hash root for different values of the same type 
 2. other properties relating to helper functions (i.e. look to lemmas)
 3. list any open questions about other properties

### Summaries and Expansions

```
Let A be an object derived from another object B by replacing some of the (possibly nested) values of B by their hash_tree_root. We say A is a "summary" of B, and that B is an "expansion" of A. Notice hash_tree_root(A) == hash_tree_root(B).
```

**TODO**: Add notes

## Merkleisation in Eth2

In the Eth2.0 specifications, the Merkleise provides `hash_tree_root` for

- **Basic types** i.e. unsigned integers of N bytes, known as uintNs, as well as Booleans,
- **List** and **vectors of bits**, known as BitLists and BitVectors,
- **Lists** and **vectors** of `Serialisable` i.e. either basic or composite types, **TODO**: add link to compositie types
- **Containers** with `Serialisable` fields,
- and **Unions** that we omit in this project.

To implement `hash_tree_root` a number of helper functions are required, including

- `size_of`
- `chunk_count`
- `pack`
- `pack_bits`
- `next_pow_of_two`
- `merkleize`
- `mix_in_length`
- `mix_in_type`

Further detail regarding these helper functions will be presented as we introduce formal specifications for this library.

## Formal Specifications, Implementations and Correctness Proofs

We write the specifications and implementations of the Merkleise functions using logical pre-conditions to define the domain of each function. Moroever, in the correctness proofs, we use provable logical post-conditions to establish the correctness properties.

In the Eth2.0 specification the helper functions are presented before a recursive formulation of the `hash_tree_root` function. Here, however, we will work in a reverse order; initially describing the `hash_tree_root` function at a high level and then adding the requisite detail that comes from understanding the role of the helper functions.

### _hash\_tree\_root_

The `hash_tree_root` function for Eth2.0 is based on the construction of a binary merkle tree in which the serialised form of the value becomes the leaves of the tree. 

However, the derivation of the final 32 bytes root hash does also depend on the _type_ of a value and for some cases additional information relating to the type or length of a value is incorporated.

The Eth2.0 specification says

>We now define Merkleization `hash_tree_root(value)` of an object `value` recursively:
>- `merkleize(pack(value))` if `value` is a basic object or a vector of basic objects.
>- `merkleize(pack_bits(value), limit=chunk_count(type))` if `value` is a bitvector.
>- `mix_in_length(merkleize(pack(value), limit=chunk_count(type)), len(value))` if `value` is a list of basic objects.
>- `mix_in_length(merkleize(pack_bits(value), limit=chunk_count(type)), len(value))` if `value` is a bitlist.
>- `merkleize([hash_tree_root(element) for element in value])` if `value` is a vector of composite objects or a container.
>- `mix_in_length(merkleize([hash_tree_root(element) for element in value], limit=chunk_count(type)), len(value))` if `value` is a list of composite objects.
>- `mix_in_type(merkleize(value.value), value.type_index)` if `value` is of union type.

It is important to note that whether a `value` is of a **fixed** or **variable length** type will impact upon the specification of its `hash_tree_root`.

<!-- As such for reference, note that -->

**TODO**: maybe add a table to summarise fixed vs variable

Also, although the `merkleize(chunks, limit=None)` helper function will be discussed in further detail below, it is important to note that this function takes as input a series of 32-byte _chunks_ that represent the value being processed and hence become the leaves of the binary merkle tree formed by merkleisation.

In this section any helper functions mentioned will be described at a high level and then further detail relating to their formal specification will be presented in the following section.

#### Basic object or vector of basic objects (fixed length types)

Let's start by looking at more detail at the procedure for basic objects (i.e. **basic type** values) or vectors of basic objects. Here `hash_tree_root(value)` = `merkleize(pack(value))`.

In this case the process is relatively simple as the value being merkleised will be either a uintN, boolean, vector of uintNs, or vector of booleans, and hence will be of a fixed length. Note that a vector of booleans is distinct from a bit vector. 

**TODO**: add reference to the relevant issue (or add notes)

The `pack` function takes the value, serialises it into bytes and right pads with zeros to create a multiple of `BYTES_PER_CHUNK`-byte chunks. These chunks are then merkleised as a binary tree and the root is returned.

The `hash_tree_root` is therefore just the root of the binary merkle tree in which the leaves are created from the serialised form of the value (with zero padding as necessary).

#### Bitvector (fixed length type)

In this case `hash_tree_root(value)` = `merkleize(pack_bits(value), limit=chunk_count(type))`.

The first noticable difference is that the value is processed by `pack_bits` rather than `pack`. `pack_bits` is a specialised form of `pack` in which the bits of the bitvector are packed into bytes directly, rather than say trying to serialise each bit individually. 

This difference is important as generally when working with a series of bits (fixed length) a bitvector would be the preferred structure due to the storage efficiencies gained from being able to pack 32 bits into each chunk. This can be contrast to using a vector of booleans which would require one byte for each bit, and thus a series of 32 bites would require _32 * 8 = 256 bytes = 8 chunks_.

The other noticable difference is the inclusion of the `limit` parameter, here set to `chunk_count(type)`. While further details regarding the helper function `chunk_count` will be provided below, it is useful to note here that this parameter is generally used for variable length types to ensure that a buffer is included so as to allow for the maximum length of the type. As such in this instance for bitvectors, as a fixed length type, it is redundant.  `merkleize(pack_bits(value))` produces an equivalent result. Again further explanation of the use of the `limit` parameter for the `merkleize` function will be provided below.

#### List of basic objects (variable length type)

In this case `hash_tree_root(value)` = `mix_in_length(merkleize(pack(value), limit=chunk_count(type)), len(value))`.

The value being merkleised will be either a list of uintNs, or list of booleans. Note that a list of booleans is distinct from a bitlist. (**TODO** add reference to issue or add notes????)

If we focus initially on the `merkleize(pack(value), limit=chunk_count(type))` part we can see that the value gets packed into chunks and we also have the `limit` parameter. 

Lists are a variable length type and so in this case the `limit` represents an upper bound on the length; the number of chunks that would be required to represent a value of maximum length. In particular, the inclusion of this upper bound means that the packed value will be padded with zero chunks up to the `limit` during merkleisation, to ensure that the number of leaves being included is that for a maximum length value of that type.

To generate the `hash_tree_root(value)` the root that results from the merkleisation function is then hashed with the actual length of the value within the `mix_in_length` function to yield the final hash tree root.

**TODO**: include a diagram similar to merkle-proofs.md

**TODO**: mention lists of zero length??? maybe in the helper function section??

#### Bitlist (variable length type)

In this case `hash_tree_root(value)` = `mix_in_length(merkleize(pack_bits(value), limit=chunk_count(type)), len(value))`.

Bitlist is similar to the list case in that to generate the `hash_tree_root(value)` the root that results from the merkleisation function is then hashed with the actual length of the value within the `mix_in_length` function to yield the final hash tree root. i.e. mix_in_length(merkleisation root, length).

The primary difference to the list case is therefore in this case we are dealing with _bits_ and hence the chunks required as the first input parameter to the `merkleise` function are generated using the `pack_bits` function rather than the `pack` function. As mentioned previously in the context of bitvectors, `pack_bits` is a specialised form of `pack` in which the bits of the bitlist are packed into bytes directly, rather than say trying to serialise each bit individually. 

This difference is important as generally when working with a series of bits (variable length) a bitlist would be the preferred structure due to the storage efficiencies gained from being able to pack 32 bits into each chunk. This can be contrast to using a list of booleans which would require one byte for each bit, and thus a series of 32 bites would require _32 * 8 = 256 bytes = 8 chunks_.

The inclusion of the `limit` parameter, here set to `chunk_count(type)` is also similar to the case of lists. While further details regarding the helper function `chunk_count` will be provided below, it is useful to note here that this parameter is generally used for variable length types to ensure that a buffer is included so as to allow for the maximum length of the type. 

#### Vector of composite objects or a container

In this case `hash_tree_root(value)` = `merkleize([hash_tree_root(element) for element in value])`.

Firslty, consider the application to vectors of composite objects and thus each _element_ in `value` will be of the same type. 

To generate the _chunks_ required as input to the `merkleize` function, each _element_ itself becomes input to the `hash_tree_root` function yielding a recursive process. For example if we have a vector of uint64 lists then we have a fixed number of the uint64 lists and each of these uint64 lists would be processed by the `hash_tree_root(value)` = `mix_in_length(merkleize(pack(value), limit=chunk_count(type)), len(value))` function. The processing of each element, i.e. each list, would yield a 32-byte hash tree root and this series of 32-byte hash tree roots then become the chunks for input to the `merkleize` function.

As a vector is a fixed length type the limit parameter for the `merkleize` function is not required, as well there is no use of the _mix_in_length_ functionality.

If we now look at the application to a container; a container will have _fields_ and so each field becomes an _element_ to be processed by `hash_tree_root`; thus generating a series of 32-byte hash tree roots that become the chunks for input to the `merkleize` function.

Again, as a container is a fixed length type the limit parameter for the `merkleize` function is not required, as well there is no use of the _mix_in_length_ functionality.

#### List of composite objects 

In this case `hash_tree_root(value)` = `mix_in_length(merkleize([hash_tree_root(element) for element in value], limit=chunk_count(type)), len(value))`.

Similar to the processing of a vector of composite objects (and containers), a 32-byte hash tree root is generated for each element of the list thus forming the chunks to be input to the `merkleize` function; however, unlike the case for a vector of composite objects, the `merkleize` function does in this case require the `limit` parameter to ensure that the number of leaves being included is that for a maximum length value of that type. The actual length, as given by `len(value)` is then incorporated using the `mix_in_length` function to yield the final hash tree root for the list of composite objects.

#### Union

Unions will not be considered within this project.


### Helper functions

In this section we will now consider the helper functions mention above in more detail, including pre and post conditions that clarify their functionality.

1.  `size_of`

Defined in the Eth2.0 spec as:

>`size_of(B)`, where `B` is a basic type: the length, in bytes, of the serialized form of the basic type.

As this function is only applicable to a basic type, the input must be a uintN or boolean. This represents a **pre-condition** of the function.

The output must be the length, in bytes, of the serialized form of the basic type. Thus the function must return a minimum of 1 byte (i.e. for boolean and uint8) and a maximum of 32 bytes (i.e. for a uint256). `1 <= size_of(B) <= 32` therefore represents a **post-condition** of the function.

[Dafny reference.]()
**TODO**: add link

2.  `chunk_count`

Defined in the Eth2.0 spec as:

>`chunk_count(type)`: calculate the amount of leafs for merkleization of the type.
> - all basic types: `1`
> - `Bitlist[N]` and `Bitvector[N]`: `(N + 255) // 256` (dividing by chunk size, rounding up)
> - `List[B, N]` and `Vector[B, N]`, where `B` is a basic type: `(N * size_of(B) + 31) // 32` (dividing by chunk size, rounding up)
> - `List[C, N]` and `Vector[C, N]`, where `C` is a composite type: `N`
> - containers: `len(fields)`

Intended to represent _the amount of leafs for merkleization of the type_ it is important to note that there is an exception if the wording is to be interupted strictly. The worded definition suggests the **post-condtion** `1 <= chunk_count(type)` given that a binary merkle tree must at a minimum include the root node, and hence at least one leaf.

However, since it is possible to define a bitlist or list (basic or composite) such that `N=0`, in these cases the formula provided yields an output of `chunk_count(type)=0`. As this is the intended outcome (**TODO**: include issue reference), the **post-condtion** is actually `0 <= chunk_count(type)` and hence we should view the `N=0` case for bitlists and lists to be an exception to the worded definition. Though, strictly speaking, giving rise to somewhat of an inconsistency between the worded definition and the corresponding formulas, we can resolve this inconsistency on the basis that we would not want to allocate 1 `EMPTY_CHUNK` to represent this type where it forms part of a larger structure and efficiencies can be gained by treating it as being _0 chunks_, only creating the minimum 1 leaf to form a merkle tree hash root as a final step. For example, if a list with N=0 were to be a field within a container, we can treat this field as a placeholder.

**TODO**: double check the issue reply explanation and compare to the hash tree root procedure for a container. As each field is merkleised separately, I don't think in this case it makes any difference with regard to minimising storage??

Any maximum bound on the output of `chunk_count` would require specification of a maximum tree depth for `merkelization`/`hash_tree_root`, which doesn't form part of this spec.

Further, the `chunk_count` function is related to both the `pack` and `pack_bits` functions. For basic types, or lists or vectors of basic types, the number of chunks returned by `chunk_count` should equal the number of chunks returned by the `pack` function. This includes for an empty list i.e. `list[B, N=0]`.

**TODO**: add reference or notes regarding the pack function returning 0 chunks for an empty list.
**TODO**: check which one is wrong in PySsz.

For bitvectors and bitlists, the number of chunks returned by `chunk_count` should equal the number of chunks returned by the `pack_bits` function, again this will be true even for an empty bitlist i.e. `bitlist[N=0]`.

For these types, that `len(pack(value)) = chunk_count(type)` or `len(pack_bits(value)) = chunk_count(type)` can be seen as an additional **post-condition** to the `chunk_count` function or as a **property** relating the functions.

[Dafny reference.]()
**TODO**: add link

3.  `pack`

Defined in the Eth2.0 spec as:

>`pack(values)`: Given ordered objects of the same basic type:
> i. Serialize  `values` into bytes.
> ii. If not aligned to a multiple of `BYTES_PER_CHUNK` bytes, right-pad with zeroes to the next multiple.
> iii. Partition the bytes into `BYTES_PER_CHUNK`-byte chunks.
> iv. Return the chunks.

This function is designed to create the chunks required to `merkleize` a value that is either a basic type, a vector of basic objects or a list of basic objects. The scope of type for the `value` parameter represents a function **pre-condition**.

The `values` (i.e. the plural form includes the case of a single basic type, as well as the possibility of an empty sequence in the case of a list) are firstly serialised and then if the number of resulting bytes is not a multiple of 32 then the output is right padded with zero bytes to ensure a multiple of 32 bytes. 

Note that if we are dealing with an empty list then its serialised form will be zero bytes.  Because zero is a multiple of 32 in this case no padding is required and zero chunks will be returned by the `pack` function. This outcome is consistent with the intention discussed within the explanation of the `chunk_count` function.

The final step of the `pack` function is to partition the serialised and padded bytes into 32 byte chunks. 

The output of the `pack` function is therefore a series of 32 byte chunks and we can observe the following **post-conditions**:

- `0 <= len(pack(values))`
- `len(pack(values))` == `chunk_count(type)`

[Dafny reference.]()
**TODO**: add link

4.  `pack_bits`

Defined in the Eth2.0 spec as:

>`pack_bits(bits)`: Given the bits of bitlist or bitvector, get `bitfield_bytes` by packing them in bytes and aligning to the start. The length-delimiting bit for bitlists is excluded. Then return `pack(bitfield_bytes)`.

The `pack_bits` function is analogous to the `pack` function with the output being a series of 32 byte chunks that willget used in the merkleisation process. 

In this case the input comprises the bits of a bitvector or bitlist. It can be distinguished from the `pack` function because the bits get packed into bytes with no delimiting bit; noting that when a bitlist is serialised the bits are also packed into bytes but a delimitng bit is appended. It is therefore almost the same as the `pack` function but in the case of a bitlist, the serialisation differs to exclude the use of a delimiting bit.

The bytes generated are referred to as `bitfield_bytes` and then this series of bytes (i.e. a series of uint8s) become the input of `pack` to complete the generation of the chunk output. Note that as the input to `pack` in this context is a series of uint8s, the first step of the `pack` function, which is to serialise the values, is redundant because serialisation of a series of uint8s will leave the bytes unchanged. The main purpose of returning `pack(bitfield_bytes)` is to ensure that a multiple of 32 bytes is generated, using padding if needed, and then that these bytes are partitioned into the 32 byte chunks that form the ultimate output.

The **pre-condition** of the `pack_bits` function is thus that the `bits` are the bits of a bitvector or bitlist.

The **post-conditions** of the `pack_bits` are the same as for the `pack` function:

- `0 <= len(pack(values))`
- `len(pack(values))` == `chunk_count(type)`

[Dafny reference.]()
**TODO**: add link

5.  `next_pow_of_two`

Defined in the Eth2.0 spec as:

>`next_pow_of_two(i)`: get the next power of 2 of `i`, if not already a power of 2, with 0 mapping to 1. Examples: `0->1, 1->1, 2->2, 3->4, 4->4, 6->8, 9->16`

The `next_pow_of_two` function is a helper function for the `merkleize` function and is used to ensure that the number of leaves being merkleised is a power of 2.

A relatively straight forward mathematical helper function it is important to make sure that an input of zero maps to an output of 1.

Hence the `next_pow_of_two(i)` function has the following **pre-condition**:

- `0 <= i`

and the following **post-conditions** and **properties**:

- `1 <= next_pow_of_two(i)`
- `next_pow_of_two(i) == next_pow_of_two(next_pow_of_two(i))`
- `is_power2(next_pow_of_two(i)) == true`

**TODO**: add addition properties

[Dafny reference.]()
**TODO**: add link

6.  `merkleize`

Defined in the Eth2.0 spec as:

>`merkleize(chunks, limit=None)`: Given ordered `BYTES_PER_CHUNK`-byte chunks, merkleize the chunks, and return the root:
> - The merkleization depends on the effective input, which must be padded/limited:
>   - if no limit: pad the `chunks` with zeroed chunks to `next_pow_of_two(len(chunks))` (virtually for memory efficiency).
>   - if `limit >= len(chunks)`, pad the `chunks` with zeroed chunks to `next_pow_of_two(limit)` (virtually for memory efficiency).
>   - if `limit < len(chunks)`: do not merkleize, input exceeds limit. Raise an error instead.
> - Then, merkleize the chunks (empty input is padded to 1 zero chunk):
>   - If `1` chunk: the root is the chunk itself.
>   - If `> 1` chunks: merkleize as binary tree.

The `merkleize` function takes a series of 32 byte `chunks` and a `limit` parameter. 

The chunks are used to form the leaves of a binary merkle tree and the function returns the root of that tree. Note that `len(chunks) >= 0` and hence as the chunks will form the leaves of the binary tree, chunk padding may need to be implemented to ensure that the number of leaves is a power of 2. Which _power of 2_ depends on the `limit` parameter. If there is no limit then we simply pad with zeroed chunks to `next_pow_of_two(len(chunks))` (virtually for memory efficiency). If `limit >= len(chunks)` then we pad with zeroed chunks to `next_pow_of_two(len(chunks))` (virtually for memory efficiency). And if neither of these cases apply then we have a situation where something has gone wrong and the `limit < len(chunks)`; in which case an error should be raised.

The limit parameter has a default value of `None` but is generally set to `chunk_count(type)` where the `value` being processed is a variable length type such as a list or a bitlist. The use of something other than the default is to ensure that sufficient leaves are created to allow for the maximum length of that type, regardless of its current length. I say _generally_ in the context of it being used for variable length types because `limit=chunk_count(type)` also appears for a bitvector; though in this case the use of the limit is redundant because a bitvector is a fixed length type and so that is no need for the provision of additional leaves; it can be seen that `len(chunks) == chunk_count(type)`.

At this point in the processing the number of chunks, i.e. leaves, is a power of 2 and we are ready to create the binary merkle tree. Because of the chunk padding rule we should note that there will be a minimum of 1 chunk. For example, even if zero chunks were sent into the `merkleize` function (e.g. as in the case of a `list[B,0]`) because `next_pow_of_two(0) == 1` we will have 1 chunk after padding. Hence it should be noted that the second step of this function, namely `Then, merkleize the chunks (empty input is padded to 1 zero chunk)` includes some redundancy as _empty input_ can not occur at this stage in the processing.

This second step completes the processing: if we have 1 chunk then that is the root and can be returned, if we have more than 1 chunk then we implement merkelization as a binary tree.

[Dafny reference.]()
**TODO**: add link

7.  `mix_in_length`

Defined in the Eth2.0 spec as:

>`mix_in_length`: Given a Merkle root `root` and a length `length` (`"uint256"` little-endian serialization) return `hash(root + length)`.

This function is used for variable length types i.e. where the length of the value may be less than the maximum specified. The _maximum_ is encoded into the binary merkle tree be the provision of sufficient leaves to store a value of this maximum length, however the _actual length_ must also be represented and is done so through the `mix_in_length` function. The merkle root generated from the `merkleize` function is concatenated with the actual length (i.e. where length is represented as a `uint256` using little-endian serialization) and then hashed.

**TODO**: add diagram similar to that in merkle-proofs.md

[Dafny reference.]()
**TODO**: add link

8.  `mix_in_type`

Used in the context of unions.

# Other TODOs:

**TODO**: Check that all pre and post conditions are referenced.
**TODO**: Check that all properties are referenced.
**TODO**: Check markdown formatting and links.
