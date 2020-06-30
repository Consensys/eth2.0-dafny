

# Simple SerialiaZe (SSZ) Library

This file contains notes about the Eth2.0 specifications of SSZ and links to the corresponding formal definitions in Dafny.

## Overview

The SSZ functions aims at providing some functionalities to encode data structures as sequences of bytes, via  _serialise_ and decode sequences of bytes to reconstruct a data structure _deserialise_.

Given an object `O`, its serialised version is `serialise(O)` which is a finite sequence of bytes.
Conversely, given a finite sequence of bytes `xs`, and a data structure's type `Tipe`, `deserialise(xs, Type)` should reconstruct, when possible,  an object of type `Tipe` from the given sequence of bytes.

## Informal Specifications

An object that can be serialised is of type `Serialisable` in SSZ (`Serialisable` can be thought of as a trait.)
Given a type `T`, we write  `T <: Serialisable` if `T` extends (or inherits) `Serialisable`.

Each type `T <: Serialisable` should offer two  functions:

* `serialise<T> : T --> seq<bytes>`, a total function that returns a sequence of bytes when applied to an object of type `T`, i.e. 
 
* and `deserialise<T> : Seq<bytes>  ~-> T` with `xs` a sequence of bytes, 
returns an object of type `T` **when it is possible to deserialise `xs` in an object of type `T`**.
Indeed, `deserialise` may fail when it is not possible to reconstruct an object of the target type from a sequence of bytes and as a consequence, `deserialise` is a _partial function_.


How objects of type `T <: Serialisable` are serialised and deserialised is explained in the sequel.

## Expected Properties

Given an object `O1 : T`, `O2 : T` (read "O of type T") where `T <: Serialisable`, the pair of functions `(serialise<T>, deserialise<T>)` should be:

* Involutive: `deserialise<T>(serialise<T>(O1)) = O1`,
* Injective: `serialise<T>(O1) = serialise<T>(O2)` implies that `O1 = O2`.

## SSZ in Eth2

In the Eth2 specification, SSZ provides serialisation and deserialisation for

* **Basic types** i.e. integers, Booleans,
* **List** and **vectors of bits**, known as BitLists and BitVectors,
* **Lists** and **vectors** of `Serialisable`,
* **Containers** with `Serialisable` fieds,
* and Unions that we omit in this project.

## Formal Specifications

### Booleans

Booleans are probably the simplest `Serialisable` to serialise and deserialise.
The Boolean value `true` (resp. `false`) is serialised into a byte of value `1` (resp. `0`).
Note that this implies that the co-domain of `serialise<Booleans>` is the set of bytes `{0,1}`. As a result the domain of `deserialise<Booleans>` must be `{0,1}`. 

The complete formal Dafny definition is available [in this file](https://github.com/PegaSysEng/eth2.0-dafny/blob/master/src/dafny/ssz/BoolSeDes.dfy). 

### Unsigned Integers

The Eth2.0 specifications restrict unsigned integers to a finite number of cases:
`uintN`: `N`-bit unsigned integer, where `N` in `{8, 16, 32, 64, 128, 256}`.

We provide here a general definition of the serialisation of an unsigned mathematical integer (unbounded) over a number of bytes.
Given a unsigned integer, i.e. a natural number `n`, and `k` another natural which is the number of bytes to serialise `n`, we define `serialise<nat>(n, k)` recursively, and only for values of `k` such the k-bytes that can accommodate the value of `n`.

If follows that we must have `n < 2^(8 * k)` to be able to encode `n` over `k` bytes.
Hence `serialise<nat>(n, k)` is only defined for values `n, k` such that  `n < 2^(8 * k)`.

The serialisation of `n` over `k` bytes is defined inductively as follows:

```
function serialise<nat>(n: nat, k: nat) : seq<byte>
    requires n < power2(8 * k) 
{
    if ( k == 1 ) then 
        [n as byte]
    else 
        [(n % 256) as byte] + uintSe( n / 256, k - 1)
}
```

in other words, if `b[k]b[k-1] ... b[0]`   is the little-endian bitvector representation of `n` over  
`8 * k` bits, then `serialise<nat>(n,k) = b[0]b[1] ... b[k]`.  
The complete formal Dafny definition is available [in this file](https://github.com/PegaSysEng/eth2.0-dafny/blob/master/src/dafny/ssz/IntSeDes.dfy) along with the proof that the previous algorithm always terminate.
Serialisation for `uintN`, where `N` in `{8, 16, 32, 64, 128, 256}` are special cases of the previous
function.

Deserialising a sequence of bytes `xb` into an unsigned integer works as expected by interpreting `xb` as the reversed sequence of the bitvector representation of the number: there must be at least one byte to deserialise, and the result will be an unsigned integer less than `2^( 8 * |xb|)`:

```
function deserialise<nat>(xb : seq<byte>) : nat
    requires |xb| >= 1
    ensures uintDes(xb) < power2(8 * |xb|) 
{
    if ( |xb| == 1 ) then 
        xb[0] as nat
    else 
        (xb[0] as nat) + 256 * uintDes(xb[1..])
}
```

Note however that deserialising a sequence of bytes `xb` into for `uintN`, where `N` in `{8, 16, 32, 64, 128, 256}` requires special checks to make the target type can represent the bitvector values given by `xb`. 
For instance, `deserialise<uint8>`'s domain is the set of sequences `xb` of length `1`.
More generally,  `deserialise<uintk>`'s domain is the set of sequences `xb` of length `|xb| * 8 = k`.

The complete formal Dafny definition is available [in this file](https://github.com/PegaSysEng/eth2.0-dafny/blob/master/src/dafny/ssz/IntSeDes.dfy) along with the proof of involution.


### Bitlists



## Notes

Current Dafny SSZ module does not constraint the length of serialised object to be deserialised.
Deserialise may fail if the object cannot be unpacked into the target type.
We have to account for this behaviour.

Two solutions:

* We accept that this can happen at runtime, and we want to prove that in that case we return a Failure (e.g. Try type in Scala) or Option type (or Either type).
This is what is currently implemented.
* We only deal with the happy case in the first specification.

We may also check that the sequence of bytes to be decoded has been fully consumed at the end of the decoding process.

### Py-ssz

The tests for bitvectors seem to assume that every encoded bitvector has a size which is a multiple of 8.

### Java implementation

The java implementation (Cava) does not seem to encode vectors (nor bitvectors).
It does not support bitList neither.
It provides encoding for String that are not in simple-serilise.md.
The encoding does not seem to be recursively defined. For instance there methods
for encoding List of int8, list of int16 and so on.

## Dafny notes

Match can only be used on datatype not on classes.
Use of bitvectors is not ideal:

* Seems the cast from/to int is not properly inlined in some proofs
* Z3 is not very good at bitvector and proofs take ages (when the solver can do it).

For instance Dafny can work out the proof of seDesInvolutive without hints with uint8 but needs a full proof for bv8.

## Todo list

* deserialise: add the non processed part of the sequence to decode to the returned result.

## Reported issues

* [Tuweni encoding of bitlists](https://github.com/apache/incubator-tuweni/issues/49#issue-571773400)
* [SSZ bitlists/variable parts](https://github.com/ethereum/eth2.0-specs/issues/1630#issue-571003824)
