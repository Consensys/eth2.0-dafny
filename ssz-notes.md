
# SSZ Library

This file contains notes about work in progress on specifying SSZ in Dafny.

## Overview

The Simple Serializable package aims at providing some functionalities to encode data structures as sequences of bytes (serialise) and decode sequences of bytes to reconstruct a data structure (deserialise).
As a result SSZ provides two main functions: `serialise` and `deserialise`.

Given an object `O`, its serialised version is `serialise(O)` which is a finite sequence of bytes.
Conversely, given a sequence of bytes `s`, and a data structure (type) `Type`, `deserialise(s, Type)` should reconstruct an object of type `Type` from the given sequence of bytes.

Note that `deserialise` may fail when it is not possible to reconstruct an object of the target type from a sequence of bytes: `deserialise` is a partial mapping.

## Specification

Given an object `O : T`, the pair of functions `(serialise, deserialise)` should be:

* Involutive: `deserialise(serialise(O), T) = O`,
* Injective: `serialise(O1) = serialise(O2)` implies that `O1 = O2`.

## SSZ in Eth2

In the Eth2 specification, SSZ provides serialisation and deserialisation for

* Basic types (integers, Booleans)
* arrays, vectors, lists of basic types,
* record types.

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
