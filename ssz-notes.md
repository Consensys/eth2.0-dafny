
# SSZ Library

This file contains notes about work in progress on specifying SSZ in Dafny.

## Overview

The Simple Serializable package aims at providing some functionalities to encode data structures as sequences of bytes (serialise) and decode sequences of bytes to reconstruct a data structure (deserialise).
As a result SSZ provides two main functions: `serialise` and `deserialise`.

Given an object `O`, it serialised version is `serialise(O)` which is a finite sequence of bytes.
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

