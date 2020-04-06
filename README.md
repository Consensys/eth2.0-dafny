
[![Build Status](https://circleci.com/gh/PegaSysEng/eth2.0-dafny.svg?style=shield)](https://circleci.com/gh/PegaSysEng/workflows/eth2.0-dafny) 
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

# Overview 

## eth2.0-dafny

The objective of this project is to write a **formal specification** of the Eth2.0 specification in the verification-aware programming language [Dafny](https://github.com/dafny-lang/dafny/wiki).

More specifically, our goals in this project are many-fold:

1. Write a **formal (non-ambiguous) specification** of the Eth2.0 specification.
This specification is written using pre/post-conditions using the [Hoare logic](https://en.wikipedia.org/wiki/Hoare_logic) style proof.
2. Write an **implementation** for each function to demonstrate that the specification _can be implemented_, in other words, it is not inconsistent.
3. **Formally prove** that our implementation satisfies the specification. The formal proof is provided in the form of mathematical proofs of lemmas written in Dafny.

To achieve this, we use the capabilities of the verification-aware programming language Dafny to write the specification, the implementation, and the proofs.

## Expected Results

Dafny provides extensive support for automated reasoning leveraging the power of state-of-start automated reasoning engines (SMT-solvers).
As a result, Dafny can assist in proving the lemmas that specify **correctness**.
Moreover, as the lemmas are written as Dafny programs, they provide a **non-ambiguous mathematical proof** that the code is correct with respect to a specification.
All the proofs can be **mechanically verified** using theorem provers.

## Current State 

We are gradually adding the specifications, implementations and proofs.
Our current focus in on Phase 0 of the Eth2 specifications: SSZ, Merkleisation and Beacon chain.  

# Background & Context

The Eth2.0 specifications are rather complex.
As a consequence bugs, glitches or inconsistencies can creep into the specification and the implementation code.

Testing and code peer reviews can help keeping the bugs count low.
However, testing can find some bugs but in general _cannot guarantee the absence of bugs_ ([Edsger W. Dijkstra](https://en.wikiquote.org/wiki/Edsger_W._Dijkstra)).

These bugs remain uncovered ... until they manifest, resulting in crashes.
Worse, they can be exploited as _security vulnerabilities_.
An example of critical vulnerability is the OutOfBounds exception where a non-existent index in an array is accessed. This is one of the most common _zero day_ attacks, and can occur in heavily tested code bases
[e.g. in the web brower Chromium](https://latesthackingnews.com/2020/02/26/google-patch-serious-chrome-bugs-including-a-zero-day-under-active-exploit/).

# Related Work



Runtime Verification Inc. have reported some work on:
<!-- 
The paper [An Executable K Model of Ethereum 2.0 Beacon Chain Phase 0 Specification](https://github.com/runtimeverification/beacon-chain-spec/blob/master/report/bck-report.pdf) describes how the K-framework can be used to:

* provide a formal semantics to Eth2.0 spec (phase 0)
* derive an executable model from it
* provide some insight into test coverage (using the current test suites).

This is a very nice work in terms of formalising the Eth2.0 specs.
However, the current state of the K-framework is limited to testing, and as mentioned before _testing can find bugs but cannot prove the absence of bugs._ -->

* a [formal semantics of Ethereum 2.0 Beacon Chain Phase 0 Specification](https://github.com/runtimeverification/beacon-chain-spec/) using the K framework. 
* the [initial formal verification of the Casper protocol](https://runtimeverification.com/blog/runtime-verification-completes-formal-verification-of-ethereum-casper-protocol/).
* the [verification of the deposit smart contract](https://blog.ethereum.org/2020/02/04/eth2-quick-update-no-8/)

More recently, a [security audit](https://blog.ethereum.org/2020/03/31/eth2-quick-update-no-10/) was performed by LeastAuthority. 

Our work aims to complement the previous work by providing a formal verification of the Eth2.0 phase 0 specifications. 


# Useful Resources

* [Eth2.0](wiki/eth2-specs.md) resources, specifications and implementations.
* [Dafny](wiki/dafny.md), install and learn.
* [Other](wiki/other-resources.md), eth2.0 specifications audits.

# How to install (and check the proofs)

* install Dafny, see [our Dafny wiki](wiki/dafny.md).
* Pull/clone this repository.

## Checking the proofs

Assuming you have a running Dafny compiler, you may use the following command line to check a `*.dfy` file:

```
> dafny /dafnyVerify:1 /compile:0  /timeLimit:60 src/dafny/utils/MathHelpers.dfy
Dafny 2.3.0.10506

Dafny program verifier finished with 13 verified, 0 errors
```

## Compiling and Running the code

The [test folder](https://github.com/PegaSysEng/eth2.0-dafny/tree/master/test/dafny) contains some tests. 
The purpose of this directory is to demonstrate that we can extract an implementation and run it (indeed, once we have proved the code, there is no need to test it).
To run the tests, you can issue the following command from the root directory (it collects all the files in the test folder, compile them and run them):

```
> ./scripts/runAllTests.sh 
```

<!-- ## Compile into C#, Go, JS -->


<!-- * video with how to see verified or bugs. -->
