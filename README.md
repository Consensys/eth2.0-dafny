
<!-- [![Build Status](https://circleci.com/gh/ConsenSys/eth2.0-dafny.svg?style=shield)](https://circleci.com/gh/ConsenSys/workflows/eth2.0-dafny)  -->
[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0) 
[![made-for-VSCode](https://img.shields.io/badge/Made%20for-VSCode-1f425f.svg)](https://code.visualstudio.com/)
[![lemmas](https://img.shields.io/badge/Lemmas-378-yellow.svg)](https://shields.io/) 
[![Checks](https://img.shields.io/badge/DafnyVerify-Verified-darkgreen.svg)](https://shields.io/) 

 <!-- ![GitHub commit activity](https://img.shields.io/github/commit-activity/w/PegaSysEng/eth2.0-dafny?style=flat) -->

# Overview 

This project was started by ConsenSys R&D and was also supported by the Ethereum Foundation under grant [FY20-285, Q4-2020](https://blog.ethereum.org/2021/03/22/esp-allocation-update-q4-2020/)

## Objectives

The objective of this project is to write a **formal specification** of the Eth2.0 specification in the verification-aware programming language [Dafny](https://github.com/dafny-lang/dafny/wiki).

More specifically, our goals in this project are many-fold:

1. Write a **formal (non-ambiguous and functional) specification** of the Eth2.0 specification.
This specification is written with pre/post-conditions using the [Hoare logic](https://en.wikipedia.org/wiki/Hoare_logic) style proof.
2. Write an **implementation** for each function to demonstrate that the specification _can be implemented_, in other words, it is not inconsistent.
3. **Formally prove** that our implementation satisfies the specification. The formal proof is provided in the form of mathematical proofs of lemmas written in Dafny.

To achieve this, we use the capabilities of the verification-aware programming language [Dafny](https://github.com/dafny-lang/dafny) to write the specification, the implementation, and the proofs.

## How to use the verified code?

Depending on your inclination you may use the verified code in different ways:

* you can find **function specifications**  (usually in ``.s.dfy`` files). They describe state changes as functions mapping a state (and other parameters like blocks) to a new state;
These specifications can help to write your own client in your preferred language (including functional programming languages); we have provided an example of implementation for each function, adapted from the [Eth2.0 reference spec](https://github.com/ethereum/eth2.0-specs).

* you may **contribute new code and proofs** by either adding functions we have not implemented yet or even test that new ideas and optimisations do not break the proofs;

* you may use Dafny to **generate target code** (e.g. Go, Java, C#, JavaScript) and see how the automated generated code can replace or complement your code base;

* you may use the specifications to help in **unit testing** your own code. The specifications contain **unambiguous pre and post conditions** that clearly specify the effect of a function/method.  They can be used to write property-drive tests.


## Methodology

Dafny provides extensive support for automated reasoning leveraging the power of state-of-start automated reasoning engines (SMT-solvers).
As a result, Dafny can assist in proving the lemmas that specify **correctness**.
Moreover, as the lemmas are written as Dafny programs, they provide a **non-ambiguous mathematical proof** that the code is correct with respect to a specification.
All the proofs can be **mechanically verified** using theorem provers.

## Results

This repository contains two main branches:

* [master](https://github.com/ConsenSys/eth2.0-dafny) with a substantial part of the verified Eth2.0 specs. The verified Dafny code **guarantees the absence of runtime errors** like array-out-of-bounds, division-by-zero. It also provides some functional proofs captured by the **invariants** in the top-level [ForkChoice.dfy](https://github.com/ConsenSys/eth2.0-dafny/blob/master/src/dafny/beacon/forkchoice/ForkChoice.dfy) file: 
* [goal1](https://github.com/ConsenSys/eth2.0-dafny/tree/goal1) with some proofs related to justification and finalisation. This branch has diverged from [master](https://github.com/ConsenSys/eth2.0-dafny) and may not be easily merged into it.

## Statistics

Some statistics about the project can be found in

* the master stats [table](./wiki/stats-master.md),
* the goal1 stats [table](https://github.com/ConsenSys/eth2.0-dafny/tree/goal1/wiki/stats.md).

Some **call graphs** are also available (DOT-Graphviz format) alongside the corresponding Dafny files.

A birds-eye view of the (more than 200) functions we have implemented is given by the [top-level call graph](https://raw.githubusercontent.com/ConsenSys/eth2.0-dafny/master/top-level-call-graph.svg).
## Notes

An introduction (WIP) to the different components of Phase 0 is available in the Wiki section of this repo:

* [Introduction](./wiki/overview.md) to the Beacon Chain,
* [Notes on SSZ](./wiki/ssz-notes.md) specifications, implementations and proofs,
* [Notes on Merkleisation](./wiki/merkleise-notes.md)  specifications, implementations and proofs,
* [Notes  on Beacon Chain](./wiki/beacon-notes.md) specifications, implementations and proofs.

Here is a recent youtube video with a presentation 

[![EEG Meet-up Dafny](EEG-Meetup-Dafny.jpg)](https://www.youtube.com/watch?v=UCSwkUQO_no "EEG: Verification of Eth2.0 using Dafny")


# Why we should formally verify the Eth2.0 specs

## Background & context

The Eth2.0 specifications are subtle and sometimes complex.
As a consequence, bugs, glitches or inconsistencies can creep into the specification and the implementation code.

Testing and code peer reviews can help keeping the bugs count low.
However, testing can find some bugs but in general _cannot guarantee the absence of bugs_ ([Edsger W. Dijkstra](https://en.wikiquote.org/wiki/Edsger_W._Dijkstra)).

These bugs remain uncovered ... until they manifest, resulting in crashes.
Worse, they can be exploited as _security vulnerabilities_.
An example of critical vulnerability is the OutOfBounds exception where a non-existent index in an array is accessed. This is one of the most common _zero day_ attacks, and can occur in heavily tested code bases
[e.g. in the web browser Chromium](https://latesthackingnews.com/2020/02/26/google-patch-serious-chrome-bugs-including-a-zero-day-under-active-exploit/).

You can read more about the specific case of the Beacon Chain in our [Wiki section](./wiki/overview.md).

We have also put together a [video series](./wiki/video_series.md) to introduce this project. 
The videos include discussions on the state transition, fork choice and process operations components of the project.

## Related work

Runtime Verification Inc. have reported some work on:
<!-- 
The paper [An Executable K Model of Ethereum 2.0 Beacon Chain Phase 0 Specification](https://github.com/runtimeverification/beacon-chain-spec/blob/master/report/bck-report.pdf) describes how the K-framework can be used to:

* provide a formal semantics to Eth2.0 spec (phase 0)
* derive an executable model from it
* provide some insight into test coverage (using the current test suites).

This is a very nice work in terms of formalising the Eth2.0 specs.
However, the current state of the K-framework is limited to testing, and as mentioned before _testing can find bugs but cannot prove the absence of bugs._ -->

* a [formal semantics of Ethereum 2.0 Beacon Chain Phase 0 Specification](https://github.com/runtimeverification/beacon-chain-spec/) using the K framework.
This work presents a formal semantics of the Eth2.0 specifications in the K-framework. 
The semantics are executable and can be used for testing e.g. symbolic execution. 
* the [initial formal verification of the Casper protocol](https://runtimeverification.com/blog/runtime-verification-completes-formal-verification-of-ethereum-casper-protocol/).
* the [verification of the deposit smart contract](https://blog.ethereum.org/2020/02/04/eth2-quick-update-no-8/)
* a [security audit](https://blog.ethereum.org/2020/03/31/eth2-quick-update-no-10/) was performed by LeastAuthority. 
The code was manually reviewed and some potential security vulnerabilities highlighted.

Our work aims to complement the previous work by providing a thorough formal verification of the Eth2.0 phase 0 specifications.

# Useful resources

* [Eth2.0 resources](wiki/eth2-specs.md) resources, specifications and implementations.
* [Dafny resources](wiki/dafny.md), install and learn.
* [Coding practices and database of known vulnerabilities](wiki/vulnerabilities.md),
* [Other resources](wiki/other-resources.md), K-framework resources.

# How to check the proofs?

We have checked the proofs with Dafny 3.0.0 and Dafny 3.2.0.

The bash scripts ``verifyAll.sh`` can be used to verify the files in a given directory (e.g. using the Docker container, see below).

For example checking the ``attestations`` package can be done by:

```[bash]
/home/user1/eth2.0-dafny $ time ./verifyAll.sh src/dafny/beacon/attestations   -------------------------------------------------------
Processing src/dafny/beacon/attestations/AttestationsHelpers.dfy with config /dafnyVerify:1 /compile:0  /noCheating:1
/home/user1/eth2.0-dafny/src/dafny/beacon/attestations/../../utils/SetHelpers.dfy(38,17): Warning: /!\ No terms found to trigger on.
/home/user1/eth2.0-dafny/src/dafny/beacon/attestations/../../utils/SetHelpers.dfy(60,22): Warning: /!\ No terms found to trigger on.
/home/user1/eth2.0-dafny/src/dafny/beacon/attestations/../gasper/GasperEBBs.dfy(91,16): Warning: /!\ No terms found to trigger on.
/home/user1/eth2.0-dafny/src/dafny/beacon/attestations/../gasper/GasperEBBs.dfy(159,16): Warning: /!\ No terms found to trigger on.

Dafny program verifier finished with 24 verified, 0 errors
No errors in src/dafny/beacon/attestations/AttestationsHelpers.dfy
-------------------------------------------------------
Processing src/dafny/beacon/attestations/AttestationsTypes.dfy with config /dafnyVerify:1 /compile:0  /noCheating:1
/home/user1/eth2.0-dafny/src/dafny/beacon/attestations/../../utils/SetHelpers.dfy(38,17): Warning: /!\ No terms found to trigger on.
/home/user1/eth2.0-dafny/src/dafny/beacon/attestations/../../utils/SetHelpers.dfy(60,22): Warning: /!\ No terms found to trigger on.

Dafny program verifier finished with 12 verified, 0 errors
No errors in src/dafny/beacon/attestations/AttestationsTypes.dfy
-------------------------------------------------------
[OK] src/dafny/beacon/attestations/AttestationsHelpers.dfy
[OK] src/dafny/beacon/attestations/AttestationsTypes.dfy
Summary: 2 files processed - No errors occured! Great job.
./verifyAll.sh src/dafny/beacon/attestations  29.27s user 0.54s system 102% cpu 29.138 total
```

## Using a Docker container

Pre-requisites:

1. a working installation of [Docker](https://docs.docker.com),
2. a fork or clone of this repository.

A simple way to check the proofs is to use a pre-configured installation of Dafny on a Docker container.

On Unix-based system, `cd` to the root directory of your working copy of this repository.
```
/home/user1/ $ git clone git@github.com:PegaSysEng/eth2.0-dafny.git
/home/user1/ $ cd eth2.0-dafny
/home/user1/eth2.0-dafny $ 
```

The next commands will start a [Docker container](https://hub.docker.com/repository/docker/franck44/linux-dafny) with Dafny pre-installed, and mount your local working directory as a volume in the Docker machine (this way you can access it from the running Docker machine):
```
/home/user1/eth2.0-dafny $ docker run -v /home/user1/eth2.0-dafny:/eth2.0-dafny -it franck44/linux-dafny /bin/bash
root@749938cb155d:/# cd eth2.0-dafny/
root@749938cb155d:/eth2.0-dafny# dafny /dafnyVerify:1 /compile:0 src/dafny/utils/MathHelpers.dfy 
Dafny 2.3.0.10506

Dafny program verifier finished with 13 verified, 0 errors
root@749938cb155d:/eth2.0-dafny# 
```

## Install Dafny on your computer

Pre-requisites:

* install Dafny, see [our Dafny wiki](wiki/dafny.md).
* clone or fork this repository.

Assuming you have a running Dafny compiler, you may use the following command line to check a `*.dfy` file:
```
> dafny /dafnyVerify:1 /compile:0  /timeLimit:60 src/dafny/utils/MathHelpers.dfy
Dafny 2.3.0.10506

Dafny program verifier finished with 13 verified, 0 errors
```

The [test folder](https://github.com/PegaSysEng/eth2.0-dafny/tree/master/test/dafny) contains some tests.
The purpose of this directory is to demonstrate that we can extract an implementation and run it (indeed, once we have proved the code, there is no need to test it).
To run the tests, you can issue the following command from the root directory (it collects all the files in the test folder, compile them and run them):

```
> ./scripts/runAllTests.sh
```

 For an even  better experience you may install VSCode and the Dafny plugin see [our Dafny wiki](https://github.com/PegaSysEng/eth2.0-dafny/wiki/Eth2.0-verification-in-Dafny).

## How to compile to C#, Go

To compile to Go:

```sh
dafny /compileTarget:go /spillTargetCode:1 src/dafny/ssz/BitListSeDes.dfy
```

C# can be targeted by changing `compileTarget` to `cs`.

<!-- * video with how to see verified or bugs. -->
