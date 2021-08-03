

[![License](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0) 
<!-- ![GitHub commit activity](https://img.shields.io/github/commit-activity/w/PegaSysEng/eth2.0-dafny?style=flat) -->
[![made-for-VSCode](https://img.shields.io/badge/Made%20for-VSCode-1f425f.svg)](https://code.visualstudio.com/)

 [![lemmas](https://img.shields.io/badge/Lemmas-230-yellow.svg)](https://shields.io/) 
 [![Checks](https://img.shields.io/badge/DafnyVerify-VerifiedWithAssumes-orange.svg)](https://shields.io/) 

# Overview 

This branch of the project aims to provide a proof that the computed justified (resp. finalised) check points are indeed justified (resp. finalised).

This project was started by ConsenSys R&D and was also supported by the Ethereum Foundation under grant [FY20-285, Q4-2020](https://blog.ethereum.org/2021/03/22/esp-allocation-update-q4-2020/).

## Results

The current state of this branch (as of August 2nd 2021) is as follows:

1. a [specification and proof](https://github.com/ConsenSys/eth2.0-dafny/tree/goal1/src/dafny/beacon/gasper) of the GasperFFG protocol.
    This package is fully proved (Dafny verification succeeds with no assumptions).
2. functional specifications and implementations of the state updates (Epoch) in [package stattransition](https://github.com/ConsenSys/eth2.0-dafny/tree/goal1/src/dafny/beacon/statetransition). This package does not fully verify. There are assumptions that could not be discharged in the [top level specification file](https://github.com/ConsenSys/eth2.0-dafny/blob/goal1/src/dafny/beacon/statetransition/StateTransition.s.dfy) and its [implementation](https://github.com/ConsenSys/eth2.0-dafny/blob/goal1/src/dafny/beacon/statetransition/StateTransition.dfy).
  
Some statistics about the project can be found in

* the master stats [table](https://github.com/ConsenSys/eth2.0-dafny/tree/master/wiki/stats.md),
* the goal1 stats [table](./wiki/stats.md).

Some **call graphs** are also available (DOT-Graphviz format) alongside the corresponding Dafny files.


## Assumptions

The main assumptions used in the Gasper proof are:
1. the **set of validators is fixed and has size equal to MAX_VALIDATORS_PER_COMMITTEE**.
2. each validator's stake is 1 (one) ETH.

The proof establishes lemmas 4 and lemma 5 from the GasperFFG paper [Combining GHOST and Casper](https://arxiv.org/abs/2003.03052).

The proof should work for a non fixed set of validators (the conclusion is weaker in that case) but this would require adding ``indexedAttestations`` instead of ``PendingAttestation``. 

The assumption on the unit stake does has no impact on the proof. This assumption is also made in  [Combining GHOST and Casper](https://arxiv.org/abs/2003.03052). As the computations using the stakes are linear this does not affect the correctness result.

# Contributing to this branch and merging into Master

This branch has diverged from master.
The main issue is that the number of assumptions ``requires`` needed for the proof of ``stateTransition`` cannot be easily discharged.

Before attempting a merge, it may be helpful to provide a functional definition of valid attestations [here](https://github.com/ConsenSys/eth2.0-dafny/blob/goal1/src/dafny/beacon/attestations/AttestationsHelpers.dfy) in a given state.

1. the use of the ``opaque`` attribute may help speeding up some proofs. 
2. re-factoring the code and providing defintions with weaker pre-conditions.  

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
This work presents a formal semantics of the Eth2.0 specifications in the K-framework. 
The semantics are executable and can be used for testing e.g. symbolic execution. 
* the [initial formal verification of the Casper protocol](https://runtimeverification.com/blog/runtime-verification-completes-formal-verification-of-ethereum-casper-protocol/).
* the [verification of the deposit smart contract](https://blog.ethereum.org/2020/02/04/eth2-quick-update-no-8/)
* a [security audit](https://blog.ethereum.org/2020/03/31/eth2-quick-update-no-10/) was performed by LeastAuthority. 
The code was manually reviewed and some potential security vulnerabilities highlighted.

Our work aims to complement the previous work by providing a thorough formal verification of the Eth2.0 phase 0 specifications.

# Useful Resources

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

