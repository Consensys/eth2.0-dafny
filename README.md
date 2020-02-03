# eth2.0-dafny

The objective of this project is to write a specification of the Eth2.0 spec in Dafny.

## Ethereum Search Engine

* [Search engine](https://ethsear.ch/)

## Useful Repositories - Eth 2.0 Spec

* [What's new in Ethereumn? by Ben Edgington](https://notes.ethereum.org/@ChihChengLiang/Sk8Zs--CQ/https%3A%2F%2Fhackmd.io%2F%40benjaminion%2Fwnie2_200124?type=book)

* [Eth2.0 spec](https://github.com/ethereum/eth2.0-specs)

* [Becon chain spec in K](https://github.com/runtimeverification/beacon-chain-spec)

* [SSZ types](https://github.com/prysmaticlabs/go-ssz) and [Eth2-ssz-spec](https://github.com/ethereum/eth2.0-specs/blob/master/specs/simple-serialize.md)

* [Eth2.0 spec blob](https://github.com/ethereum/eth2.0-specs/blob/v0.10.0/README.md)

* [Artemis (full java client that implements the actual state transitions of the beacon chain spec)](https://github.com/PegaSysEng/artemis/)

* [Tuweni (may be used in Artemis), basic SSZ functionality](https://tuweni.apache.org)

### Phase 0 Resources

* [djrtwo docs](https://notes.ethereum.org/@djrtwo/Bkn3zpwxB?type=view)
* [V. Buterin docs](https://notes.ethereum.org/@vbuterin/HkiULaluS)
* [Protolambda docs](<https://github.com/protolambda/eth2-docs>)
* [V. Buterin notes](https://notes.ethereum.org/@vbuterin/rkhCgQteN)

### Phase 1&2 Resources

* [Phase 2 progress - William Villanueva](https://medium.com/@william.j.villanueva/ethereum-2-0-phase-2-progress-7673b57eabff)

* [Relay networks, fee markets eth2.0 - John Adler](https://medium.com/@adlerjohn/relay-networks-and-fee-markets-in-eth-2-0-878e576f980b)

* [Phase 1 fee and eth1-eth2 bridging](https://ethresear.ch/t/phase-1-fee-market-and-eth1-eth2-bridging/6775)

* [State provider models](https://ethresear.ch/t/state-provider-models-in-ethereum-2-0/6750)

* [Shards - Problem statement](https://ethresear.ch/t/moving-eth-between-shards-the-problem-statement/6597)

* [Single Secret Leader Election paper](https://eprint.iacr.org/2020/025.pdf)

## Useful Repositories - Dafny

* [Dafny github repo](https://github.com/dafny-lang/dafny)

* [VSCode](https://code.visualstudio.com), to use DAfmy on MacOS and Linux

* [Dafny-extension-for-VSCode](https://marketplace.visualstudio.com/items?itemName=correctnessLab.dafny-vscode)

* [Verification Corner](https://www.youtube.com/channel/UCP2eLEql4tROYmIYm5mA27A), tutorials by Rustan Leino.

* [Tutorial paper](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml220.pdf)

* [Solutions to exercises in previous tutorials](https://github.com/bor0/dafny-tutorial)

* [IronClad project (2015, Dafny spec)](https://github.com/Microsoft/Ironclad/tree/master/ironfleet)

## Expected results

The paper [An Executable K Model of Ethereum 2.0 Beacon Chain Phase 0 Specification](https://github.com/runtimeverification/beacon-chain-spec/blob/master/report/bck-report.pdf) describes how the K-framework can be used to:

* provide a formal semantics to Eth2.0 spec (phase 0)
* derive an executabkle model from it
* provide some insight into test coverage (using the current test suites).

This is a very nice work in terms of formalising the Eth2.0 specs.
However, the current state of the K-framework is limited to testing, and testing can find bugs but cannot prove the absence of bugs.

To complement this work, we may try to provide some guarantees that the Eth2.0 spec is bug-free.
We can try to do so by leveraging the power of verification-friendly languages like Dafny.
The idea is to write a Dafny spec of Eth2.0 with the expected correstness properties embedded in it (annotations such a program invariants).

This work should be simplified thanks to the formal specification of Eth2.0 in K: this provides a solid formal basis for writing the Dafny code.
The annotations however, are to be carefully inserted, and the invariants that enable Dafny to establish their correctness have to be manually written. This is what we plan to do in this project.
