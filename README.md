# eth2.0-dafny

The objective of this project is to write a specification of the Eth2.0 spec in Dafny.

## Useful Repositories - Eth 2.0 Spec

* [Eth2.0 spec](https://github.com/ethereum/eth2.0-specs)

* [Becon chain spec in K](https://github.com/runtimeverification/beacon-chain-spec)

* [SSZ types](https://github.com/prysmaticlabs/go-ssz) and [Eth2-ssz-spec](https://github.com/ethereum/eth2.0-specs/blob/master/specs/simple-serialize.md)

## Useful Repositories - Dafny

* [Dafny](https://github.com/dafny-lang/dafny)

* [VSCode](https://code.visualstudio.com)

* [Dafny-extension-for-VSCode](https://marketplace.visualstudio.com/items?itemName=correctnessLab.dafny-vscode)

* [Verification Corner](https://www.youtube.com/channel/UCP2eLEql4tROYmIYm5mA27A)

* [IronClad project](https://github.com/Microsoft/Ironclad/tree/master/ironfleet)

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
