# What can go wrong with the Beacon Chain? 

In this simple context, one may think that it is easy enough to implement the state machine and the state transition function that computes the new state after accepting a valid transaction.

First there are numerous examples of flawed and buggy implementations of seemingly simple and well studied algorithms:

 * In 2015, European researchers found a bug in the standard implementation of Timsort (a sorting algorithm used in the Python and Java libraries). Overflows could occur in the implementations.
 * In 2008, the Zune (MP3 player) was unresponsive (and unusable!) for a day at the end of 2008 due to an _infinite loop_ bug (less than 10 lines of code) that only occurred on a leap year.

Second, the actual specification of the Beacon Chain is much more complex than the simplified version we have presented so far. 
The state has several components rather than the two, balances and the entry point. 
Some of the information stored in the state is encoded as a hash which is a compact and fixed-size digest of a data structure. 
Moreover, when a state transition occurs, the previous state (its hash) is recorded in the new block (`state_root`). 
This enables efficient checks (including the validity of a block) and operations but at the same time makes the computation of the  state transition function error-prone.  

# What are the desirable properties of the Beacon Chain? 
As for Timsort, **underflows or overflows** can have dire consequences: the Beacon Chain specifies the type of many variables including the balances to be unsigned integers over 64 bits. 
It is therefore important to make sure that no under/overflow can ever occur as this would result in inconsistent values (the result of the product `2^32 * 2^32` cannot be represented on 64 bits).

Another source of error is in building the linked list. Can we guarantee that, at any time, there is **no cycle in the linked list**? 
A cycle in the list would yield an infinite loop (similar to the Zune bug) if we were to collect the parent elements of a given block in the store. 
Collecting parents is an operation needed in the Beacon Chain specifications (computing _ancestors_). Can we guarantee that **all the sequences of blocks** obtained following the link to the previous one eventually **lead to the genesis block**?
Finally there is some **consistency** to guarantee **between the state and the store**: the summary provided by the state should match the result of the effects of the corresponding sequence of transactions.

Notice that these properties do not have anything to do with distributed/decentralised algorithms, but are **requirements about the state machine** that records the transactions. 
The decentralised version of the Beacon Chain implements the Beacon Chain as a replication of this state machine [2]. As a result, bugs in the state machine will carry over to the replicated (decentralised) version of the state machine. 

# Debugging the Beacon Chain

The Eth2.0 Specifications aim to provide a detailed description of the mechanisms and computations of the Beacon Chain. 
However, they are written in an operational style (based off Python) much akin to an implementation. They provide detailed descriptions of how the results of each function are computed rather than what is expected to be computed. 
They form a solid basis to understand the clever ideas of the specifications’ writers. 
The Eth2.0 specifications also contain numerous `assert` statements that can help in debugging. 
For instance one of the functions used in the computation of state transition starts with:

```python
def process_slots(state: BeaconState, slot: Slot) -> None:
    assert state.slot < slot
```

The informal intent of the `assert` statement is that, if it is violated, then the computation should somehow abort and restore a _good_ state. 
What a good state is is not precisely defined.
These `assert` statements can be used in an executable semantics. 
For instance, the meaning of the Eth2.0 Phase 0 can be precisely defined by a formal semantics e.g. within the K-framework [1]. The result is an executable model of the Eth2.0 Phase 0 specifications. It can be tested on arbitrary inputs and used to check whether `assert` statements are violated on these inputs. This is extremely useful and critical bugs have been uncovered using this approach. 

While useful this approach has some limitations:

* The first one is that **testing is incomplete**, not all inputs can be tested. 
If a test suite does not trigger an `assert` statement violation, this does not imply that it can never be violated, but rather that no test vectors in the test suite revealed a violation. As quoted by _Dijkstra_ almost fifty years ago:

> “Program testing can be used to show the presence of bugs, 
but never to show their absence!”
>
> ― Edsger W. Dijkstra (1930–2002), Turing Award 1972

 * The second one is that some desirable properties, e.g. **absence of cycle in chain of blocks**, cannot be specified with `assert` statements.

* A third one is rather subtle. The `assert` statements in the Eth2.0 specifications act as triggers for **exceptions**. 
It is not clear how and at which level such an exception should be caught, and this is error-prone. For example the code above, `process_slots`, is called  in `state_transition`, which is itself called in `on_block`. 
If the `assert state.slot < slot` is violated where is the exception supposed to be caught?

* A fourth one is a risk that the **specifications are inconsistent**. It could be the case that, given a valid input transaction (block) that should be added to the store, some incompatible conditions in the `assert` statements occur wrongly triggering an exception. 

On top of the previous shortcomings, there is another difficulty that Eth2.0 client developers could face. 
This is exemplified by the following `state_transition` Eth2.0 specification (slightly simplified):

```python
def state_transition( s: BeaconState, block: BeaconBlock) -> BeaconState:
    # Process slots (including those with no blocks) since block
    process_slots(s, block.slot)
    ...
```
The `state_transition` computation can fail if an `assert` statement is violated in one of the steps involved in the computation. 
Some of the steps are performed by functions like the previously mentioned `process_slots`. 
This makes it hard for a developer to design some tests and when a test fails to understand what went wrong. 
The specification of `state_transition` as it is, states that if an `assert` statement is violated, then the proposed transaction in block is not valid in the state `s`, but it does not define the properties a valid block should satisfy. 
In other words, the properties the block should satisfy to be valid are implicitly defined by the conditions under which the execution of `state_transition` does not violate any `assert` statements.

So the question is: can we do better? 
Can we provide **specifications capturing what** is to be computed rather than how? 
Can we provide guarantees that the specifications are consistent? 
Guarantees that there is no under/overflows, no cycle in the chain?

The answer is yes, and this starts by designing a **formal functional specification**.
From this formal specification we can propose an implementation and proofs that the implementation satisfies the specification. To do so we use **Dafny** to
write the specification, the implementation and the proofs.

The following notes provide some guidance to read our formal Dafny specs: 

* [Notes on SSZ](./ssz-notes.md).
* [Notes on Merkleisation](./merkleise-notes),
* [Notes on Beacon Chain](./beacon-notes.md).



# References 

[1] **An Executable K Model of Ethereum 2.0 Beacon Chain Phase 0 Specification**. Musab A. Altruki, Denis Bogdanas, Chris Hathhorn, Daejun Park, Grigore Rosu.
Runtime Verification Inc., 2019

[2] **The Implementation of Reliable Distributed Multiprocess Systems**. Leslie Lamport. Comput. Networks 2: 95-114 (1978)


