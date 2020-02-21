include "Constants.dfy"
include "BeaconChain.dfy"
include "NativeTypes.dfy"
include "Types.dfy"
include "Validators.dfy"
include "Helpers.dfy"
include "Merkle.dfy"

/**
 * State transition function for the Beacon Chain.
 */
module StateTransition {

    //  Import some constants and types
    import opened Eth2Constants
    import opened Native__NativeTypes_s
    import opened Eth2Types
    import opened BeaconChain
    import opened Validators
    import opened Helpers
    import opened Merkle


    /** From config.k.
     * @link{https://notes.ethereum.org/@djrtwo/Bkn3zpwxB?type=view} 
     * The beacon chain’s state (BeaconState) is the core object around 
     * which the specification is built. The BeaconState encapsulates 
     * all of the information pertaining to: 
     *  - who the validators are, 
     *  - in what state each of them is in, 
     *  - which chain in the block tree this state belongs to, and 
     *  - a hash-reference to the Ethereum 1 chain.

     * Beginning with the genesis state, the post state of a block is 
     * considered valid if it passes all of the guards within the state 
     * transition function. Thus, the precondition of a block is 
     * recursively defined as being a valid postcondition of running 
     * the state transition function on the previous block and its state 
     * all the way back to the genesis state.
     *
     * @param   genesis_time                    The Unix timestamp of when the genesis slot 
     *                                          occurred. This allows a client to calculate 
     *                                          what the current slot should be according to 
     *                                          wall clock time
     * @param   slot                            Time is divided into “slots” of fixed length 
     *                                          at which actions occur and state transitions 
     *                                          happen. This field tracks the slot of the 
     *                                          containing state, not necessarily the slot 
     *                                          according to the local wall clock
     * @param   fork                            A mechanism for handling forking (upgrading) 
     *                                          the beacon chain. The main purpose here is to
     *                                          handle versioning of signatures and handle 
     *                                          objects of different signatures across fork 
     *                                          boundaries
     * @param   latest_block_header             The latest block header seen in the chain 
     *                                          defining this state. During the slot transition 
     *                                          of the block, the header is stored without the 
     *                                          real state root but instead with a stub of Root
     *                                          () (empty 0x00 bytes). At the start of the next 
     *                                          slot transition before anything has been 
     *                                          modified within state, the state root is 
     *                                          calculated and added to the 
     *                                          latest_block_header. This is done to eliminate 
     *                                          the circular dependency of the state root 
     *                                          being embedded in the block header
     * @param   block_roots                     Per-slot store of the recent block roots. 
     *                                          The block root for a slot is added at the start 
     *                                          of the next slot to avoid the circular 
     *                                          dependency due to the state root being embedded 
     *                                          in the block. For slots that are skipped (no 
     *                                          block in the chain for the given slot), the 
     *                                          most recent block root in the chain prior to 
     *                                          the current slot is stored for the skipped 
     *                                          slot. When validators attest to a given slot, 
     *                                          they use this store of block roots as an 
     *                                          information source to cast their vote.
     * @param   state_roots                     Per-slot store of the recent state roots. 
     *                                          The state root for a slot is stored at the 
     *                                          start of the next slot to avoid a circular 
     *                                          dependency
     * @param   historical_roots                A double batch merkle accumulator of the latest
     *                                          block and state roots defined by 
     *                                          HistoricalBatch to make historic merkle 
     *                                          proofs against. Note that although this field 
     *                                          grows unbounded, it grows at less than ___ MB 
     *                                          per ___ years
     * @param   eth1_data                       The most recent Eth1Data that validators have 
     *                                          come to consensus upon and stored in state. 
     *                                          Validator deposits from eth1 can be processed 
     *                                          up through the latest deposit contained within 
     *                                          the eth1_data root
     * @param   eth1_data_votes                 Running list of votes on new Eth1Data to be 
     *                                          stored in state. If any Eth1Data achieves > 50% 
     *                                          proposer votes in a voting period, this 
     *                                          majority data is stored in state and new 
     *                                          deposits can be processed
     * @param   eth1_deposit_index              Index of the next deposit to be processed. 
     *                                          Deposits must be added to the next block and 
     *                                          processed if state.eth1_data.deposit_count > 
     *                                          state.eth1_deposit_index
     * @param   validators                      List of Validator records, tracking the current
     *                                          full registry. Each validator contains 
     *                                          relevant data such as pubkey, withdrawal 
     *                                          credentials, effective balance, a slashed 
     *                                          boolean, and status (pending, active, exited, 
     *                                          etc)
     * @param   balances                        List mapping 1:1 with the validator_registry. 
     *                                          The granular/frequently changing balances are 
     *                                          pulled out of the validators list to reduce the 
     *                                          amount of re-hashing (in a cache optimized SSZ 
     *                                          implementation) that needs to be performed at 
     *                                          each epoch transition
     * @param   randao_mixes                    The randao mix from each epoch for the past 
     *                                          EPOCHS_PER_HISTORICAL_VECTOR epochs. At the 
     *                                          start of every epoch, the randao_mix from the 
     *                                          previous epoch is copied over as the base of 
     *                                          the current epoch. At each block, the hash of 
     *                                          the block.randao_reveal is xor’d into the 
     *                                          running mix of the current epoch
     * @param   slashings                       per-epoch store of the total slashed GWEI 
     *                                          during that epoch. The sum of this list at any 
     *                                          time gives the “recent slashed balance” and is 
     *                                          used to calculate the proportion of balance 
     *                                          that should be slashed for slashable validators
     * @param   previous_epoch_attestations     Attestations from blocks are converted to 
     *                                          PendingAttestations and stored in state for 
     *                                          bulk accounting at epoch boundaries. We store 
     *                                          two separate lists.
     *                                          List of PendingAttestations for slots from the 
     *                                          previous epoch. note: these are attestations 
     *                                          attesting to slots in the previous epoch, not
     *                                          necessarily those included in blocks during 
     *                                          the previous epoch.
     * @param   current_epoch_attestations      List of PendingAttestations for slots from the 
     *                                          current epoch. Copied over to 
     *                                          previous_epoch_attestations and then emptied at
     *                                          the end of the current epoch processing
     * @param   justification_bits              4 bits used to track justification during the 
     *                                          last 4 epochs to aid in finality calculations
     * @param   previous_justified_checkpoint   The most recent justified Checkpoint as it 
     *                                          was during the previous epoch. Used to validate 
     *                                          attestations from the previous epoch
     * @param   current_justified_checkpoint    The most recent justified Checkpoint during the 
     *                                          current epoch. Used to validate current epoch 
     *                                          attestations and for fork choice purposes
     * @param   finalized_checkpoint            The most recent finalized Checkpoint, prior to
     *                                           which blocks are never reverted.
     */
    datatype BeaconState = BeaconState(
        validators: seq<Validator>,
        // ghost validators_pubkeys : set<BLSPubkey>,
        eth1_data: Eth1Data,
        eth1_deposit_index: uint64,
        balances: seq<Gwei>
    )

    function state_transition(s: BeaconState, b: BeaconBlock ) : BeaconState 
    // requires b.state_root == hash_tree_root_state()
    {
        s
        //  Process slots

        //  Process block
        
        //  Validate state block
    }

    /**
     * 
     */
    function method process_slots(s: BeaconState, slot: Slot) : BeaconState {
        s
    }

    

    /** Retrieve validator index from a public key.  */
    function method getValidatorIndexFromPubKey( s : BeaconState, p : BLSPubkey ) : Option<nat> 

        ensures 
            (   exists i :: 0 <= i < |s.validators| && (s.validators[i].pubkey == p) &&                   getValidatorIndexFromPubKey(s,p) == Some(i)  && 
                        s.validators[i].pubkey == p
            )
            || 
            getValidatorIndexFromPubKey(s,p) == None


    
      

    /**
     *  Process a deposit.
     *
     *  The balance of the validator that made the deposit is updated. 
     *  If the validator is already known in `s` balance is updated, 
     *  otherwise the validator is appended to the validators' list with
     *  balance given by the deposit.
     */
    method process_deposit( s : BeaconState, d : Deposit ) returns ( s' : BeaconState ) 

    //  In the spec, the amount is rounded down to nearest multiple of eff. bal. inc.
    //  We require the amount to be a multiple of the increment.
    requires d.data.amount % EFFECTIVE_BALANCE_INCREMENT == 0
    requires |s.validators| == |s.balances|
    //  The updated index must be a uint64 and not overflow
    requires 0 <= s.eth1_deposit_index < 0x1000000000000000 - 1
    //  Sizes of these should be preserved.
    ensures |s'.validators| == |s'.balances| 

    //  Following is not part of the Python/K specs.
    // ensures match getValidatorIndexFromPubKey(s, d.data.pubkey) {
    //     case None => 
    //             s'.validators == s.validators + [Validator(d.data.pubkey, min(d.data.amount,MAX_EFFECTIVE_BALANCE))] &&
    //             s'.balances == s.balances + [min(d.data.amount,MAX_EFFECTIVE_BALANCE)]

    //     case Some(i) => 
    //             0 <= i < |s.validators| &&
    //             |s'.validators| == |s.validators| &&
    //             |s'.balances| == |s.balances| &&
    //             s'.validators == s.validators[i := Validator(s.validators[i].pubkey, min(s.balances[i] + d.data.amount,MAX_EFFECTIVE_BALANCE))] &&
    //             s'.balances == s.balances[i := min(s.balances[i] + d.data.amount, MAX_EFFECTIVE_BALANCE)]
    //     }

    {
        //FIXME: should be hash_tree_root(d.data)
        var htrdata : Hash := ""; 
    var r := is_valid_merkle_branch(
        htrdata,
        d.proof,
        DEPOSIT_CONTRACT_TREE_DEPTH + 1,
        s.eth1_deposit_index,
        s.eth1_data.deposit_root
    );
    // assert (r);
    //  Find the index i of the validator from its pubkey
    match getValidatorIndexFromPubKey(s, d.data.pubkey)  {
        case None => 
            //  Not found, Create and append validator
            var newBalance := min(d.data.amount,MAX_EFFECTIVE_BALANCE);
            s' := BeaconState(
            s.validators + [Validator(d.data.pubkey, newBalance)],
            s.eth1_data,
            s.eth1_deposit_index + 1,
            s.balances + [min(d.data.amount,MAX_EFFECTIVE_BALANCE)]);
        case Some(i) => 
            //  Found art index i, Update the balance at index i
            var newBalance := min(s.balances[i] + d.data.amount, MAX_EFFECTIVE_BALANCE);
            s':= BeaconState(
            s.validators[i := Validator(s.validators[i].pubkey,newBalance)],
            s.eth1_data,
            s.eth1_deposit_index,
            // s.validators,
            s.balances[i  := newBalance]);
        }
    } 
}