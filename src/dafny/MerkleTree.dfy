include "Types.dfy"
include "NativeTypes.dfy"


module MerkleTree {

    import opened Eth2Types
    import opened Native__NativeTypes_s

    /** TODO: write the real code for this function. */
    function merkleize_chunks(xb : seq<Bytes>) : Hash {
        if xb == [] then
            zeroHashes(0)
        else 
            zeroHashes(1)
    }

    /** Returns a hash of an int. */
    function zeroHashes (i : int) : Hash 

    /** 
     *  Marshals a value and packs its serialized bytes into leaves of a 
     *  Merkle trie. It then determines the root of this trie.
     */
     function hash_tree_root() : Option<array<byte>>



}

/**
    Merkle tree:  binary tree with hashes
    Usage: client has a root hash, and wants to verify that a Tx is in the tree.
    Server will provide a proof: hashes in the neighbourhood of the Tx. 
    Client re-hashes and check that it is equal to its own root hash.

 */