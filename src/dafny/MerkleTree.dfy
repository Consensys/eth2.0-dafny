include "Types.dfy"


module MerkleTree {

    import opened Eth2Types

    /** TODO: write the real code for this function. */
    function merkleize_chunks(xb : seq<Bytes>) : Hash {
        if xb == [] then
            zeroHashes(0)
        else 
            zeroHashes(1)
    }

    /** Returns a hash of an int. */
    function zeroHashes (i : int) : Hash 


}