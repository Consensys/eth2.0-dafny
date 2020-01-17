include "Constants.dfy"
include "NativeTypes.dfy"
include "Types.dfy"

/**
 * Merkle trees.
 */
module Merkle {

    //  Import some constants and types
    import opened Native__NativeTypes_s
    import opened Eth2Types

    /** Check a Merkle proof. 
     *
     *  The check is: leaf at index should verify the Merkle root and branch
     *  
     *  @param  leaf    The element to check membership of.
     *  @param  branch  The branch (proof) of membership.
     *  @param  depth   ??
     *  @param  index   ??  
     *  @param  root    The root hash.
     */
    method is_valid_merkle_branch(
        leaf : Hash, 
        branch : array<Hash>, 
        depth : uint64, 
        index : uint64,
        root: Hash ) returns (b : bool)  {
            //  Start with the leaf
            var value := leaf;
            //  FIXME: Iterate computation of Merkle proof
            var i : uint64 := 0;
            while (i < depth) 
                {
                    //  FIXME
                    i := i + 1;
                }
            //  
            b := value == root ;
        } 
}