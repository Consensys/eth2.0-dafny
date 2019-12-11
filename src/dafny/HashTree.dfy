
include "Constants.dfy"

module HashTree {

    //  Import the constants declarations
    import opened Eth2Constants

    const BYTES_PER_CHUNK := 32;
    const BYTES_PER_LENGTH_OFFSET := 4 ;
    const BITS_PER_BYTE := 8 ;

    /* Compute the sha256 
    Takes a String and returns a 64-character hex-encoded string of the 32-byte SHA2-256 hash of the string.
Input `String` is interpreted as byte array, e.g. it is NOT hex-encoded.
*/
    
    /**
     *  Extract something from the current configuration which is a BeaconState. 
     */
    // function hash_tree_root_state

    


}