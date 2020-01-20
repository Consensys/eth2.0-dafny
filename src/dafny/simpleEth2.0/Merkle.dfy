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

    /** Compute 2^n.  */
    function power2(n : nat): nat 
    ensures power2(n) >= 1
    {
        if n == 0 then 1 else 2 * power2(n - 1)
    }

    /** Get the next power of two. */
    function get_next_power_of_two(n : nat) : nat 
    {
        if n == 0 then 0
        else if n <= 2 then n
        else 2 * get_next_power_of_two( (n + 1) / 2)
    }

    /** Some desirable properties of get_next_power_of_two.  */
    lemma lem1(n: nat) 
        ensures get_next_power_of_two(0) == 1 
        ensures get_next_power_of_two(1) == 1 
        ensures get_next_power_of_two(2) == 2 
        ensures get_next_power_of_two(3) == 2 
        ensures get_next_power_of_two(8) == 4 
        ensures get_next_power_of_two(15) == 5 
        
    /** Arithmetic 1. */
    lemma la(n: nat) 
        requires n >= 2;
        ensures 2 * (n - 1) >= n {
        }

    /** Power of two is monotonic. */
    lemma power2_monotonic(n: nat, n': nat) 
        requires n > n'
        ensures n > n' ==> power2(n) > power2(n') {

        }

    /** Lower bound for power2. */
    lemma lb(n : nat) 
        ensures power2(n + 1) >= n {
            if n <= 1 {
                //  Dafny can infer the proof
            } else {
                calc >= {
                    power2(n + 1) ; 
                    2 * power2(n)  ;
                        { lb(n - 1); }
                    2 * (n - 1);
                        { la(n) ;}  //  not necessary
                }
            }
        }

    /** Arithmetic equivalence. */
    lemma k1(x: int, y: int) 
        ensures x > y / 2 <==> 2 * x > y 

    /** get_next_power_of_two(x) = i, then x < 2^i */
    lemma lem2(n: nat) 
        ensures power2(get_next_power_of_two(n)) > n
        {
            if n <= 2 { 
                //  Proof can be infered by Dafny
            }  
            else { 
                calc {
                    get_next_power_of_two((n + 1)/2) > (n + 1)/2;
                        ==> { k1( get_next_power_of_two((n + 1)/2), n + 1); }
                    (2 * get_next_power_of_two((n + 1)/2)) > (n + 1);
                        ==> { power2_monotonic(2 * get_next_power_of_two((n + 1)/2), n + 1 ); } 
                    power2(2 * get_next_power_of_two((n + 1)/2)) > power2(n + 1); 
                        ==> { lb(n); }
                    power2(2 * get_next_power_of_two((n + 1)/2)) > n  ;
                        ==>
                    power2(get_next_power_of_two(n)) > n ;
                    true;
                } 
            }
        }
}
