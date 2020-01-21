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

    /** Compute 2^n. */
    function power2(n : nat): nat 
    ensures power2(n) >= 1
        {
            if n == 0 then 1 else 2 * power2(n - 1)
        }

    /** get_next_power_of_two returns a power of 2. */
    lemma lem4(n: nat)
    ensures exists k:nat :: get_next_power_of_two(n) == power2(k) {
        if n <= 1 {
            //  Dafny figures it out.
            assert(get_next_power_of_two(n) == power2(0)) ;
        } else {
            var k: nat :| get_next_power_of_two( (n + 1) / 2) == power2(k) ;
            calc {
                get_next_power_of_two(n);
                2 * get_next_power_of_two( (n + 1) / 2);
                2 * power2(k) ;
                power2(k + 1);
            }
        }
    }

    /** Get the next power of two.
     *
     *  @param  n   A positive integer. 
     *  @return     The smallest power of 2 that is larger than n.
     */
    function get_next_power_of_two(n : nat) : nat 
    ensures get_next_power_of_two(n) >= 1
    ensures get_next_power_of_two(n) >= n
    ensures n >= 1 ==> (get_next_power_of_two(n) / 2) < n
        {
        if n <= 1 then 1
        // else if n <= 2 then n
        else 2 * get_next_power_of_two( (n + 1) / 2)
        }
    
     /** Get the previous power of two.
     *
     *  @param  n   A positive integer. 
     *  @return     The largest power of 2 that is larger than n.
     */
    function get_prev_power_of_two(n : nat) : nat 
    ensures get_prev_power_of_two(n) >= 1
    ensures get_prev_power_of_two(n) <= n
    ensures n >= 1 ==> (get_prev_power_of_two(n) / 2) < n
        {
        if n <= 1 then 1
        // else if n <= 2 then n
        else 2 * get_prev_power_of_two( n / 2)
        }

    /** Some desirable properties of get_next_power_of_two.  */
    lemma lem1(n: nat) 
    ensures get_next_power_of_two(0) == 1 
    ensures get_next_power_of_two(1) == 1 
    ensures get_next_power_of_two(2) == 2 
    ensures get_next_power_of_two(3) == 4 
    ensures get_next_power_of_two(8) == 8 
    ensures get_next_power_of_two(15) == 16
    ensures get_next_power_of_two(121) == 128
        {
        }
        
    /** Arithmetic 1. */
    lemma la(n: nat) 
    requires n >= 2;
    ensures 2 * (n - 1) >= n 
        {
        /* n >=2 && 2 * n - 2 >= n <==> n >= 2 && n - 2 >= 0 <==> true */
        }

    /** Power of two is monotonic. */
    lemma power2_monotonic(n: nat, n': nat) 
    requires n > n'
    ensures n > n' ==> power2(n) > power2(n') 
        {
        } 

    /** Lower bound for power2. */
    lemma lowerBoundPower2(n : nat) 
    ensures power2(n + 1) >= n 
        {
            if n <= 1 {
                //  Dafny can infer the proof
            } else {
                calc >= {
                    power2(n + 1) ; 
                    //  Use definition of pwer2(n), n >= 1
                    2 * power2(n)  ;
                        { lowerBoundPower2(n - 1); }
                    2 * (n - 1);
                        { la(n) ;}  //  not necessary
                }
            }
        }

    lemma rule3(n: nat, k : nat)
    ensures power2( n + k ) == power2(n) * power2(k) 
        {
            if k == 0 {
                //  Dafny can figure it out
            } else {
                calc {:induction k} {
                    power2( n + k );
                    2 * power2( n + (k - 1) );
                        calc {
                            power2( n + (k - 1) );
                            power2(n) * power2(k - 1);
                        }
                    2 * power2(n) * power2(k - 1);
                    //  And Dafny can work out the simplifications
                }
            }
        }

    lemma rule4(n : nat)
    requires n >= 1 
    ensures power2(n) >= 2 
        {
            // Dafny can guess the proof.
        }

    lemma rule2(n: nat) 
    requires n >= 1
    ensures power2( 2 * n ) >= 2 * power2(n)
        {
                calc {
                    power2( 2 * n );
                        calc { 2 * n == n + n ;} 
                    power2(n + n);
                        { rule3(n, n) ;}
                    power2(n) * power2(n);
                        >= { rule4(n) ;}
                    2 * power2(n);
                }  
        }

    /** get_next_power_of_two(x) = i, then x < 2^i */
    lemma lem2(n: nat) 
    ensures power2(get_next_power_of_two(n)) > n
        {
            if n <= 2 { 
                //  Proof can be infered by Dafny
            }  
            else { 
                calc {
                    power2(get_next_power_of_two(n));
                        //  Rewrite the def.
                    power2(2 * get_next_power_of_two((n + 1) / 2)) ;
                        >= { rule2( get_next_power_of_two((n + 1) / 2)) ; }
                    2 * power2(get_next_power_of_two((n + 1) / 2))  ;
                        //  Use the induction hypothesis on (n + 1) / 2 that Dafny implicitly creates
                        > 
                    2 * (n + 1) / 2;
                        >= 
                    n ;
                }
            }
        }

    // lemma lem3(n: nat) 
    // requires n >= 1 
    // ensures (get_next_power_of_two(n) / 2) < n {
    //         // if n == 0 {
    //         //     //  Dafny figures it out.
    //         // }
    //         // else {

    //         // }
    //     }

    // lemma foo(n: nat)
    //     ensures n >= 4 {}
}
