/*
 * Copyright 2020 ConsenSys AG.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
 * License for the specific language governing permissions and limitations 
 * under the License.
 */

/**
 *  Useful arithmetic functions.
 */
module MathHelpers {

    /** Define 2^n. */
    function power2(n : nat): nat 
        ensures power2(n) >= 1
        ensures n >= 1 ==> power2(n) >= 2 

        decreases n
    {
        if n == 0 then 1 else 2 * power2(n - 1)
    }

    /** Get the next power of two.
     *
     *  @param  n   A positive integer. 
     *  @return     The smallest power of 2 that is larger or equal to n.
     */
    function method get_next_power_of_two(n : nat) : nat 
        requires true

        ensures get_next_power_of_two(n) >= 1
        ensures get_next_power_of_two(n) >= n 
        ensures n >= 1 ==> (get_next_power_of_two(n) / 2) < n

        decreases n
    {
        if n <= 1 then 1
        else 2 * get_next_power_of_two( (n + 1) / 2 )
    }
    
    /** 
     * get_next_power_of_two returns a power of 2. 
     */
    lemma {:induction n} getNextPow2isPower2(n: nat)
        ensures exists k : nat {:induction k}  ::  get_next_power_of_two(n) == power2(k) 
    {
        if n <= 1 {
            assert(get_next_power_of_two(n) == power2(0)) ;
        } else {
            //  Induction on (n + 1)/2
            var k: nat :| get_next_power_of_two( (n + 1) / 2) == power2(k) ;
            calc {
                get_next_power_of_two(n);
                ==  //  Definition of 
                2 * get_next_power_of_two( (n + 1) / 2);
                == //   Use Induction assumption in (n + 1)/2
                2 * power2(k);
                ==  //  Definition of
                power2(k + 1);
            }
        }
    }

    /** Get the previous power of two.
     *
     *  @param  n   A positive integer. 
     *  @return     The largest power of 2 that is smaller than n.
     */
    function method get_prev_power_of_two(n : nat) : nat 
        requires n > 0
        ensures 1 <= get_prev_power_of_two(n) <= n
        ensures 2 * get_prev_power_of_two(n) > n
        decreases n
    {
        if n <= 1 then 1
        else 2 * get_prev_power_of_two( n / 2)
    }

    /** 
     * get_prev_power_of_two returns a power of 2. 
     */
    lemma {:induction n} getPrevPow2isPower2(n: nat)
        requires n > 0
        ensures exists k:nat  ::  get_prev_power_of_two(n) == power2(k) 
    {
        if n <= 1 {
            assert(get_prev_power_of_two(n) == power2(0)) ;
        } else {
            //  Induction on n / 2
            var k: nat :| get_prev_power_of_two( n / 2 ) == power2(k) ;
            calc {
                get_prev_power_of_two(n);
                == //   Defintion of.
                2 * get_prev_power_of_two( n / 2 );
                == //   Use Induction assumption on n / 2 
                2 * power2(k) ;
                power2(k + 1);
            }
        }
    }
     
    /** 
     *  A lower bound for power2. 
     */
    lemma {:induction n} lowerBoundPower2(n : nat) 
        ensures power2(n + 1) >= n 
        decreases n
    {
        if n <= 1 {
            //  Thanks Dafny.
        } else {
            calc >= {
                power2(n + 1) ; 
                == //  Definition of
                2 * power2(n)  ;
                >=  { // Induction assumption on n - 1
                    lowerBoundPower2(n - 1); 
                }
                2 * (n - 1);
                //  and as 2 * (n - 1) >= n  for n >= 2, QED
            }
        }
    }

    /**
     *  Product rule for exponents applied to power of 2.
     *  2^{n + k} = 2^n x 2^k
     */
    lemma {:induction n, k} productRulePower2(n: nat, k : nat)
        ensures power2( n + k ) == power2(n) * power2(k) 
    {
        if k == 0 {
            //  Dafny can figure it out
        } else {
            calc {:induction k} {
                power2( n + k );
                == 
                2 * power2( n + (k - 1) );
                == calc {
                        power2( n + (k - 1) );
                        power2(n) * power2(k - 1);
                    }
                2 * power2(n) * power2(k - 1);
                //  And Dafny can work out the simplifications
            }
        }
    }

    lemma {:induction n} lowerBoundPowerOfEvenNumber(n: nat) 
        requires n >= 1
        ensures power2( 2 * n ) >= 2 * power2(n)
    {
            calc {
                power2( 2 * n );
                == calc { 
                    2 * n == n + n ;
                } 
                power2(n + n);
                == { productRulePower2(n, n) ;}
                power2(n) * power2(n);
                >=    // power2(n) >= 2 for n >= 1
                2 * power2(n);
            }  
    }
}