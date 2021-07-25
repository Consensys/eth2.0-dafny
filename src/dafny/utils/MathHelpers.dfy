/*
 * Copyright 2020 ConsenSys Software Inc.
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

    /** 
     *  Get the minimum of 2 natural numbers. 
     *
     *  @param  a   A natural number. 
     *  @param  b   A natural number. 
     *  @return     a if a < b, else b.
     */
    function method min(a: nat, b: nat): nat
    {
        if a < b then a else b
    }

    /** Get the maximum of 2 natural numbers.
     *
     *  @param  a   A natural number. 
     *  @param  b   A natural number. 
     *  @return     a if a > b, else b. 
     */
    function method max(a: nat, b: nat): nat
    {
        if a > b then a else b
    }  

    /** Get a sequence of natural numbers [start, start+1, ..., end-1].
     *
     *  @param  start   A natural number. 
     *  @param  end     A natural number. 
     *  @return         A sequence [start, start+1, ..., end-1]. 
     */
    function method range(start: nat, end: nat): seq<nat>
        requires end >= start
        ensures |range(start,end)| == (end - start) 
        ensures forall i :: 0 <= i < |range(start,end)| ==> start <= range(start,end)[i] < end
        decreases end - start
    {
        if (end - start) == 0 then []
        else [start] + range(start+1, end)
    }

    /** 
     *  Define 2^n. 
     *
     *  @param  n   A natural number. 
     *  @return     2^n.
     */
    function power2(n : nat): nat 
        ensures power2(n) >= 1
        ensures n >= 1 ==> power2(n) >= 2 

        decreases n
    {
        if n == 0 then 1 else 2 * power2(n - 1)
    }

    /** 
     *  Get the next power of two.
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
     *  Prove get_next_power_of_two(n) returns a power of 2.
     *
     *  @param  n   A positive integer. 
     *  @return     A proof that get_next_power_of_two(n) == power2(k).
     */
    lemma {:induction n} getNextPow2isPower2(n: nat)
        ensures exists k : nat {:induction k}  ::  get_next_power_of_two(n) == power2(k) 
    {
        if n <= 1 {
            assert(get_next_power_of_two(n) == power2(0)) ;
        } else {
            //  Induction on (n + 1)/2
            var k: nat :| get_next_power_of_two( (n + 1) / 2) == power2(k) ;
            calc == {
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

    /** 
     *  Get the previous power of two.
     *
     *  @param  n   A positive integer. 
     *  @return     The largest power of 2 that is smaller or equal to n.
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
     *  Prove get_prev_power_of_two(n) returns a power of 2.
     *
     *  @param  n   A positive integer. 
     *  @return     A proof that get_prev_power_of_two(n) == power2(k).
     */
    lemma {:induction n} getPrevPow2isPower2(n: nat)
        requires n > 0
        ensures exists k:nat  {:induction k} ::  get_prev_power_of_two(n) == power2(k) 
    {
        if n <= 1 {
            assert(get_prev_power_of_two(n) == power2(0)) ;
        } else {
            //  Induction on n / 2
            var k: nat :| get_prev_power_of_two( n / 2 ) == power2(k) ;
            calc == {
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
     *
     *  @param  n   A positive integer. 
     *  @return     A proof that power2(n + 1) >= n.
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
     *
     *  @param  n   A positive integer. 
     *  @param  k   A positive integer.
     *  @return     A proof that power2( n + k ) == power2(n) * power2(k).
     */
    lemma {:induction n, k} productRulePower2(n: nat, k : nat)
        ensures power2( n + k ) == power2(n) * power2(k) 
    {
        if k == 0 {
            //  Dafny can figure it out
        } else {
            calc {:induction k} == {
                power2( n + k );
                == 
                2 * power2( n + (k - 1) );
                == calc == {
                        power2( n + (k - 1) );
                        power2(n) * power2(k - 1);
                    }
                2 * power2(n) * power2(k - 1);
                //  And Dafny can work out the simplifications
            }
        }
    }

    /**
     *  Lower bound on the power of an even number.
     *
     *  @param  n   A positive integer. 
     *  @return     A proof that for n >= 1 that power2( 2 * n ) >= 2 * power2(n).
     */
    lemma {:induction n} lowerBoundPowerOfEvenNumber(n: nat) 
        requires n >= 1
        ensures power2( 2 * n ) >= 2 * power2(n)
    {
            calc == {
                power2( 2 * n );
                == calc == { 
                    2 * n == n + n ;
                } 
                power2(n + n);
                == { productRulePower2(n, n) ;}
                power2(n) * power2(n);
                >=    // power2(n) >= 2 for n >= 1
                2 * power2(n);
            }  
    }

    /** 
     *  Test if n is a power of 2. 
     *
     *  @param  n   A positive integer. 
     *  @return     True if n is a power of 2 else false.
     */
    predicate isPowerOf2(n: nat)
    {
        exists k:nat {:induction k}:: power2(k)==n 
        // alternative methods:
        //(n == get_next_power_of_two(n))
        //x > 0 && ( x == 1 || ((x % 2 == 0) && isPowerOf2(x/2)) )
    }

    /**     
     *  The get_next_power_of_two is idempotent. 
     *
     *  @param  n   A positive integer. 
     *  @return     A proof that get_next_power_of_two is idempotent.
     */
    lemma {:induction n} getNextPow2isIdempotent(n: nat)
        ensures get_next_power_of_two(get_next_power_of_two(n)) == get_next_power_of_two(n)
    {   //Thanks Dafny
    }

    /**     
     *  Show get_next_power_of_two(n) is at least n. 
     *
     *  @param  n   A positive integer. 
     *  @return     A proof that get_next_power_of_two(n) is at least n.
     */
    lemma {:induction n} getNextPow2LowerBound(n: nat)
        ensures n <= get_next_power_of_two(n)
    {   // Thanks Dafny
    }

    /**     
     *  Show get_next_power_of_two(n) is gives a power of 2. 
     *
     *  @param  n   A positive integer. 
     *  @return     A proof that get_next_power_of_two(n) is gives a power of 2.
     */
    lemma {:induction n} nextPow2IsPow2(n: nat)
        ensures isPowerOf2(get_next_power_of_two(n))
    {
        if n <= 1 {
            assert(get_next_power_of_two(n) == power2(0)) ;
        } else {
            //  Induction on (n + 1)/2
            var k: nat :| get_next_power_of_two( (n + 1) / 2) == power2(k) ;
            calc == {
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

    /**     
     *  Show that if n > 1 and n is a power of 2 then n/2 is also a power of 2. 
     *
     *  @param  n   A positive integer. 
     *  @return     A proof that if n > 1 and n is a power of 2 
     *              then n/2 is also a power of 2.
     */
    lemma halfPow2IsPow2(n: nat)
        requires n > 1
        requires isPowerOf2(n)
        ensures isPowerOf2(n/2)
    {
        var k:nat :| power2(k)==n ;
        assert(n>=2);
        assert(k>=1);
        calc == {   //  following terms are equal
            isPowerOf2(n/2); 
            isPowerOf2(power2(k)/2); 
            isPowerOf2(power2(k-1)); 
        }
    }

    /**     
     *  Show that if b => 1 then integer division of a by b is equivalent to
     *  the floor of a/b. 
     *
     *  @param  a   A positive integer. 
     *  @param  b   A positive integer. 
     *  @return     A proof that if b => 1 then integer division of a by b is 
     *              equivalent to (a as real / b as real).Floor.
     */
    lemma NatDivision(a: nat, b: nat)
        requires b != 0
        ensures a / b == (a as real / b as real).Floor
    {
        assert a == (a / b) * b + (a % b);

        assert a as real == (a / b) as real * b as real + (a % b) as real;

        assert (a % b) as real / b as real < b as real;
        assert a as real / b as real == (a / b) as real + (a % b) as real / b as real;
        assert (a % b) < b;
        assert (a % b) as real / b as real < 1 as real;
    }

    /**
     *  A simple lemma to bound integer division when divisor >= 1.
     *
     *  @param  x   A positive integer. 
     *  @param  k   A positive integer. 
     *  @return     A proof that if k >= 1 then x/k has lower bound 0 and upper bound x.
     */
    lemma divLess(x : nat , k : nat) 
        requires k >= 1
        ensures 0 <= x / k <= x 
    {   
        if k == 1 {
            assert x / k == x;
        }
        else {
            assert k > 1;
            NatDivision(x, k);
            assert x / k <= x;
        }
    }

    /**
     *  ( x  /  k ) * k is less than or equal to x.
     *
     *  @param  x   A positive integer. 
     *  @param  k   A positive integer. 
     *  @return     A proof that if k >= 1 then (x/k)*k has an upper bound x.
     */
    lemma div2(x : nat, k : nat) 
        requires k >= 1 
        ensures ( x / k ) * k <= x
    {   //  Thanks Dafny
    }

    /**
     *  If a is a uint64, c > 0 and b <= c then ( a  /  b ) * c is a uint64.
     *
     *  @param  a   A positive integer. 
     *  @param  b   A positive integer. 
     *  @param  c   A positive integer. 
     *  @return     A proof that if a is a uint64, c > 0 and b <= c then 
     *              ( a  /  b ) * c is a uint64.
     */
    lemma divHelper(a: nat, b: nat, c: nat)
        requires a < 0x10000000000000000
        requires c > 0
        requires b <= c
        ensures a * b / c < 0x10000000000000000
    {
        assert a * b <= a * c;
    }

    /**
     *  If a is a uint64, c > 0 and b <= c then ( a  /  b ) * c <= a>.
     *
     *  @param  a   A positive integer. 
     *  @param  b   A positive integer. 
     *  @param  c   A positive integer. 
     *  @return     A proof that if a is a uint64, c > 0 and b <= c then 
     *              ( a  /  b ) * c <= a.
     */
    lemma divHelper2(a: nat, b: nat, c: nat)
        requires a < 0x10000000000000000
        requires c > 0
        requires b <= c
        ensures a * b / c <= a
    {
        assert (a * b / c) * c <= a * c;
        assert a * b <= a * c;
    }

    /**
     *  Expansion of a * (b + 1).
     *
     *  @param  a   A positive integer. 
     *  @param  b   A positive integer. 
     *  @return     A proof that a * (b + 1) == a * b + a.
     */
    lemma natExpansion(a: nat, b: nat)
        ensures a * (b + 1) == a * b + a 
    { // Thanks Dafny
    }

    /**
     *   a - b >= c implies a/c > b/c
     *
     *  @param  a   A positive integer. 
     *  @param  b   A positive integer. 
     *  @param  c   A positive integer. 
     *  @return     A proof that if c > 0 then a - b >= c ==> a/c > b/c.
     */
    lemma natRatioRule(a: nat, b: nat, c: nat)
        requires c > 0
        ensures a - b >= c ==> a/c > b/c 
    { // Thanks Dafny
    }

    /**
     *  a/c >= b/c
     *
     *  @param  a   A positive integer. 
     *  @param  b   A positive integer. 
     *  @param  c   A positive integer. 
     *  @return     A proof that if c > 0and a >= b then a/c >= b/c.
     */
    lemma commonDivRule(a: nat, b: nat, c: nat)
        requires c > 0
        requires a >= b
        ensures a/c >= b/c
    {
        if a == b { // Thanks Dafny
        }
        else {
            assert a > b;
            var i : nat :| a == b + i;
            assert i > 0;
            NatDivision(a,c);
            assert a / c == (a as real / c as real).Floor;
            NatDivision(b,c);
            assert b / c == (b as real / c as real).Floor;
            assert a as real / c as real > b as real / c as real;
        }
    }




}