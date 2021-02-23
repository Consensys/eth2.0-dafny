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

include "../../../libraries/integers/div_nonlinear.i.dfy"
include "../../../libraries/integers/div_auto.i.dfy"
include "../../../libraries/integers/div.i.dfy"
include "../../../libraries/integers/mul.i.dfy"
include "../../../libraries/integers/power.i.dfy"
include "../../../libraries/integers/powers.i.dfy"
include "../../../libraries/reals/div.r.dfy"
include "../../../libraries/reals/mul.r.dfy"

module MathHelperLemmas {
    import opened Math__div_nonlinear_i
    import opened Math__div_auto_i
    import opened Math__div_i
    import opened Math__power_i
    import opened Math__power_s
    import opened MathDivR
    import opened MathMulR

    export MathHelperLemmas provides LemmaYStrictlyLessThanXIff, 
                                     LemmaSquareYPlusOneGreaterThanX, 
                                     LemmaMaxForYDivByX,
                                     Math__power_s


    lemma LemmaYStrictlyLessThanXIff(x:nat,n:nat)
    requires x > 0
    ensures  var y:=(x+n/x)/2 ; power(x,2) > n <==> y < x
    {
        reveal_power();
        if(x*x>n)
        {
            LemmaYNatStrictlyLessThanX(x,n);
        }
        else
        {
            LemmaYNatGreaterThanX(x,n);
        }
    }

    lemma LemmaSquareYPlusOneGreaterThanX(x:nat,n:nat)
    requires x > 0
    requires power(x+1,2)>n
    ensures var y:= (x+n/x)/2; power(y+1,2) > n 
    {
        reveal_power();
        var y:= NextYNat(x,n);
        if(x*x>n)
        {
            LemmaYNatStrictlyLargerThanN(x as nat,n as nat);
        }
        else // 0 < x*x < n
        {
            var d :| n == x*x + d;
            calc {
                (y+1)*(y+1);
                >= {
                    calc {
                        y;
                        ==
                        (x+n/x)/2;
                        >= calc {
                            n/x;
                            ==
                            (x*x + d)/x;
                            == {
                                calc == {
                                    x*x % x;
                                    (x*x + 0) % x;
                                    {lemma_mod_multiples_vanish(x,0,x);}
                                    0 % x;
                                        {lemma_mod_of_zero_is_zero(x);}
                                    0;
                                }
                                lemma_div_auto(x);
                            }
                            x*x/x + d/x;
                            == calc == {
                                x*x/x;
                                    {lemma_fundamental_div_mod_converse(x*x,x,x,0);}
                                x;
                            }
                            x + d/x;
                            >= calc >= {
                                d/x;
                                0;
                            }
                            x;
                        }
                        x;
                    }
                    lemma_power_increases(x + 1,y+1,2);
                    lemma_square_is_power_2(x+1);
                    lemma_square_is_power_2(y+1);
                }
                (x+1) * (x+1);
                >
                n;
            }
        }
    }    

    /**
     * Value of the `y` variable as calculated by a `while` loop of the
     * `integer_squareroot` method.
     *
     * This function is used in the specification of all the lemmas expect for
     * those exported as this would require exporting this function as well
     * which would unnecessary pollute the namespace where the moduel is
     * imported
     *
     */
    function NextYNat(x:nat,n:nat):nat
    requires x>0;
    {
        (x+n/x)/2
    }

    /**
     * Value of the `y` variable as calculated by a `while` loop of the
     * `integer_squareroot` method using real numbers rather than natural
     * numbers.
     *
     */
    function NextYReal(x:real,n:real):real
    requires x > 0.0;
    requires n >= 0.0;
    ensures NextYReal(x,n) >= 0.0;
    {
        (x+n/x)/2.0
    }      

    lemma  LemmaYNatStrictlyLessThanX(x:nat, n:nat)
    requires n>=0;
    requires x * x > n;
    ensures  NextYNat(x,n) < x;
    {
        var t:= x*x -n ;

        calc
        {
            (x+n/x)/2; 
            ==
            (x+(x*x - t)/x)/2; 
            <= {
                lemma_div_auto(x);
                lemma_fundamental_div_mod_converse(x*x,x,x,0);
                if(t%x > 0)
                {
                    assert (x*x - t)/x ==  x*x/x - t/x-1;
                }
               }
            (x + x*x/x -1)/2;
            == {lemma_fundamental_div_mod_converse(x*x,x,x,0);}
            (2*x -1)/2;
            == {lemma_div_auto(2);}
            2*x/2 - 1/2 -1 ;
            ==
            x - 1/2 -1;
            < x;
        }
    }


    lemma LemmaYNatGreaterThanX(x:nat,n:nat)
    requires x> 0
    requires x*x<=n;
    ensures  NextYNat(x,n) >=x
    {
        var t :|  n == t + x*x;

        calc {
            NextYNat(x,n);
            ==
            (x + (t + x*x)/x)/2;
            == calc {
                (t + x*x)/x;
                    {   assert (x*x)%x == 0 by {lemma_fundamental_div_mod_converse(x*x,x,x,0);}
                        lemma_div_auto(x);
                    }
                t/x + (x*x)/x;
                    {lemma_fundamental_div_mod_converse(x*x,x,x,0);}
                t/x + x;
            }
            (2*x + t/x)/2;
            >= {lemma_div_auto(x);}
            x; 
        }
    }   


    lemma LemmaMaxForYDivByX(y:nat,n:nat)
    requires y > 0;
    requires (y+1)*(y+1) > n;
    ensures y + 3 >=n/y;
    {

        calc ==> {
            (y+1)*(y+1) > n;
              calc == {
                (y+1)*(y+1);
                y*y + 2*y + 1;
            }
            y*y + 2*y + 1 > n;
            y*(y + 2) + 1 > n;
            y*(y + 2)  > n - 1;
                {lemma_div_is_ordered(n - 1,y*(y + 2),y);}
            y*(y + 2)/y  >= (n - 1)/y;
                {lemma_fundamental_div_mod_converse(y*(y + 2),y,(y + 2),0);}
            y + 2  >= (n - 1)/y;
                {lemma_div_is_ordered(n - y,n-1,y);}
            y + 2 >= (n-y)/y;
                {lemma_div_auto(y);}
            y + 2 >= n/y - 1;
            y + 3 >= n/y;
        }
    }     


    lemma LemmaYNatStrictlyLargerThanN(x:nat,n:nat)
    requires x>0
    requires x*x > n;
    ensures (var y:=NextYNat(x,n); (y+1)*(y+1) > n)
    {
        var xr := x as real;
        var nr := n as real;
        var yr:real := NextYReal(xr, nr);
        var y:nat:= NextYNat(x,n);

        calc {
            (y+1)*(y+1) > n; 
            <==>
            (y + 1) as real  * (y + 1) as real > nr;
            <==> calc {
                (y + 1) as real  * (y + 1) as real;
                >= calc {
                    (y + 1) as real;
                    (NextYNat(x,n) + 1) as real;
                    >=  {LemmaYNatPlusOneGreaterThanYReal(x,n);}
                    yr;
                }
                yr * yr;
                > { assert xr * xr > nr;
                    LemmaYRealStrictlyLargerThanNReal(xr,nr);}
                nr;
            }
            true;
        }
    }

  
    /**
     * Helper function used by the lemma
     * `LemmaYNatPlusOneGreaterThanYReal`
     *
     */
    function ModNotZero(r:int,x:nat):nat
    requires x> 0
    ensures 0 <= ModNotZero(r,x) <= 1
    {
        if r%x > 0 then 1 else 0
    }

    lemma LemmaYNatPlusOneGreaterThanYReal(x:nat,n:nat)
    requires x>0
    requires x*x>n;
    ensures (NextYNat(x,n)+1) as real >= NextYReal(x as real, n as real)
    {
        var xr := x as real;
        var nr := n as real;
        var yr:real := NextYReal(xr, nr);

        
        var y:= NextYNat(x,n);

        var t :nat :| x * x == n + t;
        var k:= t/x;
        var r:= t%x;        

        var tr := t as real;
        var kr := k as real;
        var rr := r as real;

        calc >= {
            (y + 1) as real;
            ==  calc ==  {
                y;
                (x + n/x)/2;
                (x + (x*x - x*k -r)/x)/2;
                (x + (x*(x-k)-r)/x)/2;
                == calc {
                    (x*(x-k)-r)/x; 
                    ==  {
                        lemma_div_auto(x);
                        assert (x*(x-k)) % x ==0 by {lemma_fundamental_div_mod_converse(x*(x-k),x,x-k,0);}
                        if(r%x >0)
                        {
                            calc == {
                                (x*(x-k)-r)/x;
                                x*(x-k)/x -r/x -1;
                                x*(x-k)/x -r/x - ModNotZero(r,x);
                            }
                        }
                        else
                        {
                            calc == {
                                (x*(x-k)-r)/x;
                                x*(x-k)/x -r/x;
                                x*(x-k)/x -r/x - ModNotZero(r,x);
                            }
                        }
                    }
                    x*(x-k)/x -r/x - ModNotZero(r,x);
                }
                (x + x*(x-k)/x - r/x-ModNotZero(r,x))/2;
                    {lemma_fundamental_div_mod_converse(x*(x-k),x,x-k,0);}
                (x + x -k -r/x-ModNotZero(r,x))/2;
                (2*x -k - r/x -ModNotZero(r,x))/2;
                (2*x -k - (r/x) -ModNotZero(r,x))/2;
                == calc {
                    r/x;
                        {
                            assert 0<= r < x;
                            LemmaSmallDivNotForall(r,x);
                        }
                    0;
                }
                (2*x -k  - ModNotZero(r,x))/2;
                (2 *x -(k+ModNotZero(r,x)))/2;
                    {
                    lemma_div_auto(2);
                }
                x - (k+ModNotZero(r,x))/2 - ModNotZero(k+ModNotZero(r,x),2);
                x - ((k+ModNotZero(r,x))/2 + ModNotZero(k+ModNotZero(r,x),2));
            }
            (x - ((k+ModNotZero(r,x))/2 + ModNotZero(k+ModNotZero(r,x),2)) + 1) as real;
            >=  {
                if(r%x == 0)
                {
                    calc {
                         (k+ModNotZero(r,x))/2 + ModNotZero(k+ModNotZero(r,x),2);
                         ==
                         k/2 + ModNotZero(k,2);
                         <=
                         k/2 + 1;
                    }
                }
                else // ModNotZero(r,x)==1;
                {
                    if(k%2==0)
                    {
                        calc == {
                            (k+ModNotZero(r,x))/2 + ModNotZero(k+ModNotZero(r,x),2);
                            (k+1)/2 + ModNotZero(k+1,2);
                                { assert (k+1)/2 == k/2 && ModNotZero(k+1,2) == 1;}
                            k/2 + 1;
                        }
                    }
                    else // k%2 == 1
                    {
                        calc == {
                            (k+ModNotZero(r,x))/2 + ModNotZero(k+ModNotZero(r,x),2);
                            (k+1)/2 + ModNotZero(k+1,2);
                                { assert (k+1)/2 == (k/2 + 1) && ModNotZero(k+1,2) == 0;}
                            k/2 + 1;
                        }
                    }
                }
            }
            (x - k/2) as real;
            >= { assume rr/(xr * 2.0) >=0.0; }
            xr -kr/2.0 - rr/(xr * 2.0);   
            == calc == {
                yr;
                (xr + nr/xr)/2.0;
                == calc  <==> {
                    nr == xr*xr -tr;
                    n == x * x -t;
                    true;
                }
                (xr + ((xr*xr)-tr)/xr)/2.0;
                == calc <==> {
                    tr == xr*kr + rr;
                    t == x * k + r;
                        {lemma_fundamental_div_mod(t,x);}
                    true;
                }
                (xr + ((xr*xr)-xr*kr-rr)/xr)/2.0;
                    {assert ((xr*xr)-xr*kr-rr)/xr == (xr*xr)/xr-xr*kr/xr-rr/xr by {
                    calc == {
                        ((xr*xr)-xr*kr-rr)/xr;
                        (((xr*xr)-xr*kr)-rr)/xr;
                            {LemmaRealSubDistributeOverDiv((xr*xr)-xr*kr,rr,xr);}
                        ((xr*xr)-xr*kr)/xr-rr/xr;
                            {LemmaRealSubDistributeOverDiv(xr*xr,xr*kr,xr);}
                        (xr*xr)/xr-xr*kr/xr-rr/xr;
                    }
                }}
                (xr + (xr*xr)/xr-xr*kr/xr-rr/xr)/2.0;
                    calc {
                        xr*xr/xr;
                            {LemmaConverseRealDiv(xr*xr,xr,xr);}
                        xr;
                    }
                (xr + xr-xr*kr/xr-rr/xr)/2.0;
                    calc {
                        xr*kr/xr;
                            {LemmaConverseRealDiv(xr*kr,xr,kr);}
                        kr;
                    }
                (xr + xr -kr -rr/xr)/2.0;
                xr -kr/2.0 - rr/(xr * 2.0);
            }
            yr;         
        }
       
    }    

    lemma LemmaYRealStrictlyLargerThanNReal(x:real,n:real)
    requires n>=0.0;
    requires x>0.0
    requires x*x > n;
    ensures (var y:=NextYReal(x,n); y*y > n)
    {
        var y:=NextYReal(x,n);
        var t:=x*x -n;

        calc >
        {
            y*y;
            ==  calc == {
                y;
                (x + n/x)/2.0;
                (x + (x*x-t)/x)/2.0;
                (x + x -t/x)/2.0;
                (2.0*x - t/x)/2.0;
                x - t/(2.0*x);
            }
            x*x + t*t/(x*x*4.0) - 2.0*x *t/(2.0*x);
            ==
            x*x + t*t/(x*x*4.0) - t;
            > calc {
                (t*t/(x*x*4.0));
                > {LemmaRealMulStrictlyPositive(t,t);}
                0.0;
            } 
            x*x -t;
            ==
            n;
        }
    }
}