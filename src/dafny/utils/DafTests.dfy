/*
 * Copyright 2020 ConsenSys AG.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 */

/**
*  Provide testing framework for Dafny code
*
*/
module DafTest {

    /** Enum type for test results. */
    datatype TestResult = Pass | Fail

    /** A test case.
     *    
     *  @param  name    The textual description of the test.
     *  @param  code    A function literal from unit to bool.
     *
     *  @example: 
     *  TestItem("Double 2 * 4 is 8", () => 2 * 4 == 8)
     *  TestItem("An example using a function to compute result", () => f())
     *      where f returns a bool.
     */
    datatype TestItem = TestItem(name: string, code: () -> bool)

    datatype TestSuite = TestSuite(name: string, testCases : seq<TestItem>)
    
    /** An assertEqual operator. 
     *
     *  @tparam T   A type that supports equality.
     *  @param  f   A function from unit to T.
     *  @param  g   A function from unit to T.
     *
     *  @returns    The result of the test f() == g().
     */
    method assertEqual<T(==)>( f : () -> T, g : () -> T) returns (res:TestResult) {
        if ( f() == g() ) {
            return Pass;
        } else {
            return Fail;
        }
    } 

    /**
     *  Build a `TesResult` for a test.
     *  
     *  @param  t   A test case.
     *  @returns    Pass if t() evaluates to true and Fail otherwise.
     */
    function method runTest(t:   () -> bool) : TestResult {
        if ( t() ) then 
            Pass
        else
            Fail
    }

    /**
     *  Execute a sequence of test cases and summarise results.
     *
     *  @param  xl  A sequewnce of test cases.
     *  @param  s   Previous number of successful (Pass) test cases.
     *  @param  f   Previous number of failures (Fail) test cases.
     *  @returns    unit, side effects is to execute and print test results.
     */
    method {:tailrecursion true} executeRecTests(
            xl : seq<TestItem>, 
            s: nat, 
            f: nat
    ) returns () 
        decreases xl
    {
        if (|xl| == 0) {
            if ( f >= 1) {
                print "-- Results: \u001b[31mPassed [", s, "/", (s + f), "] Failed [", f, "/", (s + f), "]\u001b[0m\n";
            } else {
                print "-- Results: \u001b[32mPassed [", s, "/", (s + f), "] Failed [", f, "/", (s + f), "]\u001b[0m\n";
            }
            
        } else {
            var res := runTest(xl[0].code);
            match res {
                case Pass => 
                    print "\u001b[32m[", "Passed", "]\u001b[0m ", xl[0].name, "\n";
                    executeRecTests(xl[1..], s + 1, f);
                case Fail => 
                    print "\u001b[31m[", "Failed", "]\u001b[0m ", xl[0].name, "\n";
                    executeRecTests(xl[1..], s, f + 1);
            }
        }
    } 

    /**
     *  Execute a sequence of tests.
     *
     *  @param  xt  A sequence of test cases.
     *  @returns    Print out the tets results and summary.
     */
    method executeTests(xt : TestSuite) {
        print "-- ", "Test suite:", xt.name, " --\n";
        executeRecTests(xt.testCases, 0, 0);
    }
}
 