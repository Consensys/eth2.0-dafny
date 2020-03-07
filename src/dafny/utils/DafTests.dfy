/**
*  Provide testing framework for Dafny code
*
*/
module DafTest {

    /** Enum type for test results. */
    datatype TestResult = Pass | Fail

    function method displayRes(x : TestResult) : string 
    {
        //  coloring does not work ...
        // match x 
        //     case Pass =>  "\\033[31mPassed\\033[0m"
        //     case Fail =>  "\\033[31mFailed\\033[31m"
        match x 
            case Pass =>  "Passed"
            case Fail =>  "Failed"
    }

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
            //  print summary
            // print "--", "Test suite:", testSuiteName, "\n";
            print "-- Results:  Pass [", s, "/", (s + f), "] Failed [", f, "/", (s + f), "]\n";
        } else {
            var res := runTest(xl[0].code);
            print xl[0].name, " [", displayRes(res), "]\n";
            match res {
                case Pass => executeRecTests(xl[1..], s + 1, f);
                case Fail => executeRecTests(xl[1..], s, f + 1);
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
 