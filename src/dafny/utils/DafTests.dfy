

/**
*  Provide testing framework.
*
*/
module test {

    datatype TestResult = Pass | Fail

    datatype TestItem = TestItem(name: string, code: () -> bool)

    method assertEqual<T(==)>( f : () -> T, g : () -> T) returns (res:TestResult) {
        if ( f() == g() ) {
            return Pass;
        } else {
            return Fail;
        }
    } 

    function method runTest(t:   () -> bool) : TestResult {
        if ( t() ) then 
            Pass
        else
            Fail
    }

    method {:tailrecursion true} executeRecTests(
            xl : seq<TestItem>, 
            s: nat, 
            f: nat) returns () 
        decreases xl
    {
        if (|xl| == 0) {
            //  print summary
            print "Test suite: Pass [", s, "/", (s + f), "] Failed [", f, "/", (s + f), "]\n";
        } else {
            var res := runTest(xl[0].code);
            print "result of ", xl[0].name, " :", res, "\n";
            match res {
                case Pass => executeRecTests(xl[1..], s + 1, f);
                case Fail => executeRecTests(xl[1..], s, f + 1);
            }
        }
    } 

    method executeTests(xt : seq<TestItem>) {
        executeRecTests(xt, 0, 0);
    }
}
 