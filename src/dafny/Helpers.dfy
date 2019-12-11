

/**  
  *  Takes a String and returns a 64-character hex-encoded string of the * 32-byte SHA2-256 hash of the string.
  * Input `String` is interpreted as byte array, e.g. it is NOT hex-encoded.
  */
  /* function sha256
  syntax String ::= Sha256 ( String )                                 [function, hook(KRYPTO.sha256)]
  */

  /*
    1. define helpers and export sets to make it cleaner
    2. define uint_nn
    3. start with modules implemetation, later try to use abstract mod

  */

  /* 
    syntax in K: grammar in BNF, similar to rats, attributes for associativity and so on.
    semantic rules in K: evaluation: strict => evaluate arguments first, 
    KResult is a builtin rule.

    stuff below 
     // Type conversion functions
  //====================================================
  some of it need not be implemented ... I guess ...

  1. figure out what beacon chain is supposed to
  2. try to find out the main entry point
  3. refine ...

  */