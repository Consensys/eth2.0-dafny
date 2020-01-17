include "Types.dfy"

module Helpers {

  import opened Eth2Types
  
  /** Minimum of two Gwei values. */
  function method min(x : Gwei, y : Gwei) : Gwei {
      if x <= y then x else y
  } 
}