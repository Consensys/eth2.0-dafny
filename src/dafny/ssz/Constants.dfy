/*
 * Copyright 2021 ConsenSys Software Inc.
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
  * Define the constants used in the Eth2.0 spec.
  * constants-minimal.k in the K spec.
  *
  */

include "../utils/Eth2Types.dfy"

module Constants {  
  
  import opened NativeTypes
  import opened Eth2Types

  //  Powers of 2
  const TWO_UP_0 := 1;
  const TWO_UP_1 := 2;
  const TWO_UP_2 := TWO_UP_1 * TWO_UP_1;
  const TWO_UP_3 := TWO_UP_1 * TWO_UP_2;
  const TWO_UP_4 := TWO_UP_2 * TWO_UP_2;
  const TWO_UP_5 := TWO_UP_1 * TWO_UP_4;
  const TWO_UP_6 := TWO_UP_1 * TWO_UP_5;
  const TWO_UP_7 := TWO_UP_1 * TWO_UP_6;
  const TWO_UP_8 := TWO_UP_1 * TWO_UP_7;
  const TWO_UP_9 := TWO_UP_1 * TWO_UP_8;
  const TWO_UP_10 := TWO_UP_5 * TWO_UP_5;
  const TWO_UP_11 := TWO_UP_6 * TWO_UP_5;
  const TWO_UP_12 := TWO_UP_1 * TWO_UP_11;
  const TWO_UP_13 := TWO_UP_2 * TWO_UP_11;
  const TWO_UP_14 := TWO_UP_1 * TWO_UP_13;
  const TWO_UP_16 := TWO_UP_5 * TWO_UP_11;
  const TWO_UP_24 := TWO_UP_12 * TWO_UP_12;
  const TWO_UP_25 := TWO_UP_1 * TWO_UP_24;
  const TWO_UP_32 := TWO_UP_16 * TWO_UP_16;
  const TWO_UP_40 := TWO_UP_10 * TWO_UP_10 * TWO_UP_10 * TWO_UP_10;
  const TWO_UP_64 := TWO_UP_32 * TWO_UP_32;
  const TWO_UP_128 := TWO_UP_64 * TWO_UP_64;
  
  const TWO_UP_256 := TWO_UP_128 * TWO_UP_128;

  //  Powers of 10
  const TEN_UP_2 := 10 * 10;
  const TEN_UP_4 := TEN_UP_2 * TEN_UP_2;
  const TEN_UP_9 := 10 * TEN_UP_4 * TEN_UP_4;

  //  (Non-configurable) constants
  const BASE_REWARDS_PER_EPOCH := 4 ;
  const DEPOSIT_CONTRACT_TREE_DEPTH := 2 * 2 * 2 * 2 * 2 ; // 2^5
  const SECONDS_PER_DAY := 86400  ;
  const JUSTIFICATION_BITS_LENGTH : uint64 := 4 ;
  const ENDIANNESS := "little" ;

  // Configuration -- Misc
  const  MAX_COMMITTEES_PER_SLOT := TWO_UP_6; // 2^6                 
  const  TARGET_COMMITTEE_SIZE := TWO_UP_7 ; // 2^7                   
  const  MAX_VALIDATORS_PER_COMMITTEE := TWO_UP_11 ; // 2^11           
  const  MIN_PER_EPOCH_CHURN_LIMIT := TWO_UP_2 ; // 2^2               
  const  CHURN_LIMIT_QUOTIENT := TWO_UP_16 ; // 2^16                   
  const  SHUFFLE_ROUND_COUNT := 90;                        
  const  MIN_GENESIS_ACTIVE_VALIDATOR_COUNT := TWO_UP_16; // 2^16     
  const  MIN_GENESIS_TIME := 1578009600;                     

    // Configuration -- Gwei values
  const MIN_DEPOSIT_AMOUNT := TWO_UP_0 * TEN_UP_9 ; // 2^0 * 10 ^ 9         
  const MAX_EFFECTIVE_BALANCE := TWO_UP_5 * TEN_UP_9; // 2 ^ 5 * 10 ^ 9      
  const EJECTION_BALANCE := TWO_UP_4 * TEN_UP_9; // 2 ^ 4 * 10 ^ 9           
  const EFFECTIVE_BALANCE_INCREMENT := TWO_UP_0 * TEN_UP_9; //2 ^ 0 * 10 ^ 9

  // Configuration -- Initial values
  
  /**
   *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#constants}
   */
  const GENESIS_SLOT := 0 as Slot              
  const GENESIS_EPOCH := 0 as Epoch    

  // This should be of type Bytes in types.k
  // TODO: check that the type is OK (as int and uints are bounded ints, should be OK.)
  const BLS_WITHDRAWAL_PREFIX := 0x00;

  // Configuration -- Time parameters
  const  SECONDS_PER_SLOT : uint64 := 12 ;                            
  const  MIN_ATTESTATION_INCLUSION_DELAY : uint64 := TWO_UP_0 as uint64 ; // 2 ^ 0       

  const  EPOCHS_PER_ETH1_VOTING_PERIOD : uint64 := TWO_UP_6 as uint64; // (= 64)	epochs	~6.8 hours       
    

  /**
   *  
   *  The number of slots in one EPOCH.
   *  @note Current slot time seems to approx 6 seconds.
   */
  const  SLOTS_PER_EPOCH : uint64 := TWO_UP_5 as uint64; // 2 ^Int 5 = 32                           
  const  MIN_SEED_LOOKAHEAD:= TWO_UP_0 ; // 2 ^ 0                        
  const  MAX_SEED_LOOKAHEAD:= TWO_UP_2 ; // 2 ^ 2                        
  const  SLOTS_PER_ETH1_VOTING_PERIOD:= TWO_UP_10; // 2 ^ 10             
  const  SLOTS_PER_HISTORICAL_ROOT : uint64 := TWO_UP_13 as uint64 ; // 2 ^ 13  (= 8,192)            
  const  MIN_VALIDATOR_WITHDRAWABILITY_DELAY:= TWO_UP_8; // 2 ^ 8       
  const  PERSISTENT_COMMITTEE_PERIOD:= TWO_UP_11; // 2 ^ 11              
  const  MAX_EPOCHS_PER_CROSSLINK:= TWO_UP_6; // 2 ^ 6                  
  const  MIN_EPOCHS_TO_INACTIVITY_PENALTY:= TWO_UP_2; // 2 ^ 2          
  const  EARLY_DERIVED_SECRET_PENALTY_MAX_FUTURE_EPOCHS:= TWO_UP_14; // 2 ^ 14

  // Configuration -- State list lengths
  const  EPOCHS_PER_HISTORICAL_VECTOR := TWO_UP_16; // 2 ^ 16              
  const  EPOCHS_PER_SLASHINGS_VECTOR := TWO_UP_13; // 2 ^ 13               
  const  HISTORICAL_ROOTS_LIMIT := TWO_UP_24; // 2 ^ 24       

  /**
   *  Maximum size of the state.validators list.
   */             
  const  VALIDATOR_REGISTRY_LIMIT : uint64 := TWO_UP_40 as uint64; // 2 ^ 40  

  // Configuration -- Rewards and penalties
  const BASE_REWARD_FACTOR := TWO_UP_6; // 2 ^ 6                         
  const WHISTLEBLOWER_REWARD_QUOTIENT := TWO_UP_9; // 2 ^ 9              
  const PROPOSER_REWARD_QUOTIENT := TWO_UP_3; // 2 ^ 3                   
  const INACTIVITY_PENALTY_QUOTIENT := TWO_UP_25; // 2 ^ 25               
  const MIN_SLASHING_PENALTY_QUOTIENT := TWO_UP_5; // 2 ^ 5              

  // Configuration -- Max operations per block
  const MAX_PROPOSER_SLASHINGS := TWO_UP_4; // 2 ^ 4                     
  const MAX_ATTESTER_SLASHINGS := TWO_UP_0; // 2 ^ 0                     
  /**
   *  MAximum number of (aggregated) attestations in a block.
   */
  const MAX_ATTESTATIONS := TWO_UP_7; // 2 ^ 7                           
  const MAX_DEPOSITS := TWO_UP_4; // 2 ^ 4                               
  const MAX_VOLUNTARY_EXITS := TWO_UP_4; // 2 ^ 4                        

  // Configuration -- domain types
  // The following constants should be of type DomainType (String in types.k)
  // As per the rules in K, the domain types are strings and rewritten into 
  //  fixed sequences of Bytes4 
  // TODO: Check DomainType. Why are they rewitten into 5 different strings in K?
  const DOMAIN_BEACON_PROPOSER := 0x00000000 ;
  const DOMAIN_BEACON_ATTESTER := 0x01000000  ;
  const DOMAIN_RANDAO := 0x02000000  ;
  const DOMAIN_DEPOSIT := 0x03000000 ;
  const DOMAIN_VOLUNTARY_EXIT := 0x04000000  ;

    //  HashTree constants
  const BYTES_PER_CHUNK := 32        ;  
  const BYTES_PER_LENGTH_OFFSET := 4 ;
  const BITS_PER_BYTE := 8           ;
  /** Create an additional constant to store the number of bits per chunk */
  const BITS_PER_CHUNK := BYTES_PER_CHUNK * BITS_PER_BYTE ;

  /** A 0 byte, all bits set to false. */
  const FALSE_BYTE := [false, false, false, false, false, false, false, false]
  
  /** An empty chunk, all 32 bytes set to zero */
  const EMPTY_CHUNK:seq<byte> := [0, 0, 0, 0,
                                  0, 0, 0, 0,
                                  0, 0, 0, 0,
                                  0, 0, 0, 0,
                                  0, 0, 0, 0,
                                  0, 0, 0, 0,
                                  0, 0, 0, 0,
                                  0, 0, 0, 0]
} 
