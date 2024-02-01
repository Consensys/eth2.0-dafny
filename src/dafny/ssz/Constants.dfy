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
  const TWO_UP_0 : uint64 := 1;
  const TWO_UP_1 : uint64 := 2;
  const TWO_UP_2 : uint64 := TWO_UP_1 * TWO_UP_1;
  const TWO_UP_3 : uint64 := TWO_UP_1 * TWO_UP_2;
  const TWO_UP_4 : uint64 := TWO_UP_2 * TWO_UP_2;
  const TWO_UP_5 : uint64 := TWO_UP_1 * TWO_UP_4;
  const TWO_UP_6 : uint64 := TWO_UP_1 * TWO_UP_5;
  const TWO_UP_7 : uint64 := TWO_UP_1 * TWO_UP_6;
  const TWO_UP_8 : uint64 := TWO_UP_1 * TWO_UP_7;
  const TWO_UP_9 : uint64 := TWO_UP_1 * TWO_UP_8;
  const TWO_UP_10 : uint64 := TWO_UP_5 * TWO_UP_5;
  const TWO_UP_11 : uint64 := TWO_UP_6 * TWO_UP_5;
  const TWO_UP_12 : uint64 := TWO_UP_1 * TWO_UP_11;
  const TWO_UP_13 : uint64 := TWO_UP_2 * TWO_UP_11;
  const TWO_UP_14 : uint64 := TWO_UP_1 * TWO_UP_13;
  const TWO_UP_16 : uint64 := TWO_UP_5 * TWO_UP_11;
  const TWO_UP_18 : uint64 := TWO_UP_2 * TWO_UP_16;
  const TWO_UP_20 : uint64 := TWO_UP_10 * TWO_UP_10;
  const TWO_UP_24 : uint64 := TWO_UP_12 * TWO_UP_12;
  const TWO_UP_25 : uint64 := TWO_UP_1 * TWO_UP_24;
  const TWO_UP_30 : uint64 := TWO_UP_14 * TWO_UP_16;
  const TWO_UP_32 : uint64 := TWO_UP_16 * TWO_UP_16;
  const TWO_UP_40 : uint64 := TWO_UP_10 * TWO_UP_10 * TWO_UP_10 * TWO_UP_10;
  const TWO_UP_64  := TWO_UP_32 as nat * TWO_UP_32 as nat;
  const TWO_UP_128 := TWO_UP_64 * TWO_UP_64;
  const TWO_UP_256 := TWO_UP_128 * TWO_UP_128;

  //  Powers of 10
  const TEN_UP_2 : uint64 := 10 * 10;
  const TEN_UP_4 : uint64 := TEN_UP_2 * TEN_UP_2;
  const TEN_UP_9 : uint64 := 10 * TEN_UP_4 * TEN_UP_4;

  /**
   *  Beacon chain spec constants
   *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#constants}
   */
   
  // Constants -- Initial values

  const GENESIS_SLOT := 0 as Slot              
  const GENESIS_EPOCH := 0 as Epoch  
  const FAR_FUTURE_EPOCH := (TWO_UP_64 - 1) as Epoch  

  // (Non-configurable) constants

  const BASE_REWARDS_PER_EPOCH : uint64 := 4;
  const DEPOSIT_CONTRACT_TREE_DEPTH : uint64 := 2 * 2 * 2 * 2 * 2 ; // 2^5
  const JUSTIFICATION_BITS_LENGTH : uint64 := 4 ;
  const ENDIANNESS := "little" ;

  // Constants -- Withdrawal prefixes

  // This should be of type Bytes in types.k
  // TODO: check that the type is OK (as int and uints are bounded ints, should be OK.)
  const BLS_WITHDRAWAL_PREFIX := 0x00;
  const ETH1_ADDRESS_WITHDRAWAL_PREFIX: byte := 0x01; // Prefix is a single byte
  const MAX_VALIDATORS_PER_WITHDRAWAL_SWEEP := TWO_UP_14; // 2 ^ 14

  // Constants -- domain types
  // The following constants should be of type DomainType (String in types.k)
  // As per the rules in K, the domain types are strings and rewritten into 
  //  fixed sequences of Bytes4 
  // TODO: Check DomainType. Why are they rewitten into 5 different strings in K?
  const DOMAIN_BEACON_PROPOSER : DomainType := Bytes([0,0,0,0]); // 0x00000000;
  const DOMAIN_BEACON_ATTESTER : DomainType := Bytes([0x1,0,0,0]); //0x01000000  ;
  const DOMAIN_RANDAO : DomainType := Bytes([0x2,0,0,0]);
  const DOMAIN_DEPOSIT : DomainType := Bytes([0x3,0,0,0]);
  const DOMAIN_VOLUNTARY_EXIT : DomainType := Bytes([0x4,0,0,0]);

  const DOMAIN_SELECTION_PROOF : DomainType := Bytes([0x5,0,0,0]);
  const DOMAIN_AGGREGATE_AND_PROOF : DomainType := Bytes([0x6,0,0,0]);


  /**
   *  Beacon chain spec preset
   *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#preset}
   */

  // Preset -- Misc
  const  MAX_COMMITTEES_PER_SLOT : uint64 := TWO_UP_6; // 2^6                 
  const  TARGET_COMMITTEE_SIZE : uint64 := TWO_UP_7 ; // 2^7                   
  const  MAX_VALIDATORS_PER_COMMITTEE : uint64 := TWO_UP_11 ; // 2^11       
  const  SHUFFLE_ROUND_COUNT : uint64 := 90;  

  const HYSTERESIS_QUOTIENT : uint64 := 4;
  const HYSTERESIS_DOWNWARD_MULTIPLIER : uint64 := 1;
  const HYSTERESIS_UPWARD_MULTIPLIER : uint64 := 5;

  // Preset -- Gwei values
  const MIN_DEPOSIT_AMOUNT : Gwei := (TWO_UP_0 * TEN_UP_9) as Gwei; // 2^0 * 10 ^ 9         
  const MAX_EFFECTIVE_BALANCE : Gwei := (TWO_UP_5 * TEN_UP_9) as Gwei; // 2 ^ 5 * 10 ^ 9      
  const EFFECTIVE_BALANCE_INCREMENT : Gwei := TEN_UP_9;//(TWO_UP_0 * TEN_UP_9) as Gwei; //2 ^ 0 * 10 ^ 9

  // Preset -- Time parameters            
  const  MIN_ATTESTATION_INCLUSION_DELAY : uint64 := TWO_UP_0 as uint64 ; // 2 ^ 0       
  
  const  SLOTS_PER_EPOCH : uint64 := TWO_UP_5; // 2 ^Int 5  @note Current slot time seems to approx 6 seconds.    
  
  const  MIN_SEED_LOOKAHEAD : uint64 := TWO_UP_0 ; // 2 ^ 0                        
  const  MAX_SEED_LOOKAHEAD : uint64 := TWO_UP_2; // 2 ^ 2   
  const  MIN_EPOCHS_TO_INACTIVITY_PENALTY : uint64 := TWO_UP_2; // 2 ^ 2          
  const  EPOCHS_PER_ETH1_VOTING_PERIOD : uint64 := TWO_UP_6 as uint64; // (= 64)	epochs	~6.8 hours       
  const  SLOTS_PER_HISTORICAL_ROOT : uint64 := TWO_UP_13 as uint64 ; // 2 ^ 13  (= 8,192)

  // Preset -- Sync committee
  const  SYNC_COMMITTEE_SIZE : uint64 := TWO_UP_9 as uint64; // 2 ^ 9 (= 512) validators
  const  EPOCHS_PER_SYNC_COMMITTEE_PERIOD : uint64 := TWO_UP_8 as uint64; // 2 ^ 8 (= 256) epochs  ~27 hours            
  
  // Preset -- State list lengths
  const  EPOCHS_PER_HISTORICAL_VECTOR : uint64 := TWO_UP_16; // 2 ^ 16              
  const  EPOCHS_PER_SLASHINGS_VECTOR : uint64 := TWO_UP_13; // 2 ^ 13               
  const  HISTORICAL_ROOTS_LIMIT : uint64 := TWO_UP_24; // 2 ^ 24       
           
  const  VALIDATOR_REGISTRY_LIMIT : uint64 := TWO_UP_40 ; // 2 ^ 40  Maximum size of the state.validstors list.       

  // Preset -- Rewards and penalties
  const BASE_REWARD_FACTOR : uint64 := TWO_UP_6 as uint64; // 2 ^ 6                         
  const WHISTLEBLOWER_REWARD_QUOTIENT : uint64 := TWO_UP_9; // 2 ^ 9              
  const PROPOSER_REWARD_QUOTIENT : uint64 := TWO_UP_3 as uint64; // 2 ^ 3                   
  const INACTIVITY_PENALTY_QUOTIENT : uint64 := TWO_UP_25; // 2 ^ 25               
  const MIN_SLASHING_PENALTY_QUOTIENT : uint64 := TWO_UP_5; // 2 ^ 5    

  const PROPORTIONAL_SLASHING_MULTIPLIER : uint64 := 1;
  
  // Preset -- Max operations per block
  const MAX_PROPOSER_SLASHINGS := TWO_UP_4; // 2 ^ 4                     
  const MAX_ATTESTER_SLASHINGS := TWO_UP_1; // 2 ^ 1                     
  
  const MAX_ATTESTATIONS := TWO_UP_7; // 2 ^ 7  MAximum number of (aggregated) attestations in a block.                         
  
  const MAX_DEPOSITS := TWO_UP_4; // 2 ^ 4                               
  const MAX_VOLUNTARY_EXITS := TWO_UP_4; // 2 ^ 4  

  const MAX_BLS_TO_EXECUTION_CHANGES := TWO_UP_4; // 2 ^ 4

  // Preset -- Execution
  const MAX_BYTES_PER_TRANSACTION := TWO_UP_30 as uint64; // 2 ^ 30  (= 1,073,741,824) bytes
  const MAX_TRANSACTIONS_PER_PAYLOAD := TWO_UP_20 as uint64; // 2 ^ 20 (= 1,048,576) transactions
  const BYTES_PER_LOGS_BLOOM := TWO_UP_8 as uint64; // 2 ^ 8 (= 256) bytes
  const MAX_EXTRA_DATA_BYTES := TWO_UP_5 as uint64; // 2 ^ 5 (= 32) bytes
  const MAX_WITHDRAWALS_PER_PAYLOAD := TWO_UP_4 as uint64; // 2 ^ 4 (= 16) withdrawals
  const MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP := TWO_UP_14 as uint64; // 2 ^ 14 (= 16,384) validators

  /**
   *  Beacon chain spec preset
   *  @link{https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md#configuration}
   */

  // Configuration -- Genesis settings
  const MIN_GENESIS_ACTIVE_VALIDATOR_COUNT : uint64 := TWO_UP_16; // 2^16     
  const MIN_GENESIS_TIME : uint64 := 1578009600;  // Dec 1, 2020, 12pm UTC

  const GENESIS_FORK_VERSION : Version := Bytes([0,0,0,0]); 

  const GENESIS_DELAY : uint64 := 604800; // 7 days

  // Configuration -- Time parameters
  const SECONDS_PER_SLOT : uint64 := 12 ;    
  const SECONDS_PER_ETH1_BLOCK : uint64 := 14 ;    
  const MIN_VALIDATOR_WITHDRAWABILITY_DELAY:= TWO_UP_8; // 2 ^ 8       
  const SHARD_COMMITTEE_PERIOD	: Epoch := TWO_UP_8 as Epoch; // uint64(2**8) (= 256)	epochs	~27 hours

  const ETH1_FOLLOW_DISTANCE : uint64 := TWO_UP_11;

  // Configuration -- Validator cycle
  const EJECTION_BALANCE : Gwei := (TWO_UP_4 * TEN_UP_9) as Gwei; // 2 ^ 4 * 10 ^ 9   
  const MIN_PER_EPOCH_CHURN_LIMIT : uint64 := TWO_UP_2; // 2^2               
  const CHURN_LIMIT_QUOTIENT : uint64 := TWO_UP_16; // 2^16 

  /**
   *  Other constants - defined to assist with formal verification and/or from the K spec
   *  @note some may now be redundant
   */

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

  // TODO: Check if any of these are still used within the spec
  const  SECONDS_PER_DAY := 86400  ;
  const  SLOTS_PER_ETH1_VOTING_PERIOD := TWO_UP_10; // 2 ^ 10             
  const  PERSISTENT_COMMITTEE_PERIOD := TWO_UP_11; // 2 ^ 11              
  const  MAX_EPOCHS_PER_CROSSLINK := TWO_UP_6; // 2 ^ 6                  
  const  EARLY_DERIVED_SECRET_PENALTY_MAX_FUTURE_EPOCHS := TWO_UP_14; // 2 ^ 14

} 
