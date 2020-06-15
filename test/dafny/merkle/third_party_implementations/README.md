# Test of the Prysamtic Lab Bitlist Merkleisation Implementation
The following instructions detail how to compile and execute the test for the [Pysmatic Lab Bitlist Merkleisation Implementation](https://github.com/prysmaticlabs/go-ssz/blob/master/types/bitlist.go) which is part of the [Prysm Eth2 client](https://github.com/prysmaticlabs/prysm).

## Prerequisites
- Go. The commands below were tests with Go 1.14, but other versions should work fine as well.

## Commands

The following commands must be executed withing the directory including this README.md file.
```
./compilePrysmBitlistMerkleisationTest.sh 
./TestBitlistMerkleise <number-of-tests> <average-failure-percentage> <failure-reason>
```
where
- `number-of-tests` is a natural number representing the number of tests to run
- `average-failure-percentage` is a natural number, bounded between 0 and 100 included, representing the average percentage of tests that should fail.
- `failure-reason` must be either `content` or `limit` and it specifies whether the test failures should occur because of a variation in the bitlist content or in the bitlist limit respectively. 

# Test of the Py-SSZ Bitlist Merkleisation Implementation
The following instructions detail how to compile and execute the test for the [Py-SSZ](https://github.com/ethereum/py-ssz) Bitlist Merkleisation Implementation.

## Prerequisites
- Python3
- `pip3 install ssz`

## Commands

The following commands must be executed within the directory including this README.md file.
```
./compilePySszBitlistMerkleisationTest.sh
./TestBitlistMerkleise.exe <number-of-tests> <average-failure-percentage> <failure-reason>
```
where `number-of-tests`, `average-failure-percentage` and `failure-reason` are as detailed in the Prysamtic Lab Bitlist Merkleisation Implementation section above.

**Note:** The executable for the Prysamtic Lab Bitlist Merkleisation Implementation has no extension, whereas the executable for the Py-SSZ Bitlist Merkleisation Implementation has `.exe` extension.

# Test of the Py-SSZ Bitvector Merkleisation Implementation
The following instructions detail how to compile and execute the test for the [Py-SSZ](https://github.com/ethereum/py-ssz) Bitlist Merkleisation Implementation.

## Prerequisites
- Python3
- `pip3 install ssz`

## Commands

The following commands must be executed within the directory including this README.md file.
```
./compilePySszBitvectorMerkleisationTest.sh
./TestBitvectorMerkleise.exe <number-of-tests> <average-failure-percentage> 
```
where `number-of-tests` and `average-failure-percentage` are as detailed in the Prysamtic Lab Bitlist Merkleisation Implementation section above.
