# Copyright 2020 ConsenSys AG.
# Licensed under the Apache License, Version 2.0 (the "License"); you may 
# not use this file except in compliance with the License. You may obtain 
# a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software dis-
# tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
# License for the specific language governing permissions and limitations 
# under the License.

from typing import Sequence

from ssz.hashable_container import HashableContainer, SignedHashableContainer
from ssz.sedes import (
    Bitlist,
    Bitvector,
    List,
    Vector,
    boolean,
    bytes32,
    bytes48,
    bytes96,
    uint64,
)

import sys
import argparse


if __name__ == "__main__":
    # Setup argument parser
    # The only requires command line argument is the bitlist limit
    # The bitlist content is supplied via stdin
    parser = argparse.ArgumentParser()
    parser.add_argument('limit', type=int)
    args = parser.parse_args()

    # Binary read from stdin
    stdin = sys.stdin.buffer.read()    

    bl = tuple(False if b == 0 else True for b in stdin)

    # Execute function/method to test
    hash = Bitlist(args.limit).get_hash_tree_root(bl)

    # Write result to stdout in binary
    sys.stdout.buffer.write(hash)
