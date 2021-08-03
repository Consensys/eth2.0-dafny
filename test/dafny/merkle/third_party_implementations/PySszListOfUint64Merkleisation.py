# Copyright 2021 ConsenSys AG.
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
    # the first parameter is the list limit
    # the following parameters are the elements of the list
    parser = argparse.ArgumentParser()
    parser.add_argument('limit', type=int)
    parser.add_argument('element', type=int, nargs='*')
    args = parser.parse_args()

    # Execute function/method to test
    hash = List(uint64, args.limit).get_hash_tree_root(args.element)

    # Write result to stdout in binary
    sys.stdout.buffer.write(hash)
