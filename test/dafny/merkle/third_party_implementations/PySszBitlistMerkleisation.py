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
    parser = argparse.ArgumentParser()
    parser.add_argument('bitlist',default="",nargs='?')
    args = parser.parse_args()

    bl = tuple(False if c == '0' else True for c in args.bitlist)
    # print(bl)
    hash = Bitlist(len(bl)).get_hash_tree_root(bl)
    # print(hash)
    sys.stdout.buffer.write(hash)
