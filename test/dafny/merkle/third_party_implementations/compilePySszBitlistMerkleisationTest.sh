#!/bin/bash

# Copyright 2021 ConsenSys AG.
# Licensed under the Apache License, Version 2.0 (the "License"); you may 
# not use this file except in compliance with the License. You may obtain 
# a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software dis-
# tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
# License for the specific language governing permissions and limitations 
# under the License.

dafny /compile:1 /compileTarget:cs /spillTargetCode:1 TestBitlistMerkleise.dfy ../../../lowlevel_modules/CommandLine.cs  ../../../lowlevel_modules/Rand.cs ../../../../src/dafny/beacon/helpers/Crypto.cs PySszMerkleisation.cs
