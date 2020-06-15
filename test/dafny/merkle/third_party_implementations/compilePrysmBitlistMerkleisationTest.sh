#!/bin/bash

# Copyright 2020 ConsenSys AG.
# Licensed under the Apache License, Version 2.0 (the "License"); you may 
# not use this file except in compliance with the License. You may obtain 
# a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
# Unless required by applicable law or agreed to in writing, software dis-
# tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
# WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
# License for the specific language governing permissions and limitations 
# under the License.

# rm -rf TestBitlistMerkleise-go/ 2> /dev/null
# rm -rf TestBitlistMerkleise 2> /dev/null

# mkdir -p TestBitlistMerkleise-go/src/
export GOPATH="`realpath TestBitlistMerkleise-go/`"

if [[ ! -d "TestBitlistMerkleise-go/src/github.com/prysmaticlabs/go-bitfield/" ]]
then
	echo "Go getting go-bitfield..."
	go get -v github.com/prysmaticlabs/go-bitfield
fi

if [[ ! -d "TestBitlistMerkleise-go/src/github.com/prysmaticlabs/go-ssz/" ]]
then
	echo "Go getting go-ssz..."
	go get -v github.com/prysmaticlabs/go-ssz
fi

if [[ ! -d "TestBitlistMerkleise-go/src/github.com/minio/sha256-simd/" ]]
then
	echo "Go getting sha256-simd..."
	go get -v github.com/minio/sha256-simd
fi

dafny /compile:1 /compileTarget:go /spillTargetCode:1 TestBitlistMerkleise.dfy ../../../lowlevel_modules/CommandLine.go  ../../../lowlevel_modules/Rand.go ../../../../src/dafny/beacon/helpers/Crypto.go PrysmMerkleisation.go
