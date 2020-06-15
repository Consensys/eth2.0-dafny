/*
 * Copyright 2020 ConsenSys AG.
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

package thirdpartymerkleisation

import (
	_dafny "dafny"

	"github.com/prysmaticlabs/go-bitfield"
	ssztypes "github.com/prysmaticlabs/go-ssz/types"
)

func BitlistRoot(boolSeq _dafny.Seq, byteSeq _dafny.Seq, limit _dafny.Int) _dafny.Seq {
	// Converts byteSeq into an array of bytes
	var size = byteSeq.LenInt()
	byteArray := make([]byte, size)
	for i := 0; i < size; i++ {
		byteArray[i], _ = byteSeq.IndexInt(i).(byte)
	}

	// Invokes the BitlistRoot of go-ssz
	var bf = bitfield.Bitlist(byteArray)
	output, _ := ssztypes.BitlistRoot(bf, limit.Uint64())

	// Converts the array of bytes representing the result of BitlistRoot into a
	// _dafny.Seq
	resultInterface := make([]interface{}, 32)
	for i := 0; i < 32; i++ {
		resultInterface[i] = output[i]
	}
	resultSeq := _dafny.SeqOf(resultInterface...)

	// Returns the result
	return resultSeq

}
