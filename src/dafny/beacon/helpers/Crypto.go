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

package eth2crypto

import (
	_dafny "dafny"

	"github.com/minio/sha256-simd"
)

// Hash calculated the SHA256 of `data`
func Hash(data _dafny.Seq) _dafny.Seq {
	// Converts data into an array of bytes
	var size = data.LenInt()
	byteArray := make([]byte, size)
	for i := 0; i < size; i++ {
		byteArray[i], _ = data.IndexInt(i).(byte)
	}

	// Caulcates the SHA256 of the array of bytes
	var sha [32]byte = sha256.Sum256(byteArray)

	// Converts the array of bytes representing the result into a
	// _dafny.Seq
	resultInterface := make([]interface{}, 32)
	for i := 0; i < 32; i++ {
		resultInterface[i] = sha[i]
	}
	resultSeq := _dafny.SeqOf(resultInterface...)

	// Returns the SHA256 of the inputs
	return resultSeq
}
