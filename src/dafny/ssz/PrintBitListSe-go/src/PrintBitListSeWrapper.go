package main

import (
	print "17_PrintBitListSe_Compile_"
	_dafny "dafny"
	"fmt"
	"os"
)

func main() {
	args := os.Args

	if len(args) <= 2 {
		var input _dafny.Seq
		if len(args) == 2 {
			input = _dafny.SeqOfString(args[1])
		} else {
			input = _dafny.SeqOfString("")
		}
		print.Companion_Default___.PrintBitListStringToEncodedBitListByteSeq(input)
	} else {
		fmt.Println("Must specify either zero or one argument")
	}

}
