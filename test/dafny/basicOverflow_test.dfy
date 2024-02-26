type uint64 = x:int | 0 <= x < 0x1000000000000000


method overflow(c: uint64) {
  if c > 0 {
    // var d: uint64;
    var d: uint64 := 0x1000000000000000 - 2;
    // assert d > 0;
    var a : uint64 := d + 1;
  }
}

