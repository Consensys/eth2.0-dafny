from eth2spec.capella import mainnet as spec
from eth2spec.utils.ssz.ssz_typing import (uint64)

x = uint64(16)
assert spec.integer_squareroot(x) == 4