from eth2spec.capella import mainnet as spec
from eth2spec.utils.ssz.ssz_typing import uint64
from remerkleable.complex import Container
from remerkleable.core import View
from remerkleable.basic import uint64
from remerkleable.byte_arrays import Bytes32

def test_integer_squareroot():
    # Test case 1: Normal input
    x = uint64(64)
    assert spec.integer_squareroot(x) == 8

    
    # Test case 2: Maximum input
    x = uint64(0xFFFFFFFFFFFFFFFF)
    assert spec.integer_squareroot(x) == 4294967295

    # Test case 3: Invalid input
    y = uint64(38)
    try:
        spec.integer_squareroot(y)
    except ValueError as e:
        assert str(e) == "Input must be non-negative"

    # Test case 4: Using BeaconState
    bs = spec.BeaconState(genesis_time=678, eth1_deposit_index=7435, next_withdrawal_index=1875,
                           next_withdrawal_validator_index=1358, slot=18446744073709551584)
    
    assert spec.integer_squareroot(spec.get_total_active_balance(bs)) == 31622

def test_beacon_state():
    # Test case 5: BeaconState with next_withdrawal_validator_index greater than validators length
    bs = spec.BeaconState(next_withdrawal_validator_index=12)
    assert int(bs.next_withdrawal_validator_index) > len(bs.validators)

def test_invalid_input():
    # Test case 7: Invalid input for integer squareroot function
    x = uint64(0xFFFFFFFFFFFFFFFF + 1)
    try:
        spec.integer_squareroot(x)
    except ValueError as e:
        assert str(e) == "Input must be non-negative"

if __name__ == "__main__":
    test_integer_squareroot()
    test_beacon_state()
    test_invalid_input()
    print("All tests passed!")
