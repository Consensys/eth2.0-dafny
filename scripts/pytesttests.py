import pytest

@pytest.mark.parametrize(
    "file, result, expected",
    (
        ("src/dafny/utils/MathHelpers.dfy", "passed", "passed"),
        ("src/dafny/utils/Helpers.dfy", "failed", "failed"),
    ),
)


def test_proof_result(file, result, expected):
    assert file.endswith(".dfy")
    assert result == expected

@pytest.mark.parametrize(
    "file2, result, expected",
    (
        ("src/dafny/utils/MathHelpers.dfy", "passed", "passed"),
        ("src/dafny/utils/Helpers.dfy", "passed", "failed"),
    ),
)


def test_proof_resultfailing(file2, result, expected):
    assert file2.endswith(".dfy")
    assert result == expected

