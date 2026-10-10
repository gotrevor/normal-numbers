#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Known-answer tests for the joint 0/1-digit search (joint.py).
Expected values: brute force over all n below a bound, Burrell-Yu's published S(n) terms
(2, 1, 0, 3, 6, 3, 0, 5, 12, 11 for n = 0..9, their count includes 0 at n = 0), OEIS A263684 and
OEIS A146025 (0, 1, 82000)."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import pytest
from joint import solutions, next01, digits

def is01(n, b):
    return set(digits(n, b)) <= {'0', '1'}

@pytest.mark.parametrize("b", [3, 4, 5, 7])
def test_next01_matches_scan(b):
    for lo in range(0, 3000):
        n = lo
        while not is01(n, b): n += 1
        assert next01(b, lo) == n

@pytest.mark.parametrize("bases", [[4, 3], [4, 5], [3, 4, 5], [5, 3], [3, 7]])
def test_matches_brute_force(bases):
    B = bases[0]
    Lmax = 1
    while B ** Lmax < 200000: Lmax += 1     # lengths 1..Lmax cover [1, 200000)
    got = [x for L in range(1, Lmax + 1) for x in solutions(bases, L) if x < 200000]
    want = [n for n in range(1, 200000) if all(is01(n, b) for b in bases)]
    assert got == want

def test_burrell_yu_S_terms():
    S = [len(solutions([4, 3], n + 1)) for n in range(10)]
    S[0] += 1                               # their n = 0 term counts 0
    assert S == [2, 1, 0, 3, 6, 3, 0, 5, 12, 11]

def test_oeis_A263684_and_A146025():
    four_five = [x for L in range(1, 60) for x in solutions([4, 5], L)]
    assert four_five == [1, 5, 16400, 16401, 16405, 82000, 82001, 82005]
    assert [x for L in range(1, 60) for x in solutions([4, 3, 5], L)] == [1, 82000]

if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
