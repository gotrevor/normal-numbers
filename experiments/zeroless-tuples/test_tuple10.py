#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Known-answer tests for the base-10 tuple tree (tuple10.py).
Expected values come from independent instruments (a period of 2^n mod 10^d, direct brute force
over all r < 10^d with 2^d | r), hand facts, or the Lean theorem survives10_of_imitators."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import pytest
from tuple10 import levels, death_depth, powers_check

def zeroless(n, d):
    return '0' not in str(n % 10**d).zfill(d)

def brute(Ms, d):
    step = 2**d
    return sum(1 for r in range(0, 10**d, step)
               if zeroless(r, d) and all(zeroless(M * r, d) for M in Ms))

def test_depth_one_is_even_digits():
    assert levels([], 1) == [4]          # {2, 4, 6, 8}

@pytest.mark.parametrize("d", range(1, 7))
def test_single_set_matches_powers_of_two_period(d):
    assert levels([], d)[-1] == powers_check(d)

@pytest.mark.parametrize("exps", [[2, 4], [1], [5, 11], [3, 7, 12, 20, 22, 30, 33]])
def test_levels_match_brute_force(exps):
    Ms = [2**a for a in exps]
    assert levels(Ms, 6) == [brute(Ms, d) for d in range(1, 7)]

def test_lean_witness_depth_30():
    r = 121122111112111211111212122112   # survives10_four_sixteen_thirty
    assert r % 2**30 == 0 and all(zeroless(M * r, 30) for M in (1, 4, 16))

@pytest.mark.parametrize("d", [2, 3, 4])
def test_imitators_copy_single_set(d):
    g = 4 * 5**(d - 1)                     # phi(5^d)
    assert levels([2**g, 2**(2 * g), 2**(3 * g)], d) == levels([], d)

def test_sixteen_translates_die():
    exps = [3, 7, 12, 20, 22, 30, 33, 41, 44, 50, 57, 60, 66, 70, 75]
    Ms = [2**a for a in exps]
    assert levels(Ms, 6) == [brute(Ms, d) for d in range(1, 7)] == [4, 2, 1, 2, 1, 3]
    assert death_depth(Ms, 60) == len(levels(Ms, 60)) == 17

if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"] + sys.argv[1:]))
