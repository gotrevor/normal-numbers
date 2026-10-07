#!/usr/bin/env -S uv run --quiet --with pytest --with numpy --with scipy python3
"""Known-answer tests for the carry-automaton decider (triple.py) and dim C(1,M) (cdim.py).
Expected values are hand facts or published ABL values, never this code's own output."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import pytest
from triple import decide
from cdim import cdim

def brute(Ms, depth):
    """Unit prefixes x (x%3==1) of length depth+1 with x, M x having 0/1 digits 0..depth."""
    xs = [1]
    for i in range(1, depth + 1):
        xs = [x + b * 3**i for x in xs for b in (0, 1)]
        xs = [x for x in xs
              if all((M * x // 3**j) % 3 <= 1 for M in Ms for j in range(i + 1))]
    return len(xs)

@pytest.mark.parametrize("Ms,expected", [
    ((2,), False),            # M = 2 (mod 3): lowest nonzero digit becomes 2
    ((4,), True),             # golden-mean shift (ABL I)
    ((4, 256), True),         # x = 1: 1, 4, 256 = (100111)_3
    ((16, 256), False),       # hand check: x in {1, 4} both fail at digit 1
    ((4**8, 4**9), True),     # integer witness 282864854542
])
def test_decide_known(Ms, expected):
    assert decide(Ms)[0] is expected

def test_decide_agrees_with_brute_force():
    for a in range(1, 6):
        for c in range(a + 1, 8):
            Ms = (4**a, 4**c)
            nonzero, size = decide(Ms)
            # an acyclic reachable graph has no path longer than its state count
            alive = brute(Ms, size + 1)
            if nonzero:
                assert alive > 0, (a, c)
            else:
                assert alive == 0, (a, c)

@pytest.mark.parametrize("M,dim", [(4, 0.438018), (16, 0.255960), (46, 0.097266),
                                   (61, 0.410672), (145, 0.0)])
def test_cdim_matches_abl(M, dim):   # ABL II Table 7.1
    assert abs(cdim(M)[0] - dim) < 2e-5

def test_witness_digits():
    x = 282864854542
    for M in (1, 4**8, 4**9):
        n = M * x
        while n:
            assert n % 3 <= 1
            n //= 3

if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
