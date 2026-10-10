#!/usr/bin/env -S uv run --quiet --with pytest python3
"""Known-answer tests for the exponent-class tree (classtree.py).
Expected values: the exact bijection count 8^d (alpha -> 4^alpha x is a bijection onto units = 1 mod 3),
Lean-kernel counts (ErdosTripleClasses.aliveClasses_two/_three), and direct per-integer checks."""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
import pytest
from classtree import init, lift

def survives(Ms, d):
    mod = 3**(d + 1); xs = [1]
    for k in range(1, d + 1): xs = [x + e * 3**k for x in xs for e in (0, 1)]
    ok = lambda v: all((v // 3**k) % 3 != 2 for k in range(d + 1))
    return any(ok(x) and all(ok(M * x % mod) for M in Ms) for x in xs)

def levels(D):
    lev = init(1, lambda a, b: True); out = {1: lev}
    for d in range(1, D):
        lev = lift(lev, d); out[d + 1] = lev
    return out

LEV = levels(4)

@pytest.mark.parametrize("d", [1, 2, 3, 4])
def test_point_total_is_eight_to_the_d(d):
    assert sum(len(v) for v in LEV[d].values()) == 8**d

def test_lean_counts():
    assert len(LEV[2]) == 49 and len(LEV[3]) == 367

def test_classes_match_direct_check_depth_3():
    for a in range(27):
        for b in range(27):
            assert ((a, b) in LEV[3]) == survives([4**a, 4**(a + b)], 3)

def test_mod_nine_theorem_on_integers():
    bad = {0, 1, 8}
    for a in range(60):
        for b in range(60):
            if a % 9 in bad or b % 9 in bad or (a + b) % 9 in bad: continue
            assert not survives([4**a, 4**(a + b)], 2)

def test_known_nonzero_triples_alive():   # (1,3): x = 1; (8,1): x = 282864854542
    for a, b in [(1, 3), (8, 1), (2, 1)]:
        assert all(survives([4**a, 4**(a + b)], d) for d in range(6))

def test_offline_point_depth_8():
    assert pow(4, 1227, 3**9) == 10 and pow(4, 7488, 3**9) == 28
    assert survives([10, 28], 8)

if __name__ == "__main__":
    sys.exit(pytest.main([__file__, "-q"]))
