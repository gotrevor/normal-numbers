"""Hand-checked values for cantor_inverse_sums.py."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cantor_inverse_sums as C  # noqa: E402


def test_cantor_units_b2():
    # two ternary digits, last digit 2: 02_3 = 2, 22_3 = 8
    assert sorted(C.cantor_units(2).tolist()) == [2, 8]


def test_direct_b1():
    # C_1 = {2}: |S(n)| = 1 for every n
    assert abs(C.max_ratio(1, False)[0] - 1.0) < 1e-9


def test_direct_b2_by_hand():
    # S(n) = e(2n/9) + e(8n/9); |S| = |1 + e(6n/9)| = 2|cos(pi*6n/9)|; n=3k excluded;
    # n = 1: 2|cos(2pi/3)| = 1 -> ratio 0.5; every 3 ∤ n gives 6n/9 = 2n/3 mod 1 in {1/3, 2/3}
    assert abs(C.max_ratio(2, False)[0] - 0.5) < 1e-9
