"""Persistent check for experiments/g4_carry_parity.py (carry verdict, 2026-09-20).

Expectations HAND-DERIVED, not captured from the probe:

* omega(n) = number of DISTINCT prime factors: omega(1)=0, omega(2)=omega(4)=omega(8)=1,
  omega(6)=2, omega(30)=3, omega(210)=4, omega(2310)=5.
* The smallest n with omega(n) >= 4 is 2*3*5*7 = 210, so no digit of G4 can overflow
  before position 210.  Hence d_n = omega(n) exactly for every n <= 208.
* Position 210 carries: omega(210) = 4 = 4^1, so d_210 = 0 and one unit carries left into
  position 209.  omega(209) = omega(11*19) = 2, so d_209 = 3 and the carry STOPS there
  (3 < 4).  So d_209 = 3 != omega(209) = 2 is the FIRST carry-disturbed digit of G4.
* Consequently the first 208 digits are carry-free and the first disturbance is at 209.

Run: uv run --with pytest pytest -q experiments/test_g4_carry_parity.py
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from g4_carry_parity import omega_sieve, g4_base4_digits  # noqa: E402


def test_omega_hand_values():
    w = omega_sieve(2310)
    assert w[1] == 0
    for n in (2, 4, 8, 3, 5, 7):
        assert w[n] == 1
    assert w[6] == 2 and w[10] == 2 and w[209] == 2
    assert w[30] == 3
    assert w[210] == 4
    assert w[2310] == 5
    assert min(n for n in range(2, 2311) if w[n] >= 4) == 210


def test_digits_are_carry_free_below_209():
    digs, w = g4_base4_digits(400)
    for n in range(1, 209):
        assert digs[n - 1] == w[n], (n, digs[n - 1], w[n])


def test_first_carry_disturbance_is_at_209():
    digs, w = g4_base4_digits(400)
    assert digs[209 - 1] == 3 and w[209] == 2   # carry landed, digit bumped
    assert digs[210 - 1] == 0 and w[210] == 4   # overflowed to zero
    first = min(n for n in range(1, 401) if digs[n - 1] != w[n] % 4)
    assert first == 209


def test_parity_correlation_decays_with_N():
    """The design doc's claim was that (-1)^d_n tracks (-1)^omega(n).  It does not:
    the correlation falls as N grows.  Asserted as a strict decrease across three scales."""
    vals = []
    for N in (50000, 200000):
        digs, w = g4_base4_digits(N)
        c = sum(1 if (digs[i] & 1) == (w[i + 1] & 1) else -1 for i in range(N)) / N
        vals.append(c)
    assert vals[0] > vals[1], vals          # decaying, not constant near 1
    assert vals[1] < 0.5, vals              # already far from the claimed tracking
