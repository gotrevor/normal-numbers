"""Persistent check for experiments/walsh_parity_identity.py (Walsh-Weyl bridge, 2026-09-20).

Expected values HAND-COMPUTED from the Parry (maximal-entropy) measure of the golden-mean
(11-avoiding) subshift, not captured from the probe:

  Transition matrix A = [[1,1],[1,0]] on states {0,1}, Perron eigenvalue phi, right
  eigenvector v = (phi, 1) since A v = (phi+1, phi) = phi*(phi,1).
  Parry transitions P(i->j) = A_ij * v_j / (phi * v_i):
      P(0->0) = phi/(phi*phi) = 1/phi = 0.6180339887
      P(0->1) = 1/(phi*phi)   = 1/phi^2 = 0.3819660113
      P(1->0) = phi/(phi*1)   = 1
  Stationary pi_0 = 1/(1+p) with p = P(0->1):  pi_0 = 0.7236067977, pi_1 = 0.2763932023.
  Block frequencies:
      F(00) = pi_0 * (1-p) = 0.7236067977 * 0.6180339887 = 0.4472135955 = 1/sqrt(5)
      F(01) = pi_0 * p     = 0.2763932023 = (5-sqrt5)/10
      F(10) = pi_1         = 0.2763932023
      F(11) = 0
  Parity correlations:
      P({0})   = pi_0 - pi_1 = 0.4472135955 = 1/sqrt(5)
      P({0,1}) = F00 + F11 - F01 - F10 = 1/sqrt5 - (5-sqrt5)/5 = 2/sqrt(5) - 1 = -0.1055728090

The identity itself (I),(II) is exact for ANY sequence, so it is asserted to 1e-12 on all
five test sequences including the degenerate constant one.

Run: uv run --with pytest pytest -q experiments/test_walsh_parity_identity.py
"""
import os
import sys
from itertools import product
from random import Random

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from walsh_parity_identity import (  # noqa: E402
    parity, freq, champernowne_bits, golden_mean_bits, thue_morse_bits,
)

R5 = 5 ** 0.5


def _sequences(M):
    rng = Random(3)
    return {
        "champernowne": champernowne_bits(M),
        "golden": golden_mean_bits(M),
        "thue-morse": thue_morse_bits(M),
        "random": [rng.getrandbits(1) for _ in range(M)],
        "constant": [0] * M,
    }


def test_identity_I_exact_on_every_sequence():
    """F_N(w) = 2^-L (1 + sum_{S nonempty} (-1)^{w.S} P_N(S)) — exact, any sequence."""
    N, L = 4000, 3
    subsets = [S for k in (1, 2, 3) for S in __import__("itertools").combinations(range(L), k)]
    for name, s in _sequences(N + 10).items():
        P = {S: parity(s, S, N) for S in subsets}
        for w in product((0, 1), repeat=L):
            rhs = 1.0 + sum((-1 if sum(w[i] for i in S) % 2 else 1) * P[S] for S in subsets)
            assert abs(freq(s, w, N) - rhs / 2 ** L) < 1e-12, (name, w)


def test_identity_II_exact_on_every_sequence():
    """P_N(S) = sum_w (-1)^{w.S} F_N(w) — the inverse transform."""
    N, L = 4000, 3
    subsets = [S for k in (1, 2, 3) for S in __import__("itertools").combinations(range(L), k)]
    for name, s in _sequences(N + 10).items():
        for S in subsets:
            tot = sum((-1 if sum(w[i] for i in S) % 2 else 1) * freq(s, w, N)
                      for w in product((0, 1), repeat=L))
            assert abs(tot - parity(s, S, N)) < 1e-12, (name, S)


def test_golden_mean_matches_hand_computed_parry_measure():
    N = 200000
    s = golden_mean_bits(N + 10)
    tol = 0.01  # sampling error at N = 2e5
    assert abs(freq(s, (0, 0), N) - 1 / R5) < tol
    assert abs(freq(s, (0, 1), N) - (5 - R5) / 10) < tol
    assert abs(freq(s, (1, 0), N) - (5 - R5) / 10) < tol
    assert freq(s, (1, 1), N) == 0.0  # 11 is forbidden: exactly zero, not approximately
    assert abs(parity(s, (0,), N) - 1 / R5) < tol
    assert abs(parity(s, (0, 1), N) - (2 / R5 - 1)) < tol


def test_walsh_instrument_sees_the_forbidden_block():
    """The design doc's claim: depth-2 parity of an 11-free sequence is bounded away from 0."""
    N = 100000
    s = golden_mean_bits(N + 10)
    assert abs(parity(s, (0, 1), N)) > 0.05     # hand value 0.1056
    champ = champernowne_bits(N + 10)
    assert abs(parity(champ, (0, 1), N)) < 0.05  # a normal sequence: tends to 0
