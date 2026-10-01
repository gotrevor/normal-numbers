"""Persistent checks for experiments/cprime_fresh_cancellation.py (2026-09-30).

Expectations HAND-DERIVED, not captured from the probe:

* windowJ: N = 2^16 has log2 N = 16, floor(log2 16) = 4, so J = 5; N = 2^32 gives
  floor(log2 32) + 1 = 6.
* Cutoffs at N = 2^16, a = 1: y_j = 2^(16/2^j) = 256, 16, 4, 2, floor(sqrt 2) = 1.
* Primes 1 mod 4 below 100: 5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97.  So
  omega_P(65) = 2 (5, 13), omega_P(85) = 2 (5, 17), omega_P(42) = 0, and with cutoff 10,
  omega_P(85) = 1.
* Triangle chain: |mean(x)| <= mean|x| gives A <= M; pointwise
  |prod z^full - prod z^frozen| <= sum_j |z_j - 1| * fresh_j(n+j), and each fresh p hits
  at most N/p + 1 <= 2N/p of n+j over N consecutive n, plus at most J primes above N.
  So M <= B.
* No fresh primes (P = {2, 3}, cutoffs all >= 3): W = W_y exactly, A = M = 0, rho = 0.
* One fresh prime P = {101}, N = 2^16, a = 1, h = 1: site 1 (y_1 = 256) freezes 101, sites
  2..5 (y <= 16) do not.  101 > J, so at most one site is hit per n.  A hit at site 1 is
  common to both products.  A hit at site j >= 2 multiplies the full product by z_j, the
  frozen product by 1.  The n in [0, 2^16) with 101 | n+j number floor((65536 + j - 1)/101) =
  648 for j = 1..5.  Hence
      W_y = 1 + (648/65536)(z_1 - 1),   W - W_y = (648/65536) * sum_{j=2..5} (z_j - 1),
  with z_j = e(1/4^j).

* Order split: with one fresh prime no n has fresh hits at two sites, so T2 = 0 and T1 = W - W_y.
  With P = {101, 103}, N = 2^16, a = 1: both primes are frozen at site 1 (y_1 = 256) and fresh at
  sites 2..5.  Each prime hits at most one of five consecutive integers, and a fresh hit at site
  j >= 2 forces no hit at site 1, so the frozen product is 1 on every two-site n.  Hence
      T2 = (1/N) sum_{j != j' in 2..5} (z_j - 1)(z_j' - 1) #{n < N : 101 | n+j, 103 | n+j'},
  counted here by a direct loop independent of the probe's sieve.

Run: uv run --with numpy --with pytest pytest -q experiments/test_cprime_fresh_cancellation.py
"""
import cmath
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import cprime_fresh_cancellation as probe  # noqa: E402


def e(t):
    return cmath.exp(2j * math.pi * t)


def test_window_J():
    assert probe.window_J(1 << 16) == 5
    assert probe.window_J(1 << 32) == 6


def test_cutoffs():
    assert probe.cutoffs(1 << 16, 5, 1.0) == [256, 16, 4, 2, 1]


def test_band_counts_and_omega():
    ps = probe.primes_upto(100)
    P = ps[ps % 4 == 1]
    assert P.tolist() == [5, 13, 17, 29, 37, 41, 53, 61, 73, 89, 97]
    edges, out = probe.band_counts(100, P, [10, 100])
    full = probe.omega_le(edges, out, 100)
    small = probe.omega_le(edges, out, 10)
    assert full[65] == 2 and full[85] == 2 and full[42] == 0
    assert small[85] == 1 and small[65] == 1


def test_triangle_chain():
    N = 1 << 14
    ps = probe.primes_upto(N + 64)
    for P in (ps, ps[ps % 7 == 1]):
        for m in probe.measure(N, P, [1, 3]):
            assert m["A"] <= m["M"] + 1e-12
            assert m["M"] <= m["B"] + 1e-12


def test_no_fresh_primes():
    N = 1 << 16
    for m in probe.measure(N, np.array([2, 3]), [1, 3], a=16.0):
        assert m["A"] == 0.0 and m["M"] == 0.0 and m["rho"] == 0.0


def test_one_fresh_prime_exact():
    N = 1 << 16
    [m] = probe.measure(N, np.array([101]), [1], a=1.0)
    c = 648 / 65536
    Wy = 1 + c * (e(1 / 4) - 1)
    diff = c * sum(e(1 / 4 ** j) - 1 for j in range(2, 6))
    assert abs(m["Wy"] - abs(Wy)) < 1e-12
    assert abs(m["A"] - abs(diff)) < 1e-12
    assert abs(m["W"] - abs(Wy + diff)) < 1e-12


def test_order_split_one_prime():
    [m] = probe.measure(1 << 16, np.array([101]), [1], a=1.0)
    assert m["T2"] < 1e-12
    assert abs(m["T1"] - m["A"]) < 1e-12


def test_order_split_two_primes_exact():
    N = 1 << 16
    [m] = probe.measure(N, np.array([101, 103]), [1], a=1.0)
    T2 = 0
    for j in range(2, 6):
        for jp in range(2, 6):
            if j == jp:
                continue
            cnt = sum(1 for n in range(N) if (n + j) % 101 == 0 and (n + jp) % 103 == 0)
            T2 += (e(1 / 4 ** j) - 1) * (e(1 / 4 ** jp) - 1) * cnt
    T2 /= N
    assert abs(T2) > 1e-6
    assert abs(m["T2"] - abs(T2)) < 1e-12
