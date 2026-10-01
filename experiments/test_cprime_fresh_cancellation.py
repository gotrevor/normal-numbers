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
* Relative first order, P = {101}, N = 2^16, a = 1, h = 1: the frozen product is 1 off the 648
  hits at site 1, and every fresh hit (site j >= 2) lands where the frozen product is 1, so with
  c = 648/65536
      T1 = Sbar = c * sum_{j=2..5} (z_j - 1),   G = T1 / W_y = Sbar / (1 + c(z_1 - 1)),
      C = T1 - W_y Sbar = -c (z_1 - 1) Sbar.
* Analytic G levels.  g_inf(d, w, s) = s^(-dw) e^(-gamma dw)/Gamma(1+dw) - 1:
    d = 1, w = 1, s = 1/2:  2 e^(-gamma)/Gamma(2) - 1 = 2 * 0.5614594836 - 1 = 0.1229189672;
    d = 1/2, w = -2 (z = -1): 1/Gamma(0) = 0, so g = -1 exactly;
    d -> 0: g = d w log(1/s) + O(d^2).
  log_mertens(10) = log((1/2)(2/3)(4/5)(6/7)) = log(8/35).  g_sd with d = 1, w = 1, N = 10,
  primes {2,3,5,7}, y = 3:  (log 10)(8/35) * (1 + 1/5)(1 + 1/7) / Gamma(2) - 1 = 384 log(10)/1225 - 1.
  G_A for P = {101}: site 1 has Mf = My (101 frozen), sites 2..5 have My = 1, Mf = 1 + c w_k, so
  G_A = c sum_{k=2..5} w_k (= Sbar), and prod_k My_k = 1 + c w_1 = W_y.
* Generalized Dickman R_kappa(u).  kappa = 1 is Dickman: F = e^(-gamma) int_0^u rho, and on [1, 2]
  rho(t) = 1 - log t, so int_0^u rho = 2u - u log u - 1 and R(u) = F/(e^(-gamma) u) = 2 - log u - 1/u.
  F(oo) = 1 (int_0^oo rho = e^gamma for kappa = 1; the Selberg-Delange normalization in general) gives
  R(u) -> e^(gamma kappa) Gamma(1 + kappa) u^(-kappa), checked at u = 12 for real and complex kappa.
  kappa = -1 (d = 1/2, z = -1) is a pole: the site factor is -1.  Small kappa: R = 1 - kappa log u.
* Frozen-mean ratio, P = {3}, N = 100, y = 10: mean of z^[3 | m] over m = 1..100 is
  1 + (z - 1) * 33/100, CRT product 1 + (z - 1)/3.
* Extrapolation: G = 2 + 3i + (1 - i)*10/L sampled at L = 10, 20, 40 recovers G_oo = 2 + 3i with miss 0.

* PairSecondOrder ratio, P = {101, 103}, N = 2^16, a = 1: site 1 freezes both primes (fresh mass 0),
  sites 2..5 have fresh mass 1/101 + 1/103 each, so Fw = (1/101 + 1/103) * sum_{j=2..5} |z_j - 1|, and
  T2/Fw^2 uses the directly counted T2 of the order-split test.  P = {101}: T2 = 0, ratio 0.

Run: uv run --with numpy --with scipy --with pytest pytest -q experiments/test_cprime_fresh_cancellation.py
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


def test_relative_first_order_one_prime_exact():
    N = 1 << 16
    [m] = probe.measure(N, np.array([101]), [1], a=1.0)
    c = 648 / 65536
    Sbar = c * sum(e(1 / 4 ** j) - 1 for j in range(2, 6))
    Wy = 1 + c * (e(1 / 4) - 1)
    assert abs(m["Sbar"] - Sbar) < 1e-12
    assert abs(m["G"] - Sbar / Wy) < 1e-12
    assert abs(m["C"] - (-c * (e(1 / 4) - 1) * Sbar)) < 1e-12


def test_cli_relative_report_runs():
    import subprocess
    out = subprocess.run([os.path.join(HERE, "cprime_fresh_cancellation.py"), "--logN", "14",
                          "--h", "1", "--a", "1", "0.5", "--sets", "p = 1 mod 3",
                          "--report", "relative"], capture_output=True, text=True, check=True).stdout
    rows = [l for l in out.splitlines() if l.startswith("| p = 1 mod 3 |")]
    assert len(rows) == 2  # one set, one h, two values of a
    assert "y_j = N^(0.5*2^-j)" in out


def test_g_inf_hand_values():
    assert abs(probe.g_inf(1.0, 1.0, 0.5) - 0.1229189672) < 1e-9
    assert abs(probe.g_inf(0.5, -2.0, 0.5) - (-1)) < 1e-12
    w, d = complex(-1, 1), 1e-6
    assert abs(probe.g_inf(d, w, 0.25) - d * w * math.log(4)) < 1e-10


def test_g_sd_hand_value():
    assert abs(probe.log_mertens(10) - math.log(8 / 35)) < 1e-12
    g = probe.g_sd(1.0, 1.0, 10, np.array([2, 3, 5, 7]), 3, math.log(8 / 35))
    assert abs(g - (384 * math.log(10) / 1225 - 1)) < 1e-12


def test_site_reduction_one_prime_exact():
    N = 1 << 16
    [m] = probe.measure(N, np.array([101]), [1], a=1.0)
    c = 648 / 65536
    assert abs(m["GA"] - c * sum(e(1 / 4 ** j) - 1 for j in range(2, 6))) < 1e-12
    assert abs(m["My_prod_over_Wy"] - 1) < 1e-12


def test_dickman_R_kappa_one_closed_form():
    for u in (1.25, 1.5, 2.0):
        assert abs(probe.dickman_R(1, u) - (2 - math.log(u) - 1 / u)) < 1e-12


def test_dickman_R_normalization_at_infinity():
    from scipy.special import gamma
    g = probe.EULER_GAMMA
    for k in (1, 0.5, -0.5, complex(-0.3, 0.3), complex(-0.5, 0.5)):
        want = cmath.exp(g * k) * gamma(1 + k) * 12 ** (-k)
        assert abs(probe.dickman_R(k, 12) - want) < 1e-5 * abs(want)


def test_dickman_pole_and_small_kappa():
    assert probe.g_dickman(0.5, -2.0, 0.5) == -1
    k = complex(-1e-6, 1e-6)
    assert abs(probe.dickman_R(k, 8) - (1 - k * math.log(8))) < 1e-9


def test_extrapolate_exact_on_model():
    Ls = [10.0, 20.0, 40.0]
    Gs = [complex(2, 3) + complex(1, -1) * 10 / L for L in Ls]
    Goo, miss = probe.extrapolate(Ls, Gs)
    assert abs(Goo - complex(2, 3)) < 1e-12 and miss < 1e-12


def test_dickman_boundary_re_kappa_minus_one():
    # z = -i, d = 1: kappa = -1 - i up to rounding; must be finite, not the Re < -1 refusal
    k = complex(math.cos(3 * math.pi / 2) - 1, -1)
    assert np.isfinite(probe.dickman_R(k, 4))


def test_frozen_mean_ratio_one_prime():
    z = e(1 / 4)
    r = probe.frozen_mean_ratio(100, np.array([3]), z, 10)
    assert abs(r - (1 + (z - 1) * 33 / 100) / (1 + (z - 1) / 3)) < 1e-12


def test_pair_second_order_ratio_exact():
    N = 1 << 16
    [m] = probe.measure(N, np.array([101, 103]), [1], a=1.0)
    Fw = (1 / 101 + 1 / 103) * sum(abs(e(1 / 4 ** j) - 1) for j in range(2, 6))
    T2 = 0
    for j in range(2, 6):
        for jp in range(2, 6):
            if j != jp:
                cnt = sum(1 for n in range(N) if (n + j) % 101 == 0 and (n + jp) % 103 == 0)
                T2 += (e(1 / 4 ** j) - 1) * (e(1 / 4 ** jp) - 1) * cnt
    T2 /= N
    assert abs(m["Fw"] - Fw) < 1e-12
    assert abs(m["T2_over_Fw2"] - abs(T2) / Fw ** 2) < 1e-9
    [m1] = probe.measure(N, np.array([101]), [1], a=1.0)
    assert m1["T2_over_Fw2"] < 1e-9
