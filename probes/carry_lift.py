#!/usr/bin/env -S uv run --quiet --with numpy python3
"""PROBE 15 (2026-09-22, Ren/Fable, Pair B shift-consistency): the carry-lift countermodel.

One sequence, overlapping windows.  Background A_n = 3 + Poisson(L) (iid realization), carries
C_n = floor(sum_{j>=1} A_{n+j}/4^j), prescribed orbit X_n = {4^n x_0} with digits d_n = floor(4 X_n), and

    W_{n+1} = 4 C_n - C_{n+1} + d_n            (so sum_{j>=1} W_{n+j}/4^j = C_n + X_n exactly).

Claims probed (paper: papers/ROUND2-shift-consistency-{astra,fable}.md):
  (E) exact identities: sum_{j<=k} 4^{k-j} W_{n+j} = 4^k(C_n + X_n) - (C_{n+k} + X_{n+k}) [integers when x_0=0],
      W = A + d - d' with d' in {0..3}, W >= 0.
  (P) fixed-prefix Fourier means (k = 1, 2) are small; singleton law is the 4-point smoothing of Pois(L)+3.
  (F) scheduled Fourier mean at K with 4^K >> L is e(h * mean of X) up to O(|h| L / 4^K):
      x_0 = 0 gives -> 1 at every h; x_0 = 1/3 gives e(h/3); a random x_0 gives 0.

`--selftest` asserts the exact finite block formula (2.1) against values worked out BY HAND (see `selftest`),
the exact identities on a random background, and the hand-computed Pois(8)+3 singleton value P(W=11) = 0.10878 (arithmetic of (2.1) under a uniform carry; the
L = 8 run shows the carry is NOT yet uniform there, and the L = 64 / L = 1000 runs show the regime that is).

Reading the data: fixed-prefix decay at k sites needs the carry uniform mod 4^k, i.e. A uniform mod 4^{k+1},
which needs L (1 - cos(2 pi / 4^{k+1})) >> 1 - roughly L >> 16^k / 2.  So L = 64 clears k = 1 only, L = 1000 clears
k = 2 only; that is Astra's eta_J(lambda), not a defect.  The scheduled column is orbit-controlled at every L.
"""
import sys, math, cmath, argparse
import numpy as np


def e(x):
    return np.exp(2j * np.pi * np.asarray(x, dtype=float))


def carries(A):
    """C_n = floor(sum_{j>=1} A_{n+j}/4^j) for n = 0..len(A)-1, exact integer backward recursion.
    The last 64 entries are transient (unknown far tail) and must not be used."""
    C = np.zeros(len(A), dtype=np.int64)
    c = 0
    for n in range(len(A) - 1, -1, -1):
        # C_n = floor((A_{n+1} + C_{n+1}) / 4); A_{n+1} is A[n] in 0-based storage
        c = (int(A[n]) + c) // 4
        C[n] = c
    return C


def orbit_digits(x0, n):
    """First n base-4 digits of x_0 in [0,1), exact via Fraction-free integer arithmetic on a rational."""
    from fractions import Fraction
    x = Fraction(x0)
    d = np.zeros(n, dtype=np.int64)
    for i in range(n):
        x *= 4
        d[i] = int(x)  # floor
        x -= d[i]
    return d


def lift(A, d):
    """W_{n+1} = 4 C_n - C_{n+1} + d_n.  Returns (W, C, dprime) with dprime the background's own digit."""
    C = carries(A)
    n = len(A) - 1
    W = 4 * C[:n] - C[1:n + 1] + d[:n]
    dprime = A[:n] + C[1:n + 1] - 4 * C[:n]   # A_{n+1} + C_{n+1} - 4 C_n  in {0..3}
    return W, C, dprime


def window_phase_mean(W, k, h, M):
    """(1/M) sum_{n<M} e(h sum_{j=1}^k W_{n+j}/4^j), W 0-based: W[n] = W_{n+1}."""
    T = np.zeros(M)
    for j in range(1, k + 1):
        T += W[j - 1:j - 1 + M] / 4.0 ** j
    return e(h * T).mean()


def poisson_pmf(L, kmax):
    p = np.zeros(kmax + 1)
    lp = -L
    for k in range(kmax + 1):
        p[k] = math.exp(lp)
        lp += math.log(L) - math.log(k + 1)
    return p


def block_formula_bruteforce(p, J, cmod):
    """Enumerate A_1..A_J ~ p (dict value->prob) and terminal carry C_J uniform on {0..cmod-1}, d = 0.
    Returns dict w-tuple -> probability, by the forward recursion (2.1 is NOT used here)."""
    import itertools
    out = {}
    vals = list(p.keys())
    for c in range(cmod):
        for As in itertools.product(vals, repeat=J):
            pr = 1.0 / cmod
            for a in As:
                pr *= p[a]
            C = [0] * (J + 1)
            C[J] = c
            for i in range(J, 0, -1):
                C[i - 1] = (As[i - 1] + C[i]) // 4
            w = tuple(4 * C[i - 1] - C[i] for i in range(1, J + 1))
            out[w] = out.get(w, 0.0) + pr
    return out


def selftest():
    """Hand-computed controls.

    (a) J = 1, p uniform on {3,4,5,6}, C_1 uniform mod 4, d = 0.  W = A - ((A + c) mod 4).  Enumerating the
        16 pairs by hand: W = 3 from (3,1),(4,1),(5,1),(6,1) -> 4/16 = 1/4; W = 2 from (3,2),(4,2),(5,2) -> 3/16;
        W = 0 from (3,0) -> 1/16.  Formula (2.1): P(W=w) = (1/4) sum_{b=0}^3 p(w+b): 1/4, 3/16, 1/16.  Also every
        pair satisfies W = -c (mod 4).
    (b) J = 2, same p, C_2 uniform mod 16.  (2.1): P(W=(3,3)) = (1/16) s(3) s(3) = 1/16 with s(3) = 1;
        P(W=(2,4)) = (1/16)(3/4)(3/4) = 9/256.
    (c) Pois(8)+3 background, d = 0: P(W=11) = (1/4)(p_8+p_9+p_10+p_11), Poisson(8) table
        p_8 = 0.139587, p_9 = 0.124077, p_10 = 0.099262, p_11 = 0.072190, sum 0.435116, /4 = 0.108779.
    (d) Exact identities on a random background (structural, exact in integers).
    """
    p = {3: .25, 4: .25, 5: .25, 6: .25}
    b1 = block_formula_bruteforce(p, 1, 4)
    assert abs(b1[(3,)] - 0.25) < 1e-12 and abs(b1[(2,)] - 3 / 16) < 1e-12 and abs(b1[(0,)] - 1 / 16) < 1e-12, b1
    # residue lock: with terminal carry c, W = -c mod 4
    for c in range(4):
        for a in p:
            w = 4 * ((a + c) // 4) - c
            assert (w + c) % 4 == 0
    b2 = block_formula_bruteforce(p, 2, 16)
    assert abs(b2[(3, 3)] - 1 / 16) < 1e-12 and abs(b2[(2, 4)] - 9 / 256) < 1e-12, (b2[(3, 3)], b2[(2, 4)])
    pm = poisson_pmf(8.0, 20)
    assert abs(pm[8] - 0.139587) < 2e-6 and abs(pm[11] - 0.072190) < 2e-6
    assert abs(pm[8:12].sum() / 4 - 0.108779) < 2e-6
    rng = np.random.default_rng(1)
    A = 3 + rng.poisson(8.0, 5000)
    d = orbit_digits(0, 5000)
    W, C, dp = lift(A, d)
    assert dp.min() >= 0 and dp.max() <= 3 and W.min() >= 0 and np.array_equal(W, A[:-1] - dp)
    n = 4000
    for k in (1, 3, 5):
        lhs = sum(4 ** (k - j) * W[n + j - 1] for j in range(1, k + 1))
        assert lhs == 4 ** k * C[n] - C[n + k], (k, lhs, 4 ** k * C[n] - C[n + k])
    d13 = orbit_digits(1, 3) if False else orbit_digits(__import__('fractions').Fraction(1, 3), 5000)
    assert set(d13.tolist()) == {1}
    W3, C3, _ = lift(A, d13)
    # sum_{j<=k} 4^{k-j} W_{n+j} = 4^k (C_n + 1/3) - (C_{n+k} + 1/3) = 4^k C_n - C_{n+k} + (4^k - 1)/3
    k = 4
    lhs = sum(4 ** (k - j) * W3[n + j - 1] for j in range(1, k + 1))
    assert lhs == 4 ** k * C3[n] - C3[n + k] + (4 ** k - 1) // 3
    print("selftest OK")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--M", type=int, default=1_000_000)
    ap.add_argument("--seed", type=int, default=2026)
    a = ap.parse_args()
    if a.selftest:
        selftest(); return
    rng = np.random.default_rng(a.seed)
    M = a.M
    for L, K in ((8.0, 6), (64.0, 8), (1000.0, 10)):
        A = 3 + rng.poisson(L, M + K + 80)
        print(f"\n=== L = {L:g}, M = {M}, K = {K} (4^K = {4**K}), background A = 3 + Pois(L) ===")
        pm = poisson_pmf(L, int(L + 12 * math.sqrt(L) + 30))
        for name, d in (("x0 = 0", np.zeros(M + K + 80, dtype=np.int64)),
                        ("x0 = 1/3", np.ones(M + K + 80, dtype=np.int64)),
                        ("x0 = random digits", rng.integers(0, 4, M + K + 80).astype(np.int64))):
            W, C, dp = lift(A, d)
            assert W.min() >= 0
            print(f"-- {name}: mean W = {W[:M].mean():.3f}, mean C = {C[:M].mean():.3f} (L/3+1.5 = {L/3+1.5:.3f})")
            if name == "x0 = 0":
                # singleton law vs Pois(L) and vs the exact 4-point smoothing (1/4) sum_b p(w+b-3)
                kmax = len(pm) - 1
                emp = np.bincount(W[:M], minlength=kmax + 1)[:kmax + 1] / M
                sm = np.zeros(kmax + 1)
                for w in range(kmax + 1):
                    sm[w] = sum(pm[w + b - 3] for b in range(4) if 0 <= w + b - 3 <= kmax) / 4
                print(f"   TV(emp, Pois(L)) = {0.5*np.abs(emp-pm).sum():.4f}   TV(emp, smoothed) = {0.5*np.abs(emp-sm).sum():.4f}"
                      f"   TV(smoothed, Pois(L)) = {0.5*np.abs(sm-pm).sum():.4f}   [sampling noise ~ {0.5*math.sqrt(len(pm)/M):.4f}]")
                if L == 8.0:
                    print(f"   P(W=11): emp {emp[11]:.5f}; the hand value 0.10878 assumes C uniform mod 4, which L = 8 does NOT reach"
                          f" (see C mod 4 below) - L = 8 is the pre-asymptotic control, not a check of (2.1)")
                lock = np.mean((W[:M] + C[1:M + 1]) % 4 == 0)
                print(f"   residue lock W_(n+1) + C_(n+1) = 0 mod 4: fraction {lock:.4f} (exact: 1)")
                cm4 = np.bincount(C[1:M + 1] % 4, minlength=4) / M
                print(f"   C mod 4 empirical: {np.round(cm4, 4)}  |E e(N/16)| = {math.exp(-L*(1-math.cos(math.pi/8))):.2e}")
            # X_n from the next 30 digits (error 4^-30), for the orbit Weyl sum control
            X = np.zeros(M)
            for i in range(30):
                X += d[i:i + M] / 4.0 ** (i + 1)
            for h in (1, 2, 3):
                orbit = e(h * X).mean()
                fixed = [abs(window_phase_mean(W, k, h, M)) for k in (1, 2, 3)]
                sched = window_phase_mean(W, K, h, M)
                # prediction: (1/M) sum e(h X_n) times e(-h 4^-K (C+X)); bound 2 pi |h| (mean C + 1)/4^K
                bound = 2 * math.pi * h * (C[:M].mean() + 1) / 4 ** K
                print(f"   h={h}: |fixed k=1,2,3| = {fixed[0]:.4f} {fixed[1]:.4f} {fixed[2]:.4f}   "
                      f"scheduled K={K}: {sched.real:+.4f}{sched.imag:+.4f}i   orbit Weyl sum {orbit.real:+.4f}{orbit.imag:+.4f}i"
                      f"   |diff| = {abs(sched-orbit):.4f} <= bound {bound:.4f}")


if __name__ == "__main__":
    main()
