#!/usr/bin/env -S uv run --quiet --with numpy python3
"""PROBE 14 (2026-09-22, Ren/Fable): two checks for the Lane-B invention round.

(1) ROTATION.  Candidate A says the window can be cut at K sites with a DETERMINISTIC unimodular
    rotation, not a loss:  W_J = e(h mu sum_{K<j<=J} 4^-j) W_K + E,  |E| <= 2 pi |h| sum_{K<j<=J} 4^-j
    E_n |omega(n+j) - mu|,  mu = window mean of omega.  Probe 13 reported |W_K - W_J| ~ 4^-K and read
    it as "fixed K fails".  Here we report |r_K W_K - W_J| (rotation applied), ||W_K| - |W_J|| (modulus),
    and the CENTERED L1 bound.  If the rotated difference and the modulus difference are both far below
    |W_K - W_J|, probe 13's gap is a rotation.

(2) RESONANCE.  The brief's diagnostic: at primes prod_{j<=k} z_j = e(h(1-4^-k)/3); for 3 | h this -> 1
    and D(prod f_j, 1; M)^2 = (1/2)|prod z_j - 1|^2 sum_{p<=M} 1/p -> 0 at k = windowK(M).  Printed for
    h in {1,2,3,12} at M = 1e8, 1e100, 1e1000 with Mertens sum_{p<=M} 1/p ~ loglog M + 0.2615.

`--selftest` asserts the resonance numbers against values worked out BY HAND (in the docstring of
`selftest`), and asserts the exact identity 4 T_k(m) - T_{k-1}(m+1) = omega(m+1) on a small range.
"""
import sys, math, cmath
import numpy as np

MERTENS_B = 0.2614972128


def omega_full(L):
    om = np.zeros(L + 1, dtype=np.int8); comp = np.zeros(L + 1, dtype=bool)
    for p in range(2, L + 1):
        if not comp[p]:
            comp[p*p::p] = True; om[p::p] += 1
    return om


def nat_log2(n):
    return n.bit_length() - 1 if n >= 1 else 0


def windowJ(N):
    return nat_log2(nat_log2(N)) + 1


def windowK(N):
    return nat_log2(nat_log2(nat_log2(N))) + 1


def windowK_of_pow10(e):
    # Nat.log 2 (10^e) = floor(e * log2 10)
    l1 = int(math.floor(e * math.log2(10)))
    return nat_log2(nat_log2(l1)) + 1


def e(x):
    return cmath.exp(2j * math.pi * x)


def resonance_row(h, e10):
    """Return (k, |prod z_j - 1|^2, D^2) at k = windowK(10^e10)."""
    k = windowK_of_pow10(e10)
    prod = e(h * (1 - 4.0 ** (-k)) / 3)
    dist2 = abs(prod - 1) ** 2
    loglogM = math.log(e10 * math.log(10))
    D2 = 0.5 * dist2 * (loglogM + MERTENS_B)
    return k, dist2, D2


def rotation_table(lN, hs=(1, 3, 4, 5, 12)):
    N = 1 << lN; J = windowJ(N)
    om = omega_full(2 * N + J + 2)
    n = np.arange(N, 2 * N)
    # window mean of omega over all sites j = 1..J (they agree to O(J/N))
    mu = float(np.mean([om[n + j].astype(float).mean() for j in range(1, J + 1)]))
    absdev = [np.abs(om[n + j].astype(float) - mu).mean() for j in range(1, J + 1)]
    out = []
    for h in hs:
        phases = [np.exp(2j * math.pi * h * om[n + j].astype(float) / 4**j) for j in range(1, J + 1)]
        full = np.ones(N, dtype=np.complex128)
        for ph in phases: full *= ph
        WJ = full.mean()
        part = np.ones(N, dtype=np.complex128)
        rows = []
        for K in range(1, J + 1):
            part *= phases[K - 1]
            WK = part.mean()
            tail = sum(4.0 ** (-j) for j in range(K + 1, J + 1))
            rK = e(h * mu * tail)
            cbound = 2 * math.pi * h * sum(4.0 ** (-j) * absdev[j - 1] for j in range(K + 1, J + 1))
            rows.append((K, abs(WK - WJ), abs(rK * WK - WJ), abs(abs(WK) - abs(WJ)), cbound, abs(WK)))
        out.append((h, J, mu, abs(WJ), rows))
    return out


def selftest():
    """Hand-computed expectations (2026-09-22, Ren).
    windowK(10^8): log2(10^8)=26.57 -> 26 -> log2 26 = 4 -> log2 4 = 2 -> K = 3.
    windowK(10^100): 332.19 -> 332 -> 8 -> 3 -> K = 4.
    h=12,k=3: e(4*63/64) = e(63/16) = e(-1/16): 4 sin^2(pi/16) = 4*(0.195090)^2 = 0.152241.
      loglog 1e8 = log(18.4207) = 2.91347; D^2 = 0.5*0.152241*(2.91347+0.26150) = 0.24168.
    h=12,k=4: e(4*255/256) = e(-1/64): 4 sin^2(pi/64) = 4*(0.0490677)^2 = 0.0096306.
      loglog 1e100 = log(230.2585) = 5.43920; D^2 = 0.5*0.0096306*5.70070 = 0.027451.
    h=3,k=3:  e(1-1/64) = e(-1/64): 0.0096306; D^2 = 0.5*0.0096306*3.17497 = 0.015289.
    h=3,k=4:  e(-1/256): 4 sin^2(pi/256) = 4*(0.0122715)^2 = 0.00060236; D^2 = 0.5*0.00060236*5.70070 = 0.0017169.
    h=1,k=3:  e(21/64): 4 sin^2(21 pi/64) = 4*sin^2(1.03084) = 4*(0.857729)^2 = 2.94279; D^2 = 0.5*2.94279*3.17497 = 4.67164.
    """
    checks = [((12, 8), (3, 0.152241, 0.24168)), ((12, 100), (4, 0.0096306, 0.027451)),
              ((3, 8), (3, 0.0096306, 0.015289)), ((3, 100), (4, 0.00060236, 0.0017169)),
              ((1, 8), (3, 2.94279, 4.67164))]
    for (h, e10), (k0, d0, D0) in checks:
        k, d, D = resonance_row(h, e10)
        assert k == k0, (h, e10, k, k0)
        assert abs(d - d0) < 2e-5, (h, e10, d, d0)
        assert abs(D - D0) < 2e-4, (h, e10, D, D0)
    # exact identity 4 T_k(m) - T_{k-1}(m+1) = omega(m+1), k = 5, m < 200
    om = omega_full(300)
    for m in range(200):
        Tk = sum(om[m + j] / 4**j for j in range(1, 6))
        Tk1 = sum(om[m + 1 + j] / 4**j for j in range(1, 5))
        assert abs(4 * Tk - Tk1 - om[m + 1]) < 1e-12, m
    # trivial windows: h = 4^a h', k <= a  =>  every phase is 1
    for a in (1, 2):
        for k in range(1, a + 1):
            S = sum(e((4**a * 3) * sum(om[m + j] / 4**j for j in range(1, k + 1))) for m in range(50))
            assert abs(S - 50) < 1e-9, (a, k, S)
    print("selftest OK")


if __name__ == "__main__":
    if "--selftest" in sys.argv:
        selftest(); sys.exit(0)
    print("== RESONANCE: k = windowK(M), |prod z_j - 1|^2, D(prod f_j,1;M)^2 (Mertens) ==")
    for h in (1, 2, 3, 12):
        for e10 in (8, 100, 1000):
            k, d, D = resonance_row(h, e10)
            print(f"h={h:2d} M=1e{e10:<4d} k={k}  |prod-1|^2={d:.6f}  D^2={D:.5f}")
    print("\n== ROTATION: J = windowJ N; per K: |WK-WJ| | |rK WK - WJ| | ||WK|-|WJ|| | centered L1 bound | |WK| ==")
    for lN in (16, 20, 24):
        for h, J, mu, aWJ, rows in rotation_table(lN):
            print(f"N=2^{lN} J={J} mu={mu:.3f} h={h}  |WJ|={aWJ:.4f}")
            for K, d, dr, dm, cb, aWK in rows:
                print(f"   K={K}: |WK-WJ|={d:.4f}  rot={dr:.4f}  mod={dm:.4f}  cbd={cb:.3f}  |WK|={aWK:.4f}")
            sys.stdout.flush()
