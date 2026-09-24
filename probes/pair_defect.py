#!/usr/bin/env python3
"""PROBE (2026-09-24, pd-refute): is `pairDefect` decaying, flat, or growing?

Stdlib only (the box has no numpy and no egress).

Target: `PairDecouple b p q t` of `src/NormalNumbers/SwingC1Decouple.lean`,

    Q = primorialLe P = prod_{r <= P prime} r,
    T(N)             = sum_{k>=1} omega(N+k)/b^k          (= omegaTail b N)
    pairTail(n)      = T(pn) - T(qn),
    truncPairTail(n) = sum_{r<=P} (b^{pn mod r} - b^{qn mod r})/(b^r - 1),
    pairRemainder(n) = pairTail(n) - truncPairTail(n),
    B(n)             = e(t * pairRemainder(n)),           t = m/b
    progMean_c(R)    = (1/R) sum_{r<R} B(c + rQ),   fullMean(N) = (1/N) sum_{n<N} B(n),
    pairDefect(R)    = (1/Q) sum_{c<Q} | progMean_c(R) - fullMean(QR) |.

`PairDecouple` is: for every P, pairDefect(R) -> 0 as R -> oo.

WHY THE FOURIER COLUMN IS THE THERMOMETER.  `norm_test_le_pairDefect`
(`src/NormalNumbers/PairDecoupleLower.lean`, this lap) proves: for every chi on Z/Q with
|chi| <= 1 and sum_c chi(c) = 0,

    | (1/Q) sum_c chi(c) progMean_c(R) |  <=  pairDefect(R).

With chi(c) = e(-ac/Q), a != 0, that is Q-1 CERTIFIED lower bounds LB(a) on the defect.  A
refutation of `PairDecouple` = one (P, a) whose LB(a) stays away from 0 as R -> oo.  So `maxLB`
is the refutation thermometer and `defect` is its upper envelope.  `lowerbnd` is the second,
independent certificate of `norm_fullMean_pairTail_le`:
pairDefect >= (|fullMean f (QR)| - |prod_{r<=P} pairLocalFactor|)/2.

CONTROLS (hand-computed; `--selftest`):
  C1  B == 1                    => defect = 0 exactly, every LB(a) = 0.
  C2  B(n) = e(an/Q), a != 0    => progMean_c = e(ac/Q), fullMean = 0, defect = 1 EXACTLY,
                                   LB(a) = 1 and LB(a') = 0 for a' != a.
  C3  B(n) = e(alpha n)         => progMean_c = e(alpha c) D_R with
                                   D_R = (1/R) sum_{r<R} e(alpha Q r); defect ~ 1/R.  Compared
                                   against the closed-form geometric sum.
  C4  ARITHMETIC IDENTITY (the real one).  omega(m) = #{r prime : r | m} gives
          T(N) = sum_{r prime} b^{N mod r}/(b^r - 1),
      hence   pairRemainder(n) = sum_{k>=1}(omega_{>P}(pn+k) - omega_{>P}(qn+k))/b^k.
      Every case computes pairRemainder BOTH ways -- (full omega) minus (closed-form
      truncPairTail), and directly from a sieve on omega_{>P} -- and asserts agreement.  That
      pins primePeriodicTerm, the primorial period, and the tail convergence at once.
  C5  T(b,0) = sum_{r prime} 1/(b^r - 1), the two sides computed independently.
"""

import argparse
import cmath
import math
import sys
from array import array

TWOPI = 2.0 * math.pi


# ---------------------------------------------------------------- sieve ----
def omega_sieve(limit: int, pmin: int = 0) -> bytearray:
    """omega_{>pmin}(m) for m <= limit (pmin = 0 gives full omega)."""
    om = bytearray(limit + 1)
    comp = bytearray(limit + 1)
    for r in range(2, limit + 1):
        if comp[r]:
            continue
        if r * r <= limit:
            for i in range(r * r, limit + 1, r):
                comp[i] = 1
        if r > pmin:
            for i in range(r, limit + 1, r):
                om[i] += 1
    return om


def primes_le(P):
    return [r for r in range(2, P + 1) if all(r % d for d in range(2, int(r**0.5) + 1))]


def primorial_le(P):
    z = 1
    for r in primes_le(P):
        z *= r
    return z


def tail_array(om, b, limit):
    """T[M] = sum_{k>=1} om[M+k]/b^k for M <= limit, by the exact backward recurrence
    T[M] = (om[M+1] + T[M+1])/b.  Contracting, so numerically stable and free of any
    k-truncation."""
    T = array("d", bytes(8 * (limit + 1)))
    inv = 1.0 / b
    acc = 0.0
    for M in range(limit - 1, -1, -1):
        acc = (om[M + 1] + acc) * inv
        T[M] = acc
    return T


def trunc_pair_tail(b, P, p, q, n):
    """Closed form sum_{r<=P} (b^{pn mod r} - b^{qn mod r})/(b^r - 1)."""
    s = 0.0
    for r in primes_le(P):
        s += (float(b) ** ((p * n) % r) - float(b) ** ((q * n) % r)) / (float(b) ** r - 1.0)
    return s


# ------------------------------------------------------------- the defect ----
def defect_and_lb(B, Q, R, want_lb=True):
    prog = [0j] * Q
    for c in range(Q):
        s = 0j
        base = c
        for r in range(R):
            s += B[base]
            base += Q
        prog[c] = s / R
    full = sum(prog) / Q
    defect = sum(abs(g - full) for g in prog) / Q
    lbs = []
    if want_lb:
        for a in range(1, Q):
            s = 0j
            for c in range(Q):
                s += cmath.exp(-1j * TWOPI * a * c / Q) * prog[c]
            lbs.append(abs(s) / Q)
    return defect, prog, full, lbs


def run_case(b, m, p, q, P, Rlist, out=sys.stdout):
    t = m / b
    Q = primorial_le(P)
    R = max(Rlist)
    N = Q * R
    limit = max(p, q) * N + 64
    om_all = omega_sieve(limit, 0)
    om_big = omega_sieve(limit, P)
    T_all = tail_array(om_all, b, limit)
    T_big = tail_array(om_big, b, limit)

    c4 = 0.0
    rem = [0.0] * N
    pt = [0.0] * N
    for n in range(N):
        pn, qn = p * n, q * n
        pt[n] = T_all[pn] - T_all[qn]
        r1 = pt[n] - trunc_pair_tail(b, P, p, q, n)
        r2 = T_big[pn] - T_big[qn]
        d = abs(r1 - r2)
        if d > c4:
            c4 = d
        rem[n] = r2
    if c4 > 1e-9:
        raise AssertionError(f"C4 FAILED: the two pairRemainder routes disagree by {c4:.3e}")

    B = [cmath.exp(1j * TWOPI * t * x) for x in rem]
    f = [cmath.exp(1j * TWOPI * t * x) for x in pt]
    A = [cmath.exp(1j * TWOPI * t * trunc_pair_tail(b, P, p, q, c)) for c in range(Q)]
    model = abs(sum(A) / Q)   # |periodMean A Q| = |prod_{r<=P} pairLocalFactor b t r p q|

    print(f"b={b} m={m} t={t:.6g} p={p} q={q} P={P} Q={Q}  "
          f"|periodMean A|={model:.6f}  C4 residual={c4:.2e}", file=out)
    print(f"{'R':>8} {'N':>9} {'defect':>10} {'maxLB':>10} {'a*':>4} "
          f"{'|fullB|':>9} {'|fullf|':>9} {'d*sqrtR':>9} {'lowerbnd':>9}", file=out)
    rows = []
    for Rr in Rlist:
        d, prog, full, lbs = defect_and_lb(B, Q, Rr)
        fm = abs(sum(f[: Q * Rr]) / (Q * Rr))
        mx = max(lbs) if lbs else 0.0
        am = (lbs.index(mx) + 1) if lbs else 0
        rows.append((Rr, d, mx, am, abs(full), fm))
        print(f"{Rr:>8} {Q*Rr:>9} {d:>10.6f} {mx:>10.6f} {am:>4} "
              f"{abs(full):>9.6f} {fm:>9.6f} {d*math.sqrt(Rr):>9.4f} "
              f"{(fm-model)/2:>9.6f}", file=out)
    print(file=out, flush=True)
    return rows, model, c4


# ------------------------------------------------------------- selftest ----
def selftest():
    ok = True
    Q, R = 6, 400

    B = [1 + 0j] * (Q * R)
    d, _, _, lbs = defect_and_lb(B, Q, R)
    good = d < 1e-13 and max(lbs) < 1e-13
    print(f"C1  B==1:   defect={d:.3e} (want 0)  maxLB={max(lbs):.3e} (want 0)  "
          f"{'ok' if good else 'FAIL'}")
    ok &= good

    for a in (1, 2, 3, 5):
        B = [cmath.exp(1j * TWOPI * a * n / Q) for n in range(Q * R)]
        d, _, full, lbs = defect_and_lb(B, Q, R)
        want = [1.0 if j == a - 1 else 0.0 for j in range(Q - 1)]
        good = abs(d - 1) < 1e-11 and max(abs(x - y) for x, y in zip(lbs, want)) < 1e-11
        print(f"C2  B=e({a}n/{Q}): defect={d:.12f} (want 1)  "
              f"LB={[round(x,9) for x in lbs]} (want {want})  {'ok' if good else 'FAIL'}")
        ok &= good

    alpha = (math.sqrt(5) - 1) / 2
    for Rr in (100, 1000, 4000):
        B = [cmath.exp(1j * TWOPI * alpha * n) for n in range(Q * Rr)]
        d, prog, full, lbs = defect_and_lb(B, Q, Rr, want_lb=False)
        DR = sum(cmath.exp(1j * TWOPI * alpha * Q * r) for r in range(Rr)) / Rr
        ph = [cmath.exp(1j * TWOPI * alpha * c) * DR for c in range(Q)]
        pred = sum(abs(z - sum(ph) / Q) for z in ph) / Q
        good = abs(d - pred) < 1e-10
        print(f"C3  B=e(phi n), R={Rr:>5}: defect={d:.3e}  closed form={pred:.3e}  "
              f"{'ok' if good else 'FAIL'}")
        ok &= good

    for b in (3, 4):
        lim = 400
        om = omega_sieve(lim, 0)
        lhs = tail_array(om, b, lim)[0]
        rhs = sum(1.0 / (b**r - 1) for r in primes_le(lim))
        good = abs(lhs - rhs) < 1e-13
        print(f"C5  b={b}: T(0)={lhs:.16f}  sum_r 1/(b^r-1)={rhs:.16f}  "
              f"{'ok' if good else 'FAIL'}")
        ok &= good

    print("SELFTEST", "PASS" if ok else "FAIL")
    return 0 if ok else 1


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--nmax", type=int, default=120000)
    ap.add_argument("--only", type=int, default=0)
    args = ap.parse_args()
    if args.selftest:
        sys.exit(selftest())

    print("=" * 102)
    print("pairDefect probe.  Decaying defect and maxLB => PairDecouple TRUE at that (b,m,p,q,P).")
    print("A maxLB (or lowerbnd) bounded away from 0 as R grows is a CERTIFIED refutation.")
    print("=" * 102)

    cases = [
        (3, 1, 2, 3, 2), (3, 1, 2, 3, 3), (3, 1, 2, 3, 5),
        (3, 1, 3, 5, 2), (3, 1, 3, 5, 3), (3, 1, 3, 5, 5),
        (3, 1, 2, 5, 3), (3, 1, 5, 7, 3),
        (4, 1, 2, 3, 2), (4, 1, 2, 3, 3), (4, 1, 3, 5, 3),
        (3, 2, 2, 3, 3), (3, 4, 2, 3, 3), (3, 1, 2, 3, 7),
    ]
    if args.only:
        cases = cases[: args.only]
    for (b, m, p, q, P) in cases:
        Q = primorial_le(P)
        Rmax = max(8, args.nmax // Q)
        Rlist = sorted({max(4, Rmax // 8), max(4, Rmax // 4), max(4, Rmax // 2), Rmax})
        try:
            run_case(b, m, p, q, P, Rlist)
        except AssertionError as e:
            print(f"b={b} m={m} p={p} q={q} P={P}: {e}", flush=True)


if __name__ == "__main__":
    main()
