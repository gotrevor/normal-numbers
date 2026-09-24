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
def omega_sieve(limit: int, pmin: int = 0, pmax: int | None = None) -> bytearray:
    """omega_{(pmin, pmax]}(m) for m <= limit: the number of distinct prime factors r of m with
    pmin < r <= pmax.  pmin = 0, pmax = None gives the full omega."""
    om = bytearray(limit + 1)
    comp = bytearray(limit + 1)
    hi = limit if pmax is None else min(limit, pmax)
    for r in range(2, limit + 1):
        if comp[r]:
            continue
        if r * r <= limit:
            for i in range(r * r, limit + 1, r):
                comp[i] = 1
        if pmin < r <= hi:
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

    # truncPairTail is exactly Q-periodic (truncPairTail_add_mul_primorial), so tabulate it once
    tptQ = [trunc_pair_tail(b, P, p, q, c) for c in range(Q)]
    c4 = 0.0
    rem = [0.0] * N
    pt = [0.0] * N
    nc4 = min(N, 20000)
    for n in range(N):
        pn, qn = p * n, q * n
        pt[n] = T_all[pn] - T_all[qn]
        r2 = T_big[pn] - T_big[qn]
        rem[n] = r2
        if n < nc4:
            d = abs((pt[n] - tptQ[n % Q]) - r2)
            if d > c4:
                c4 = d
    if c4 > 1e-9:
        raise AssertionError(f"C4 FAILED: the two pairRemainder routes disagree by {c4:.3e}")

    B = [cmath.exp(1j * TWOPI * t * x) for x in rem]
    f = [cmath.exp(1j * TWOPI * t * x) for x in pt]
    A = [cmath.exp(1j * TWOPI * t * x) for x in tptQ]
    model = abs(sum(A) / Q)   # |periodMean A Q| = |prod_{r<=P} pairLocalFactor b t r p q|

    print(f"b={b} m={m} t={t:.6g} p={p} q={q} P={P} Q={Q}  "
          f"|periodMean A|={model:.6f}  C4 residual={c4:.2e}", file=out)
    print(f"{'R':>8} {'N':>9} {'defect':>10} {'maxLB':>10} {'a*':>4} "
          f"{'|fullB|':>9} {'|fullf|':>9} {'rel=d/|fB|':>11} {'lowerbnd':>9}", file=out)
    rows = []
    for Rr in Rlist:
        d, prog, full, lbs = defect_and_lb(B, Q, Rr)
        fm = abs(sum(f[: Q * Rr]) / (Q * Rr))
        mx = max(lbs) if lbs else 0.0
        am = (lbs.index(mx) + 1) if lbs else 0
        rows.append((Rr, d, mx, am, abs(full), fm))
        rel = d / abs(full) if abs(full) > 1e-12 else float('nan')
        print(f"{Rr:>8} {Q*Rr:>9} {d:>10.6f} {mx:>10.6f} {am:>4} "
              f"{abs(full):>9.6f} {fm:>9.6f} {rel:>11.6f} "
              f"{(fm-model)/2:>9.6f}", file=out)
    print(file=out, flush=True)
    return rows, model, c4


def band_case(b, m, p, q, P, nmax):
    t = m / b
    Q = primorial_le(P)
    R = max(8, nmax // Q)
    N = Q * R
    limit = max(p, q) * N + 64
    Rlist = sorted({max(4, R // 4), max(4, R // 2), R})
    ys = [P, 5, 11, 31, 101, 1009, 10007, 100003, limit]
    print(f"b={b} m={m} p={p} q={q} P={P} Q={Q}  N={N}  (y = {limit} is the full remainder)")
    print(f"{'y':>9} " + " ".join(f"{'d(R='+str(x)+')':>13}" for x in Rlist)
          + f" {'maxLB(Rmax)':>12}")
    for y in ys:
        if y < P:
            continue
        om = omega_sieve(limit, P, None if y >= limit else y)
        T = tail_array(om, b, limit)
        Bv = [cmath.exp(1j * TWOPI * t * (T[p * n] - T[q * n])) for n in range(N)]
        cells = []
        mx = 0.0
        for Rr in Rlist:
            d, _, _, lbs = defect_and_lb(Bv, Q, Rr)
            cells.append(d)
            if Rr == Rlist[-1] and lbs:
                mx = max(lbs)
        lbl = "all" if y >= limit else str(y)
        print(f"{lbl:>9} " + " ".join(f"{c:>13.6f}" for c in cells) + f" {mx:>12.6f}",
              flush=True)
    print()


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
    ap.add_argument("--bands", action="store_true",
                    help="decompose the defect by prime band (P, y]: CRT handles every fixed y, "
                         "so the y -> oo limit is the whole content.")
    ap.add_argument("--degen", action="store_true",
                    help="the DEGENERATE pairs p == q mod primorialLe P, where "
                         "prod_{r<=P} pairLocalFactor = 1 EXACTLY "
                         "(pairDefect_eq_classDev_of_congr): the split is vacuous there and "
                         "pairDefect is the RAW class deviation of the pair correlation.")
    args = ap.parse_args()
    if args.selftest:
        sys.exit(selftest())
    if args.bands:
        print("=" * 102)
        print("BAND DECOMPOSITION.  B_y(n) = e(t * sum_{k>=1}(om_{(P,y]}(pn+k) - om_{(P,y]}(qn+k))/b^k):")
        print("the pair remainder restricted to primes in (P, y].  For FIXED y this is a function of")
        print("finitely many residues n mod r, r <= y, all coprime to Q, so CRT PROVES its class")
        print("deviation is O(y/R) -> 0.  The whole content of `PairDecouple` is therefore the")
        print("y -> oo limit.  If the defect saturates at moderate y, the large primes carry no")
        print("class bias and PairDecouple is true for the CRT reason.")
        print("=" * 102)
        for (b, m, p, q, P, nmax) in [(3, 1, 3, 5, 2, 200000), (3, 1, 5, 11, 3, 150000)]:
            band_case(b, m, p, q, P, nmax)
        return
    if args.degen:
        print("=" * 102)
        print("DEGENERATE pairs: p == q mod primorialLe P, so |periodMean A| = 1 EXACTLY and")
        print("pairDefect is the raw class deviation of f.  The sharpest place for a "
              "counterexample.")
        print("=" * 102)
        # (b, m, p, q, P, nmax)   -- q large, so nmax is capped by the sieve limit q*N
        dcases = [
            (3, 1, 3, 5, 2, 200000),      # 5 - 3 = 2  = primorialLe 2
            (3, 1, 5, 7, 2, 200000),
            (3, 1, 5, 11, 3, 150000),     # 11 - 5 = 6  = primorialLe 3
            (3, 1, 7, 13, 3, 150000),
            (3, 1, 11, 17, 3, 100000),
            (4, 1, 5, 11, 3, 150000),
            (3, 2, 5, 11, 3, 150000),
            (3, 1, 7, 37, 5, 60000),      # 37 - 7 = 30 = primorialLe 5
            (3, 1, 11, 41, 5, 60000),
            (3, 1, 11, 431, 7, 10500),    # 431 - 11 = 420 = 2 * primorialLe 7
        ]
        for (b, m, p, q, P, nmax) in dcases:
            Q = primorial_le(P)
            Rmax = max(8, nmax // Q)
            Rlist = sorted({max(4, Rmax // 8), max(4, Rmax // 4),
                            max(4, Rmax // 2), Rmax})
            try:
                run_case(b, m, p, q, P, Rlist)
            except AssertionError as e:
                print(f"b={b} m={m} p={p} q={q} P={P}: {e}", flush=True)
        return

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
