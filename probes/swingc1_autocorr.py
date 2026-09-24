#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.10"
# ///
"""Probe: does G4_b = sum_m omega(m) b^{-m} satisfy the SwingC1 leaf `HAutoCorr`?

Leaf (SwingC1.lean, `HAutoCorr`): with T(n) = sum_{m<=n} omega(m) + c_n and
zeta = exp(2*pi*i/(b-1)), for every 0 < j < b-1 and every L,

    (1/N) sum_{n<N} zeta^{j (T(n+L) - T(n)))}  ->  b^{-L}.

Equivalently T(n+L)-T(n) = d_{n+1}+...+d_{n+L} mod (b-1) where d are the base-b
digits of G4_b, so this is the digit-sum-mod-(b-1) law.  The probe also computes
the NAIVE omega-only correlation (carry deleted), which the refutation
`not_hAutoCorr_of_carryNegligible` says must NOT agree: it should go to 0.
"""
import cmath

N = 400000
DEPTH = 64


def omega_sieve(limit):
    w = [0] * (limit + 1)
    for p in range(2, limit + 1):
        if w[p] == 0:
            for m in range(p, limit + 1, p):
                w[m] += 1
    return w


def carries(b, w, N, depth):
    """c_n = floor(sum_{k>=1} w(n+k) b^{-k}), exact for depth beyond digit reach."""
    c = [0] * (N + 1)
    for n in range(N, -1, -1):
        acc = 0
        for k in range(depth, 0, -1):
            m = n + k
            acc = (w[m] if m < len(w) else 0) + acc // b
        # acc//b is floor of the tail sum
        c[n] = acc // b
    return c


def run(b, Ls=(1, 2, 3)):
    lim = N + DEPTH + 2
    w = omega_sieve(lim)
    c = carries(b, w, N + max(Ls) + 1, DEPTH)
    q = b - 1
    S = [0] * (N + max(Ls) + 2)
    for m in range(1, len(S)):
        S[m] = S[m - 1] + (w[m] if m < len(w) else 0)
    T = [(S[n] + c[n]) % q for n in range(N + max(Ls) + 1)]
    out = {}
    for j in range(1, q):
        z = cmath.exp(2j * cmath.pi * j / q)
        for L in Ls:
            tot = sum(z ** ((T[n + L] - T[n]) % q) for n in range(N)) / N
            tot_om = sum(z ** ((S[n + L] - S[n]) % q) for n in range(N)) / N
            out[(j, L)] = (tot, tot_om, b ** (-L))
    return out


def known_answer_check():
    """Hand-computed: omega(1..12) = 0,1,1,1,1,2,1,1,1,2,1,2."""
    w = omega_sieve(12)
    assert w[1:13] == [0, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2], w[1:13]
    # base 3, G4_3 = 0.(0)(1)(1)(1)(1)(2)(1)... in base-3 "digits" before carrying.
    # Hand carry, positions 6..1 with tail 0 beyond 12 (omega<=2 here so no
    # runaway): value at position 6 is 2, 2<3 so d6=2, c6=0; position 5: 1+0=1
    # -> d5=1, c5=0; likewise d4=d3=d2=1, c=0; d1=0... check against carries().
    c = carries(3, w, 6, 6)
    assert all(x == 0 for x in c), c
    d = [(w[n + 1] + c[n + 1] - 3 * c[n]) for n in range(6)]
    assert d == [0, 1, 1, 1, 1, 2], d
    print("known-answer check OK: omega(1..12) and the base-3 digits 0,1,1,1,1,2")


if __name__ == "__main__":
    known_answer_check()
    for b in (3, 4, 10):
        print(f"\n=== b = {b}  (N = {N}) ===")
        for (j, L), (tot, tot_om, pred) in sorted(run(b).items()):
            print(f"  j={j} L={L}: corr = {tot.real:+.5f}{tot.imag:+.5f}i   "
                  f"|corr| = {abs(tot):.5f}   predicted b^-L = {pred:.5f}   "
                  f"omega-only |.| = {abs(tot_om):.5f}")


def carry_activation(bmax=12):
    """The carry c_n in base b is IDENTICALLY ZERO until omega reaches b.

    sum_{k>=1} omega(n+k) b^{-k} < 1 as soon as omega <= b-2 on the tail, and
    omega(m) >= t first happens at the t-th primorial.  So base-b carrying only
    switches on around the b-th primorial -- astronomically far out for b >= 8.
    """
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
    prim = 1
    rows = []
    for t in range(1, bmax + 1):
        prim *= primes[t - 1]
        rows.append((t, prim))
    print("\n=== carry activation: least m with omega(m) = t is the t-th primorial ===")
    for t, prim in rows:
        print(f"  omega(m) = {t:2d} first at m = {prim:,}"
              f"   -> base b = {t} carrying is inert below this")
    return rows


def marginal_control(b=3, NMAX=4_000_000, depth=48, seed=11):
    """**The correct control for C1 numerics**, and a FALSE-ALARM guard.

    At b = 3 the digit frequencies of G4_3 are nowhere near (1/3,1/3,1/3) at
    reachable N: at N = 4e6 they are about (0.325, 0.386, 0.289), and
    mean_n (-1)^{d_{n+1}} sits near 0.23 against the predicted 1/3, stable over
    2.5 decades.  Read naively that looks like a REFUTATION of ConjC1.  It is not.

    The control: block-shuffle omega within dyadic blocks (destroying all
    arithmetic correlations while preserving the local marginal), or resample iid
    from omega's own marginal.  Both controls have uniform digits in the limit --
    the resulting number is a.s. normal -- so their column MUST tend to 1/3.  It
    doesn't either: it sits near 0.27.  So ~3/4 of the apparent deficit is a
    finite-N artefact of omega's MARGINAL (mean omega is only ~2.95 at m ~ 4e6,
    far too small to spread evenly mod 3), not of arithmetic structure.  The
    genuine arithmetic residue is the real-minus-control gap, ~ -0.040, and both
    columns rise together past N = 1e6.

    Moral: never compare C1 numerics against the uniform-digit model directly.
    Compare against the same-marginal random model, which carries the identical
    finite-N bias.
    """
    import random
    lim = NMAX + depth + 10
    w = omega_sieve(lim)
    random.seed(seed)
    w2 = w[:]
    lo = 2
    while lo < len(w2):
        hi = min(2 * lo, len(w2))
        blk = w2[lo:hi]
        random.shuffle(blk)
        w2[lo:hi] = blk
        lo = hi
    assert sorted(w2[2:]) == sorted(w[2:]), "shuffle must preserve the multiset"

    def digits(ws):
        c = carries(b, ws, NMAX + 5, depth)
        return [(ws[n + 1] + c[n + 1] - b * c[n]) for n in range(NMAX)]

    dr, ds = digits(w), digits(w2)
    assert all(0 <= x < b for x in dr), "carrying must produce base-b digits"
    print(f"\n=== marginal control, b = {b} (the shuffled column MUST tend to 1/3) ===")
    print("    N      real mean   shuffled mean   avg omega   gap(real-shuf)")
    for N in [10**5, 3 * 10**5, 10**6, 2 * 10**6, NMAX]:
        mr = sum((-1) ** x for x in dr[:N]) / N
        ms = sum((-1) ** x for x in ds[:N]) / N
        aw = sum(w[2:N + 2]) / N
        print(f"{N:>9}  {mr:+.5f}     {ms:+.5f}      {aw:.3f}       {mr - ms:+.5f}")
    print("  prediction 0.33333")


if __name__ == "__main__":
    carry_activation()
    marginal_control()
    print("""
VERDICT (2026-09-24).  This probe CANNOT test `HAutoCorr` numerically, and that
is the deliverable:

* b = 10 (and every b >= 8) is PRE-ASYMPTOTIC at any reachable N.  omega(m) <= 7
  for all m < 9,699,690, so sum_k omega(n+k)/10^k < 1 and the carry c_n is
  IDENTICALLY 0: the digits of G4_10 literally ARE omega(m).  Base-10 carrying
  only switches on near the 10th primorial, m ~ 6.5e9.  Hence the b=10 rows
  above coincide exactly with the omega-only rows and measure Delange's theorem
  (mean -> 0), NOT the leaf's b^{-L}.  They are not evidence against C1.
* b = 3, 4 do exercise the carry (omega(m) >= 3 already at m = 30).  There the
  correlations are the right ORDER and decay like b^{-L} (b=3: 0.224, 0.054,
  0.016 against 1/3, 1/9, 1/27; successive ratios 4.2, 3.3 vs 3) but sit off the
  predicted constant by a factor ~0.5-2.  That is expected: equidistribution of
  omega mod q has (log N)^{-c} discrepancy, so N = 4e5 gives ~one digit.
* CONCLUSION: no computation at feasible N separates `HAutoCorr` from its
  negation.  C1 must be settled structurally.  In particular the apparent
  "counterexample" at large b is exactly the inertness of carrying below the
  b-th primorial, and `not_hAutoCorr_of_carryNegligible` in SwingC1.lean says
  what that means: on the initial stretch where c_n = 0 the correlation follows
  Delange to 0, so ALL of the leaf's b^{-L} is produced by the tail where omega
  exceeds b.  The asymptotic regime is invisible to experiment.
""")
