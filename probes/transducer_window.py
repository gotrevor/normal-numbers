#!/usr/bin/env -S uv run --quiet --with mpmath python3
"""
Route A probe -- does the phi*x continued-fraction transducer keep its REAL-PLACE
state in a compact bounded-distortion window, and does it lose memory?

Vandehey 2017 Sec.7 problem 1: x CF-normal, q,r quadratic irrational, q != 0
  =>  is qx + r CF-normal?
Vandehey's own theorem (q, r rational) rides on the transducer's state set being
FINITE: entries are integers with |entry| <= D, so bounded => finitely many.
Over Z[phi] that certificate dies -- Dirichlet's unit theorem gives infinitely
many units (+-phi^n), and Z[phi] is dense in R, so "bounded" no longer means
"finite".  The attack map's Route A replaces finiteness by COMPACTNESS: the
emission rule reads only the REAL embedding of the state, which evolves
autonomously, so the conjugate place may drift off to infinity while the real
place recurs to a compact window W of bounded-distortion Moebius maps.

That is a checkable claim about a concrete dynamical system.  This probe checks it:

  (W) window     -- distortion of the post-emission real-place state over time.
                    Bounded, with no drift between the first and second half of
                    a run, = recurrence to a compact window.
  (C) place split -- log|entries| at the real and conjugate places, which is the
                    "compact fiber" thesis made directly visible.
  (M) merging    -- two different initial states, same input digit stream: do
                    they converge?  Reported both as exact state coincidence and
                    as contraction in the Hilbert projective metric, which is the
                    form Route A actually needs (Birkhoff-Hopf).

ARITHMETIC NOTE, and it is the whole ballgame: the real-place value of p + q*phi
is a near-total cancellation of two huge integers (that IS what "real place stays
bounded while the conjugate drifts" means).  At 1000 input digits the entries
reach ~10^200 while their real embedding stays O(1), so ANY fixed-precision float
measures pure rounding noise -- and it fails in the direction that looks like a
refutation.  Every comparison, floor and sign below is therefore exact integer
arithmetic in Z[phi]; floats appear only in the final reported magnitudes, via a
bracket whose precision scales with the operands.
"""
import argparse, math, random, sys
from math import isqrt

# ---------------------------------------------------------------- Z[phi] exact
# phi = (1+sqrt5)/2,  phi^2 = phi + 1.  z = p + q*phi is stored as (p, q).
# For sign/floor work we use  2z = A + B*sqrt5  with  A = 2p + q,  B = q.

class Z:
    __slots__ = ("p", "q")
    def __init__(s, p=0, q=0): s.p, s.q = p, q
    def __add__(s, o): return Z(s.p + o.p, s.q + o.q)
    def __sub__(s, o): return Z(s.p - o.p, s.q - o.q)
    def __neg__(s):    return Z(-s.p, -s.q)
    def __mul__(s, o):
        a, b, c, d = s.p, s.q, o.p, o.q
        return Z(a * c + b * d, a * d + b * c + b * d)      # phi^2 = phi + 1
    def __eq__(s, o):  return s.p == o.p and s.q == o.q
    def __hash__(s):   return hash((s.p, s.q))
    def ab(s):         return (2 * s.p + s.q, s.q)          # 2z = A + B sqrt5
    def __repr__(s):   return f"({s.p}{s.q:+}phi)"

ZERO, ONE, PHI_Z = Z(0, 0), Z(1, 0), Z(0, 1)
def zint(n): return Z(n, 0)


def sign_ab(A, B):
    """exact sign of A + B*sqrt5 (A, B integers). sqrt5 irrational => zero only at A=B=0."""
    if A == 0 and B == 0: return 0
    if A >= 0 and B >= 0: return 1
    if A <= 0 and B <= 0: return -1
    if A > 0:  return 1 if A * A > 5 * B * B else -1        # B < 0
    return 1 if 5 * B * B > A * A else -1                   # A < 0, B > 0

def zsign(z):
    A, B = z.ab(); return sign_ab(A, B)

def _bracket(A, B, R):
    """integer n0 with n0 <= (A + B*sqrt5)/R  (R > 0), within 1 of the true floor"""
    if B >= 0: lo = A + isqrt(5 * B * B)
    else:      lo = A - isqrt(5 * B * B) - 1
    return lo // R

def zdiv_floor(num, den):
    """exact floor(num/den) for num, den in Z[phi], den != 0.  None if den == 0."""
    sd = zsign(den)
    if sd == 0: return None
    if sd < 0: num, den = -num, -den
    A1, B1 = num.ab(); A2, B2 = den.ab()          # num/den = (A1+B1 r5)/(A2+B2 r5)
    R = A2 * A2 - 5 * B2 * B2                     # rationalise
    P = A1 * A2 - 5 * B1 * B2
    Q = B1 * A2 - A1 * B2
    if R < 0: P, Q, R = -P, -Q, -R
    n = _bracket(P, Q, R)
    # exact correction:  n <= v  <=>  sign(P - nR + Q sqrt5) >= 0
    while sign_ab(P - (n + 1) * R, Q) >= 0: n += 1
    while sign_ab(P - n * R, Q) < 0:        n -= 1
    return n

def log10_abs(z):
    """log10 |p + q*phi|, exact-bracketed so cancellation cannot corrupt it."""
    A, B = z.ab()
    if A == 0 and B == 0: return float("-inf")
    k = max(B.bit_length(), A.bit_length()) // 3 + 40       # precision scales with operands
    D = 10 ** k
    N = A * D + (B * isqrt(5 * D * D) if B >= 0 else -((-B) * isqrt(5 * D * D)))
    N = abs(N)
    if N == 0: return float("-inf")
    b = N.bit_length()
    if b <= 900: base = math.log10(N)
    else:        base = math.log10(N >> (b - 900)) + (b - 900) * math.log10(2)
    return base - k - math.log10(2)

def _log10_ab(A, B):
    if A == 0 and B == 0: return float("-inf")
    k = max(abs(B).bit_length(), abs(A).bit_length()) // 3 + 40
    D = 10 ** k
    S = isqrt(5 * D * D)
    N = abs(A * D + (B * S if B >= 0 else -((-B) * S)))
    if N == 0: return float("-inf")
    b = N.bit_length()
    base = math.log10(N) if b <= 900 else math.log10(N >> (b - 900)) + (b - 900) * math.log10(2)
    return base - k - math.log10(2)


# ---------------------------------------------------------------- transducer

class Mat:
    """[[a,b],[c,d]] over Z[phi] as the Moebius map t -> (a t + b)/(c t + d)."""
    __slots__ = ("a", "b", "c", "d")
    def __init__(s, a, b, c, d): s.a, s.b, s.c, s.d = a, b, c, d
    def __mul__(s, o):
        return Mat(s.a * o.a + s.b * o.c, s.a * o.b + s.b * o.d,
                   s.c * o.a + s.d * o.c, s.c * o.b + s.d * o.d)
    def det(s): return s.a * s.d - s.b * s.c
    def entries(s): return (s.a, s.b, s.c, s.d)
    def same(s, o): return s.a == o.a and s.b == o.b and s.c == o.c and s.d == o.d

def digit_mat(a): return Mat(zint(a), ONE, ONE, ZERO)
def emit_mat(q):  return Mat(ZERO, ONE, ONE, zint(-q))

class Transducer:
    def __init__(s, M): s.M = M; s.out = []

    def _emittable(s):
        """floor(M(t)) if it is the SAME integer >= 1 for every tail t in (1, inf).
        M(1) = (a+b)/(c+d), M(inf) = a/c; both computed exactly."""
        M = s.M
        f1 = zdiv_floor(M.a + M.b, M.c + M.d)
        fi = zdiv_floor(M.a, M.c)
        if f1 is None or fi is None: return None
        if f1 != fi or f1 < 1: return None
        return f1

    def step(s, a):
        s.M = s.M * digit_mat(a)
        got = []
        while True:
            q = s._emittable()
            if q is None: break
            s.M = emit_mat(q) * s.M
            s.out.append(q); got.append(q)
            if len(got) > 256: break
        return got


# ---------------------------------------------------------------- measurement

def distortion(M):
    """-log10( |det| / max|entry|^2 ) at the real place, scale-invariant.
    0 = perfectly non-degenerate; large = the projectivised map is collapsing
    toward singular, i.e. the state is leaving any compact bounded-distortion
    window.  A run that stays flat is a state recurring inside a compact W."""
    ls = [log10_abs(e) for e in M.entries()]
    m = max(ls)
    if m == float("-inf"): return float("inf")
    return 2 * m - log10_abs(M.det())

def place_split(M):
    r = max(log10_abs(e) for e in M.entries())
    A_B = [e.ab() for e in M.entries()]
    c = max(_log10_ab(A, -B) for A, B in A_B)
    return r, c

def hilbert_gap(M, N):
    """Hilbert projective distance between the two states' first columns,
    log-scale.  Birkhoff-Hopf contraction => this decays to 0."""
    def col(X): return (X.a, X.c)
    a1, c1 = col(M); a2, c2 = col(N)
    try:
        r1 = log10_abs(a1) - log10_abs(c1)
        r2 = log10_abs(a2) - log10_abs(c2)
    except Exception:
        return float("nan")
    return abs(r1 - r2)


# ---------------------------------------------------------------- input stream

def cf_digits_of_random_real(nbits=8000, cap=None):
    """CF digits of a random rational with ~nbits numerator/denominator.  Partial
    quotients of random rationals follow Gauss-Kuzmin WITH the true dependence
    structure, so this is a faithful Gauss-distributed CF stream (better than
    i.i.d. sampling from the Gauss-Kuzmin law, where digits are independent)."""
    p = random.getrandbits(nbits) | 1
    q = random.getrandbits(nbits) | 1
    if p < q: p, q = q, p
    out = []
    while q and (cap is None or len(out) < cap):
        a, r = divmod(p, q)
        out.append(a); p, q = q, r
    return out[1:]


# ---------------------------------------------------------------- self-test

def selftest():
    """Teeth, red-then-green, against an INDEPENDENT high-precision computation."""
    try:
        from mpmath import mp, mpf, sqrt as mpsqrt, floor as mpfloor
    except ImportError:
        print("  self-test SKIPPED (mpmath absent)"); return True
    mp.dps = 400
    random.seed(7)
    digs = cf_digits_of_random_real(nbits=2000, cap=300)
    x = mpf(0)
    for a in reversed(digs[:150]): x = 1 / (mpf(a) + x)
    x = 1 / x
    phi = (1 + mpsqrt(5)) / 2
    ref, t = [], phi * x
    for _ in range(60):
        f = int(mpfloor(t)); ref.append(f); t = t - f
        if t == 0: break
        t = 1 / t

    T = Transducer(Mat(PHI_Z, ZERO, ZERO, ONE))
    for a in digs[:150]: T.step(a)
    n = min(len(ref), len(T.out), 40)
    ok = ref[:n] == T.out[:n]
    print(f"  self-test green : first {n} emitted digits of phi*x match reference -> {ok}")
    if not ok:
        print(f"    ref {ref[:n]}\n    got {T.out[:n]}"); return False

    W = Transducer(Mat(zint(2), ZERO, ZERO, ONE))          # 2x, deliberately wrong
    for a in digs[:150]: W.step(a)
    bad = ref[:n] == W.out[:n]
    print(f"  self-test red   : wrong map (2x) reproduces them -> {bad} (want False)")

    # emission must KEEP UP: output length comparable to input, not stalling
    rate = len(T.out) / 150
    print(f"  self-test rate  : {len(T.out)} digits out of 150 in  (ratio {rate:.2f}, want > 0.5)")
    return ok and not bad and rate > 0.5


# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=8)
    ap.add_argument("--digits", type=int, default=600)
    ap.add_argument("--seed", type=int, default=20260825)
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--stage2", action="store_true")
    ap.add_argument("--stage3", action="store_true")
    ap.add_argument("--samples", type=int, default=120)
    ap.add_argument("--steps", type=int, default=120)
    a = ap.parse_args()

    print("=" * 84)
    print("Route A probe -- phi*x CF transducer: compact window + loss of memory")
    print("=" * 84)
    if not selftest():
        print("\nSELF-TEST FAILED - every measurement below would be meaningless."); sys.exit(1)
    if a.selftest: return
    if a.stage2:
        stage2(a.runs, a.digits, a.seed); return
    if a.stage3:
        stage3(a.samples, a.steps, a.seed); return
    random.seed(a.seed)

    print(f"\n(W) WINDOW + (C) PLACE SPLIT   {a.runs} runs x {a.digits} input digits")
    print(f"{'run':>4} {'in':>5} {'out':>5} | {'distortion  1st-half med':>24} {'2nd-half med':>13}"
          f" {'max':>7} | {'log|e| real':>12} {'conj':>9}")
    firsts, seconds, maxima = [], [], []
    for k in range(a.runs):
        digs = cf_digits_of_random_real(nbits=a.digits * 8, cap=a.digits)
        T, tr = Transducer(Mat(PHI_Z, ZERO, ZERO, ONE)), []
        for d in digs:
            T.step(d)
            if zsign(T.M.c) != 0: tr.append(distortion(T.M))
        if not tr: continue
        h = len(tr) // 2
        f_, s_ = sorted(tr[:h]), sorted(tr[h:])
        fm, sm = f_[len(f_)//2], s_[len(s_)//2]
        firsts.append(fm); seconds.append(sm); maxima.append(max(tr))
        lr, lc = place_split(T.M)
        print(f"{k:>4} {len(digs):>5} {len(T.out):>5} | {fm:>24.3f} {sm:>13.3f} {max(tr):>7.3f}"
              f" | {lr:>12.2f} {lc:>9.2f}")

    print(f"\n  median distortion  first half {sum(firsts)/len(firsts):8.3f}"
          f"   second half {sum(seconds)/len(seconds):8.3f}   (drift => escaping W)")
    print(f"  worst distortion over all runs {max(maxima):.3f}")

    print(f"\n(M) MERGING   different initial states (phi*x + r), same input stream")
    print(f"{'run':>4} {'r':>3} | {'states coincide at':>19} {'common output suffix':>21}"
          f" {'Hilbert gap: start':>19} {'end':>9}")
    coincide = 0
    for k in range(a.runs):
        digs = cf_digits_of_random_real(nbits=a.digits * 8, cap=a.digits)
        A_ = Transducer(Mat(PHI_Z, ZERO,       ZERO, ONE))
        B_ = Transducer(Mat(PHI_Z, zint(1 + k), ZERO, ONE))
        at, g0, gl = None, None, None
        for i, d in enumerate(digs):
            A_.step(d); B_.step(d)
            if zsign(A_.M.c) != 0 and zsign(B_.M.c) != 0:
                g = hilbert_gap(A_.M, B_.M)
                if g0 is None: g0 = g
                gl = g
            if at is None and A_.M.same(B_.M): at = i
        suf = 0
        while suf < min(len(A_.out), len(B_.out)) and A_.out[-1-suf] == B_.out[-1-suf]: suf += 1
        coincide += at is not None
        print(f"{k:>4} {1+k:>3} | {str(at):>19} {suf:>21} "
              f"{(g0 if g0 is not None else float('nan')):>19.3f} {(gl if gl is not None else float('nan')):>9.3f}")
    print(f"\n  exact state coincidence in {coincide}/{a.runs} runs")




# ================================================================ stage 2
# The stage-1 merging test starts B from phi*x + r with r an INTEGER, which is
# the easy case (integer shifts are already handled downstream by
# isCFNormal_add_nat).  The claim Route A actually needs is merging from
# ARBITRARY states reachable in W, and for q, r both quadratic irrational.

def reachable_state(nbits, cap, warmup, M0):
    """Run the transducer on a private prefix so its state is a generic point of W."""
    T = Transducer(M0)
    for d in cf_digits_of_random_real(nbits=nbits, cap=cap)[:warmup]:
        T.step(d)
    return T.M

def stage2(runs, digits, seed):
    random.seed(seed)
    print("\n" + "=" * 84)
    print("STAGE 2 -- merging from arbitrary reachable states; excursion tail")
    print("=" * 84)

    print(f"\n(M2) MERGING FROM GENERIC STATES OF W  (both sides warmed on private prefixes)")
    print(f"{'run':>4} | {'coincide at':>12} {'Hilbert gap start':>18} {'end':>10} {'common out suffix':>18}")
    coin, ends = 0, []
    for k in range(runs):
        MA = reachable_state(digits * 8, digits, 60 + 7 * k, Mat(PHI_Z, ZERO, ZERO, ONE))
        MB = reachable_state(digits * 8, digits, 40 + 11 * k, Mat(PHI_Z, PHI_Z, ZERO, ONE))
        A_, B_ = Transducer(MA), Transducer(MB)
        shared = cf_digits_of_random_real(nbits=digits * 8, cap=digits)
        at, g0, gl = None, None, None
        for i, d in enumerate(shared):
            A_.step(d); B_.step(d)
            if zsign(A_.M.c) != 0 and zsign(B_.M.c) != 0:
                g = hilbert_gap(A_.M, B_.M)
                if g0 is None: g0 = g
                gl = g
            if at is None and A_.M.same(B_.M): at = i
        suf = 0
        while suf < min(len(A_.out), len(B_.out)) and A_.out[-1-suf] == B_.out[-1-suf]: suf += 1
        coin += at is not None; ends.append(gl if gl is not None else float("nan"))
        print(f"{k:>4} | {str(at):>12} {(g0 or 0):>18.4f} {(gl if gl is not None else float('nan')):>10.6f} {suf:>18}")
    print(f"\n  exact state coincidence in {coin}/{runs} runs from generic W states")

    print(f"\n(Q) QUADRATIC-IRRATIONAL SHIFT  x -> phi*x + phi   (the real problem's shape)")
    print(f"{'run':>4} {'in':>5} {'out':>5} | {'distortion med':>15} {'max':>7} | {'log|e| real':>12} {'conj':>9}")
    for k in range(runs):
        digs = cf_digits_of_random_real(nbits=digits * 8, cap=digits)
        T, tr = Transducer(Mat(PHI_Z, PHI_Z, ZERO, ONE)), []
        for d in digs:
            T.step(d)
            if zsign(T.M.c) != 0: tr.append(distortion(T.M))
        if not tr: continue
        ts = sorted(tr); lr, lc = place_split(T.M)
        print(f"{k:>4} {len(digs):>5} {len(T.out):>5} | {ts[len(ts)//2]:>15.3f} {ts[-1]:>7.3f}"
              f" | {lr:>12.2f} {lc:>9.2f}")

    print(f"\n(E) EXCURSION TAIL  --  P(distortion > t), pooled")
    pool = []
    for k in range(runs):
        digs = cf_digits_of_random_real(nbits=digits * 8, cap=digits)
        T = Transducer(Mat(PHI_Z, ZERO, ZERO, ONE))
        for d in digs:
            T.step(d)
            if zsign(T.M.c) != 0: pool.append(distortion(T.M))
    pool.sort(); n = len(pool)
    print(f"  n = {n}")
    print(f"  {'t':>6} {'P(D>t)':>12} {'-log10 P':>10}")
    prev = None
    for t in (1, 2, 3, 4, 5, 6, 7, 8, 10, 12):
        cnt = sum(1 for v in pool if v > t)
        p = cnt / n
        rate = "" if prev is None or p == 0 or prev == 0 else f"   ratio/prev {p/prev:6.3f}"
        print(f"  {t:>6} {p:>12.5f} {(-math.log10(p) if p else float('inf')):>10.2f}{rate}")
        prev = p
    print("  (geometric decay in the ratio column = exponential tail = Doeblin-friendly;")
    print("   a fattening ratio would be the heavy tail that threatens uniform merging)")




# ================================================================ stage 3
# CORRECTION to (M2).  Testing whether two states driven by the SAME input become
# EQUAL is the wrong test, and it cannot succeed for structural reasons: with
# M_n = L_n . M_0 . P_n (L_n the emitted digits, P_n the common ingested ones),
# equality forces (L^B)^-1 L^A = M_0^B (M_0^A)^-1, i.e. the two starts must differ
# by an element of the emission subgroup.  Integer shifts do (stage 1: coincided
# in 1-2 steps, 8/8); generic elements of GL_2(Z[phi]) do not.  Nothing dynamical
# is being measured there.
#
# What Vandehey's argument actually needs is a Doeblin condition ON THE CHAIN:
# the DISTRIBUTION of the state after n steps forgets where it started, over
# random input.  That is what this stage measures -- two different initial
# states, many independent input streams each, compared as distributions.

def zfloat(z):
    s = zsign(z)
    if s == 0: return 0.0
    lg = log10_abs(z)
    if lg < -300: return 0.0
    if lg > 300:  return s * float("inf")
    return s * (10.0 ** lg)

def state_coord(M):
    """A bounded coordinate on W: the post-state's image interval endpoints,
    mapped into (0,1) by t -> 1/t.  Returns None when undefined."""
    d1, d2 = M.c + M.d, M.c
    if zsign(d1) == 0 or zsign(d2) == 0: return None
    lo = zfloat(M.a + M.b) / zfloat(d1)          # M(1)
    hi = zfloat(M.a) / zfloat(d2)                # M(inf)
    if lo <= 0 or hi <= 0: return None
    u, v = 1.0 / lo, 1.0 / hi
    if not (0 < u < 1e6 and 0 < v < 1e6): return None
    return (min(u, v), max(u, v))

def ks(xs, ys):
    xs, ys = sorted(xs), sorted(ys)
    i = j = 0; d = 0.0
    nx, ny = len(xs), len(ys)
    while i < nx and j < ny:
        if xs[i] <= ys[j]: i += 1
        else: j += 1
        d = max(d, abs(i / nx - j / ny))
    return d

def stage3(samples, steps, seed):
    random.seed(seed)
    print("\n" + "=" * 84)
    print("STAGE 3 -- Doeblin test: does the STATE DISTRIBUTION forget its start?")
    print("=" * 84)
    starts = {
        "phi*x"        : Mat(PHI_Z, ZERO,       ZERO, ONE),
        "phi*x + phi"  : Mat(PHI_Z, PHI_Z,      ZERO, ONE),
        "phi*x + 3"    : Mat(PHI_Z, zint(3),    ZERO, ONE),
        "(phi x+1)/(x+phi)": Mat(PHI_Z, ONE,    ONE,  PHI_Z),
    }
    print(f"  {samples} independent input streams per start, state read after {steps} steps\n")
    coords = {}
    for name, M0 in starts.items():
        us, vs = [], []
        for _ in range(samples):
            digs = cf_digits_of_random_real(nbits=steps * 12, cap=steps)
            T = Transducer(M0)
            for d in digs[:steps]: T.step(d)
            c = state_coord(T.M)
            if c: us.append(c[0]); vs.append(c[1])
        coords[name] = (us, vs)
        us_s = sorted(us)
        print(f"  {name:<20} n={len(us):>4}  median u={us_s[len(us_s)//2]:.4f}"
              f"  IQR=[{us_s[len(us_s)//4]:.4f},{us_s[3*len(us_s)//4]:.4f}]")

    names = list(starts)
    print(f"\n  pairwise Kolmogorov-Smirnov distance between start-conditioned state distributions:")
    print(f"  {'':<22}" + "".join(f"{n:>20}" for n in names[1:]))
    crit = 1.36 * math.sqrt(2 / samples)          # ~5% critical value, two-sample
    worst = 0.0
    for i, a in enumerate(names[:-1]):
        row = f"  {a:<22}"
        for b in names[i+1:]:
            d = ks(coords[a][0], coords[b][0]); worst = max(worst, d)
            row += f"{d:>20.4f}"
        print(row)
    print(f"\n  worst KS = {worst:.4f}   5%-critical ~ {crit:.4f}"
          f"   -> {'INDISTINGUISHABLE' if worst < crit else 'DISTINGUISHABLE'}")
    print("  (indistinguishable = the chain on W has forgotten its initial state:")
    print("   the Doeblin/merging condition Route A needs, in its correct form)")


if __name__ == "__main__":
    main()
