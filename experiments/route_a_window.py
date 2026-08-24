#!/usr/bin/env -S uv run --quiet python3
"""Route A crux probe: does the phi*x CF transducer keep a COMPACT projectivized state?

Context: papers/vandehey-2017-open-problem-attack-map.md section 3 ("Route A: Vandehey
with a COMPACT fiber").  Vandehey 2017 proves: M an integer matrix, det != 0, x CF-normal
=> Mx CF-normal.  The engine is a finite-state transducer; the state set M_D is FINITE
only because an integer matrix with |det| = D has bounded entries.  For q, r in Z[phi] the
same transducer runs verbatim (the digit matrices A_j are integer, hence self-conjugate,
so the state stays in Z[phi] and det stays a fixed unit), but Z[phi] is dense in R:
bounded real embedding no longer implies finiteness.

Route A's bet: finiteness was only a CERTIFICATE.  The update rule and the emission rule
read ONLY the real embedding, so compactness of the closure W of the post-emission states
in PGL2(R) should suffice.  This script measures that bet, plus the loss-of-memory claim.

Everything that drives a decision is EXACT integer arithmetic in Z[phi] (u + v*phi with
u, v in Z); floats appear only in reported statistics.

Conventions (match the pin note papers/vandehey-2017-matrix-actions-cf-normality.md):
  x = [0; a1, a2, ...],  A_a = [[0,1],[1,a]],  so x = A_{a1}(T x),  T = Gauss map.
  Full state after n inputs:      S_n = M A_{a1} ... A_{an},   Mx = S_n(T^n x).
  Residual (post-emission) state: G_n = A_{b_m}^-1 ... A_{b_1}^-1 S_n,   b = output digits.
  Emit c as soon as G([0,1]) lies inside the cylinder [1/(c+1), 1/c]; then G <- A_c^-1 G.
  Invariant after the integer-part step: G maps [0,1] into [0,1].

Statistics, and what each one is for:
  lognorm_real  log||G||/sqrt|det|  -- THE headline.  Bounded <=> state stays in a compact
                subset of PGL2(R) <=> Route A's window lemma holds empirically.
  lognorm_conj  same at the Galois-conjugate place.  Predicted to DRIFT linearly: that is
                Dirichlet's unit theorem killing finiteness while the dynamics ignores it.
  logJ, lkappa  log|G([0,1])| and log of the distortion sup|G'|/inf|G'| on [0,1].
  #states       distinct post-emission states.  Saturates for integer M (Vandehey's M_D),
                must grow for M over Z[phi] -- the two facts side by side are the point.

Usage:
  ./route_a_window.py selftest              # teeth: red-then-green on every instrument
  ./route_a_window.py window  --map phi --steps 3000
  ./route_a_window.py window  --map phi --input adversarial   # planted huge digits
  ./route_a_window.py memory  --map phi
  ./route_a_window.py freq    --map phi
  ./route_a_window.py all     --map phi
"""

import argparse
import math
import random
import sys
from collections import Counter

LOG2 = math.log(2.0)
SQRT5 = math.sqrt(5.0)
PHI = (1.0 + SQRT5) / 2.0
LOGPHI = math.log(PHI)

# --------------------------------------------------------------------------- Z[phi]
# element = (u, v)  meaning  u + v*phi,  phi^2 = phi + 1.
# real embedding:      u + v*PHI
# conjugate embedding: u + v*(1-PHI)
# Writing 2*(u+v*phi) = A + B*sqrt5 with A = 2u+v, B = v makes signs and logs exact.

ZERO = (0, 0)
ONE = (1, 0)


def zadd(a, b):
    return (a[0] + b[0], a[1] + b[1])


def zsub(a, b):
    return (a[0] - b[0], a[1] - b[1])


def zneg(a):
    return (-a[0], -a[1])


def zmul(a, b):
    u1, v1 = a
    u2, v2 = b
    return (u1 * u2 + v1 * v2, u1 * v2 + u2 * v1 + v1 * v2)


def zscale(k, a):
    return (k * a[0], k * a[1])


def zsign(a):
    """Exact sign of the real embedding.  O(1) in the common case."""
    u, v = a
    A = 2 * u + v
    B = v
    if A == 0 and B == 0:
        return 0
    if A >= 0 and B >= 0:
        return 1
    if A <= 0 and B <= 0:
        return -1
    # opposite signs: |A| vs |B|*sqrt5.  Cheap bit-length shortcuts first.
    la = A.bit_length() if A > 0 else (-A).bit_length()
    lb = B.bit_length() if B > 0 else (-B).bit_length()
    if la >= lb + 3:
        dom = 1 if A > 0 else -1
        return dom
    if lb >= la + 1:
        dom = 1 if B > 0 else -1
        return dom
    d = A * A - 5 * B * B  # never 0 unless A = B = 0
    if A > 0:
        return 1 if d > 0 else -1
    return -1 if d > 0 else 1


def _log_pos(P, Q):
    """log(P + Q*sqrt5) for P, Q >= 0, not both zero.  No cancellation, so floats suffice
    after a bit-shift down to a safe exponent."""
    b = max(P.bit_length(), Q.bit_length())
    k = max(0, b - 900)
    if k:
        val = (P >> k) + (Q >> k) * SQRT5
        if val <= 0.0:  # cannot happen for k chosen as above, but stay honest
            k = 0
            val = P + Q * SQRT5
    else:
        val = P + Q * SQRT5
    return math.log(val) + k * LOG2


def zlogs(a):
    """(log|a|, log|sigma(a)|).  Uses the exact norm to recover whichever side cancels."""
    u, v = a
    A = 2 * u + v
    B = v
    if A == 0 and B == 0:
        raise ZeroDivisionError("log of 0")
    n4 = A * A - 5 * B * B  # = 4 * a * sigma(a)
    lnorm = math.log(abs(n4)) - 2 * LOG2  # = log|a| + log|sigma(a)|
    if (A >= 0) == (B >= 0):
        la = _log_pos(abs(A), abs(B)) - LOG2  # |A + B sqrt5| = |A| + |B| sqrt5
        return la, lnorm - la
    ls = _log_pos(abs(A), abs(B)) - LOG2  # |A - B sqrt5| = |A| + |B| sqrt5
    return lnorm - ls, ls


def _floor_nonneg(num, den):
    """floor(num/den) for num >= 0, den > 0.  Exact, O(log answer) sign tests."""
    hi = 1
    while zsign(zsub(num, zscale(hi, den))) >= 0:
        hi *= 2
        if hi > (1 << 200):
            raise OverflowError("absurd digit")
    lo = hi // 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if zsign(zsub(num, zscale(mid, den))) >= 0:
            lo = mid
        else:
            hi = mid
    return lo


def zfloordiv(num, den):
    """floor of the real embedding of num/den.  den != 0."""
    if zsign(den) < 0:
        num, den = zneg(num), zneg(den)
    if zsign(num) >= 0:
        return _floor_nonneg(num, den)
    k = _floor_nonneg(zneg(num), den)
    exact = zsign(zsub(zneg(num), zscale(k, den))) == 0
    return -k if exact else -k - 1


def cmp_frac(n1, d1, n2, d2):
    """compare n1/d1 with n2/d2; d1, d2 > 0 required."""
    return zsign(zsub(zmul(n1, d2), zmul(n2, d1)))


# --------------------------------------------------------------------------- matrices
# M = (p, q, r, s) acting as z -> (p z + q) / (r z + s)


def mmul(M, N):
    p, q, r, s = M
    a, b, c, d = N
    return (
        zadd(zmul(p, a), zmul(q, c)),
        zadd(zmul(p, b), zmul(q, d)),
        zadd(zmul(r, a), zmul(s, c)),
        zadd(zmul(r, b), zmul(s, d)),
    )


def mdet(M):
    p, q, r, s = M
    return zsub(zmul(p, s), zmul(q, r))


def A_in(a):
    """G <- G * A_a  consumes input digit a."""
    return (ZERO, ONE, ONE, (a, 0))


def A_out_inv(c):
    """G <- A_c^-1 * G  emits output digit c.  A_c^-1 = [[-c,1],[1,0]]."""
    return ((-c, 0), ONE, ONE, ZERO)


def shift(k):
    """G <- [[1,-k],[0,1]] * G  emits the integer part k."""
    return (ONE, (-k, 0), ZERO, ONE)


def canon(M):
    """Projective canonical form: det is a fixed unit here, so the only freedom is +-1."""
    for e in M:
        s = zsign(e)
        if s:
            if s < 0:
                return tuple(zneg(x) for x in M)
            return M
    return M


MAPS = {
    # name: (matrix, human description)
    "phi": (((0, 1), ZERO, ZERO, ONE), "x -> phi*x            (det = phi, a UNIT of Z[phi])"),
    "xphi": ((ONE, (0, 1), ZERO, ONE), "x -> x + phi          (det = 1)"),
    "x/phi": (((-1, 1), ZERO, ZERO, ONE), "x -> x/phi = (phi-1)x (det = phi-1, a UNIT)"),
    "sqrt5x": (((-1, 2), ZERO, ZERO, ONE), "x -> sqrt5 * x        (det = sqrt5, NOT a unit)"),
    "2x": (((2, 0), ZERO, ZERO, ONE), "x -> 2x               (INTEGER control, Vandehey D=2)"),
    "3x": (((3, 0), ZERO, ZERO, ONE), "x -> 3x               (INTEGER control, Vandehey D=3)"),
    "x/2": ((ONE, ZERO, ZERO, (2, 0)), "x -> x/2              (INTEGER control, D=2)"),
    "(x+1)/2": ((ONE, ONE, ZERO, (2, 0)), "x -> (x+1)/2          (INTEGER control, D=2)"),
}


# --------------------------------------------------------------------------- transducer


class Transducer:
    """Greedy CF transducer for a fixed Mobius map M.

    feed(a) pushes one input CF digit through and emits every output digit that is then
    determined.  Progress is guaranteed for irrational input: the image interval is nested
    decreasing with length -> 0, so it eventually falls strictly inside a cylinder.
    """

    def __init__(self, M, break_p=0.0, rng=None):
        self.G = M
        self.det = mdet(M)
        self.logdet = zlogs(self.det)[0]
        self.logdet_conj = zlogs(self.det)[1]
        self.out = []
        self.phase = "int"
        self.break_p = break_p  # teeth: skip a legal emission with this probability
        self.rng = rng
        self.max_burst = 0
        self.max_wait = 0
        self._wait = 0

    # -- geometry -------------------------------------------------------------
    def endpoints(self):
        p, q, r, s = self.G
        n0, d0 = q, s
        n1, d1 = zadd(p, q), zadd(r, s)
        if zsign(d0) < 0:
            n0, d0 = zneg(n0), zneg(d0)
        if zsign(d1) < 0:
            n1, d1 = zneg(n1), zneg(d1)
        if cmp_frac(n0, d0, n1, d1) <= 0:
            return n0, d0, n1, d1
        return n1, d1, n0, d0

    def stats(self):
        """(lognorm_real, lognorm_conj, log|J|, log distortion) for the current state."""
        p, q, r, s = self.G
        lr = []
        lc = []
        for e in self.G:
            if e == ZERO:
                lr.append(-math.inf)
                lc.append(-math.inf)
            else:
                a, b = zlogs(e)
                lr.append(a)
                lc.append(b)
        lognorm = max(lr) - 0.5 * self.logdet
        lognorm_c = max(lc) - 0.5 * self.logdet_conj
        rs = zadd(r, s)
        if s == ZERO or rs == ZERO:
            return lognorm, lognorm_c, math.inf, math.inf
        ls = zlogs(s)[0]
        lrs = zlogs(rs)[0]
        logJ = self.logdet - ls - lrs
        lkappa = 2.0 * abs(lrs - ls)
        return lognorm, lognorm_c, logJ, lkappa

    # -- dynamics -------------------------------------------------------------
    def try_emit(self):
        burst = 0
        while True:
            if self.break_p and self.rng.random() < self.break_p:
                break
            nlo, dlo, nhi, dhi = self.endpoints()
            if self.phase == "int":
                k1 = zfloordiv(nlo, dlo)
                k2 = zfloordiv(nhi, dhi)
                if k1 != k2:
                    break
                self.out.append(k1)
                self.G = mmul(shift(k1), self.G)
                self.phase = "cf"
                burst += 1
                continue
            if zsign(nlo) <= 0 or zsign(nhi) <= 0:
                break
            c_lo = zfloordiv(dlo, nlo)  # floor(1/lo), the larger candidate
            c_hi = zfloordiv(dhi, nhi)  # floor(1/hi)
            if c_lo != c_hi or c_lo < 1:
                break
            self.out.append(c_lo)
            self.G = mmul(A_out_inv(c_lo), self.G)
            burst += 1
        if burst > self.max_burst:
            self.max_burst = burst
        if burst:
            self._wait = 0
        else:
            self._wait += 1
            if self._wait > self.max_wait:
                self.max_wait = self._wait
        return burst

    def feed(self, a):
        self.G = mmul(self.G, A_in(a))
        return self.try_emit()

    def bits(self):
        return max(max(abs(u).bit_length(), abs(v).bit_length()) for (u, v) in self.G)


# --------------------------------------------------------------------------- inputs


class LebesgueStream:
    """Exact CF digits of a genuine x ~ Uniform[0,1).

    x is realised lazily by i.i.d. random bits: x in [k/2^m, (k+1)/2^m).  A CF digit is
    emitted only once BOTH endpoints agree on it -- and the set of reals with a given CF
    prefix is an interval, so agreement at the endpoints means agreement throughout.  The
    digit stream is therefore the true CF of a uniformly sampled real (Gauss ~ Lebesgue,
    so a.e. such x is CF-normal), not an i.i.d. approximation to one.
    """

    name = "lebesgue (exact CF of a uniform random real)"

    def __init__(self, rng):
        self.rng = rng
        self.k = 0
        self.m = 0
        self.inv = (1, 0, 0, 1)  # integer Mobius taking x to the current tail

    def _ends(self):
        e, f, g, h = self.inv
        M = 1 << self.m
        n0, d0 = e * self.k + f * M, g * self.k + h * M
        n1, d1 = e * (self.k + 1) + f * M, g * (self.k + 1) + h * M
        if d0 < 0:
            n0, d0 = -n0, -d0
        if d1 < 0:
            n1, d1 = -n1, -d1
        if d0 == 0 or d1 == 0:
            return None
        if n0 * d1 > n1 * d0:
            n0, d0, n1, d1 = n1, d1, n0, d0
        return n0, d0, n1, d1

    def next(self):
        for _ in range(100000):
            ends = self._ends()
            if ends is not None:
                n0, d0, n1, d1 = ends
                if n0 > 0 and n1 > 0 and n1 * 1 <= d1:  # both endpoints in (0,1]
                    c0 = d0 // n0
                    c1 = d1 // n1
                    if c0 == c1 and c0 >= 1:
                        e, f, g, h = self.inv
                        # inv <- A_c^-1 inv = [[-c,1],[1,0]] inv
                        self.inv = (-c0 * e + g, -c0 * f + h, e, f)
                        return c0
            self.k = 2 * self.k + self.rng.getrandbits(1)
            self.m += 1
        raise RuntimeError("lebesgue stream stalled")


class IidStream:
    """i.i.d. Gauss-Kuzmin digits.  Right marginal, WRONG dependence -- kept as a control
    (its 2-block frequencies are detectably off Gauss, which the freq mode will show)."""

    name = "iid Gauss-Kuzmin (control: correct marginal, independent digits)"

    def __init__(self, rng):
        self.rng = rng

    def next(self):
        u = self.rng.random()
        t = 2.0 ** (1.0 - u) - 1.0
        k = max(1, int(math.ceil(1.0 / t)) - 1) if t > 0 else 1
        while 1.0 - math.log2((k + 2) / (k + 1)) < u:
            k += 1
        while k > 1 and 1.0 - math.log2((k + 1) / k) >= u:
            k -= 1
        return k


class PeriodicStream:
    """Periodic digits: a quadratic irrational, emphatically NOT CF-normal.  Red control
    for the frequency instrument."""

    def __init__(self, pattern):
        self.pattern = pattern
        self.i = 0
        self.name = "periodic %s (NOT CF-normal -- red control)" % (list(pattern),)

    def next(self):
        c = self.pattern[self.i % len(self.pattern)]
        self.i += 1
        return c


class AdversarialStream:
    """Random input with deliberately planted ENORMOUS digits.

    This is the sharp form of the window question.  CF digits are unbounded a.s., and
    crux risk (i) in the attack map is precisely that excursions are unbounded-rank.  If
    the post-emission state norm grows with the size of the planted digit, W is not
    compact and Route A is dead; if it snaps back, the renormalisation really does
    enforce the window."""

    def __init__(self, rng, period=25, sizes=(10**3, 10**6, 10**9, 10**12, 10**15)):
        self.base = LebesgueStream(rng)
        self.period = period
        self.sizes = sizes
        self.i = 0
        self.j = 0
        self.name = "adversarial (uniform real + a planted huge digit every %d)" % period
        self.planted_at = {}

    def next(self):
        self.i += 1
        if self.i % self.period == 0:
            d = self.sizes[self.j % len(self.sizes)]
            self.j += 1
            self.planted_at[self.i] = d
            return d
        return self.base.next()


def make_stream(kind, rng, period=25):
    if kind == "lebesgue":
        return LebesgueStream(rng)
    if kind == "iid":
        return IidStream(rng)
    if kind == "adversarial":
        return AdversarialStream(rng, period=period)
    if kind.startswith("periodic"):
        pat = kind.split(":", 1)[1] if ":" in kind else "1,2"
        return PeriodicStream([int(t) for t in pat.split(",")])
    raise SystemExit("unknown input stream %r" % kind)


# --------------------------------------------------------------------------- Gauss measure

BUCKET_K = 6  # digits 1..5 tracked individually, 6 means ">= 6"


def bucket(d):
    return d if d < BUCKET_K else BUCKET_K


def cyl_measure(word):
    """Exact-ish Gauss measure of the cylinder C_word (float log at the very end)."""
    p, q, r, s = 1, 0, 0, 1
    for a in word:
        p, q, r, s = q, p + q * a, s, r + s * a
    lo_n, lo_d = q, s
    hi_n, hi_d = p + q, r + s
    lo = lo_n / lo_d
    hi = hi_n / hi_d
    if lo > hi:
        lo, hi = hi, lo
    return (math.log1p(hi) - math.log1p(lo)) / LOG2


def gauss_tables():
    one = {k: cyl_measure((k,)) for k in range(1, BUCKET_K)}
    one[BUCKET_K] = 1.0 - sum(one.values())
    two = {}
    for i in range(1, BUCKET_K):
        for j in range(1, BUCKET_K):
            two[(i, j)] = cyl_measure((i, j))
    for i in range(1, BUCKET_K):
        two[(i, BUCKET_K)] = one[i] - sum(two[(i, j)] for j in range(1, BUCKET_K))
        two[(BUCKET_K, i)] = one[i] - sum(two[(j, i)] for j in range(1, BUCKET_K))
    two[(BUCKET_K, BUCKET_K)] = 1.0 - sum(two.values())
    return one, two


GAUSS1, GAUSS2 = gauss_tables()


def tv_against_gauss(digits):
    if len(digits) < 50:
        return None, None
    c1 = Counter(bucket(d) for d in digits)
    n1 = sum(c1.values())
    tv1 = 0.5 * sum(abs(c1.get(k, 0) / n1 - GAUSS1[k]) for k in GAUSS1)
    c2 = Counter((bucket(a), bucket(b)) for a, b in zip(digits, digits[1:]))
    n2 = sum(c2.values())
    tv2 = 0.5 * sum(abs(c2.get(k, 0) / n2 - GAUSS2[k]) for k in GAUSS2)
    return tv1, tv2


def tv_between(d1, d2):
    c1 = Counter((bucket(a), bucket(b)) for a, b in zip(d1, d1[1:]))
    c2 = Counter((bucket(a), bucket(b)) for a, b in zip(d2, d2[1:]))
    n1, n2 = max(1, sum(c1.values())), max(1, sum(c2.values()))
    keys = set(c1) | set(c2)
    return 0.5 * sum(abs(c1.get(k, 0) / n1 - c2.get(k, 0) / n2) for k in keys)


def noise_floor(digits):
    """TV between the two halves of one stream: the sampling-noise baseline."""
    h = len(digits) // 2
    return tv_between(digits[:h], digits[h:])


# --------------------------------------------------------------------------- modes


def quantiles(xs, qs=(0.5, 0.9, 0.99, 0.999, 1.0)):
    if not xs:
        return {}
    ys = sorted(xs)
    out = {}
    for q in qs:
        i = min(len(ys) - 1, int(q * (len(ys) - 1) + 0.5))
        out[q] = ys[i]
    return out


def run_window(M, stream, steps, break_p=0.0, rng=None, state_cap=2500, max_bits=400000,
               track_states=True):
    td = Transducer(M, break_p=break_p, rng=rng)
    rec = []
    seen = set()
    saturated_at = None
    half = steps // 2
    seen_at_half = None
    digits_in = []
    per_digit = []  # (input digit, lognorm right after)
    for n in range(1, steps + 1):
        a = stream.next()
        digits_in.append(a)
        td.feed(a)
        if td.phase != "cf":
            continue
        st = td.stats()
        rec.append(st)
        per_digit.append((a, st[0]))
        if track_states and len(seen) < state_cap:
            before = len(seen)
            seen.add(canon(td.G))
            if len(seen) == before and saturated_at is None:
                saturated_at = n
        if track_states and n == half:
            seen_at_half = len(seen)
        if td.bits() > max_bits:
            break
    return td, rec, seen, digits_in, per_digit, (saturated_at, seen_at_half)


def running_max_profile(rec, idx=0):
    out = []
    m = -math.inf
    marks = []
    n = len(rec)
    for frac in (0.125, 0.25, 0.5, 1.0):
        marks.append(max(1, int(frac * n)))
    j = 0
    for i, r in enumerate(rec, 1):
        if r[idx] > m:
            m = r[idx]
        while j < len(marks) and i == marks[j]:
            out.append((i, m))
            j += 1
    return out


def mode_window(args, rng):
    M, desc = MAPS[args.map]
    stream = make_stream(args.input, rng, period=args.period)
    print("== WINDOW ==  map: %s" % desc)
    print("   input: %s" % stream.name)
    print("   steps: %d   break-emission p=%.3f" % (args.steps, args.break_p))
    td, rec, seen, din, per_digit, (sat, half) = run_window(
        M, stream, args.steps, break_p=args.break_p, rng=rng, state_cap=args.state_cap,
        max_bits=args.max_bits)
    if not rec:
        print("   !! never left the integer-part phase")
        return None
    lognorm = [r[0] for r in rec]
    logconj = [r[1] for r in rec]
    logJ = [r[2] for r in rec]
    lkap = [r[3] for r in rec]
    print()
    print("   -- real place (THE window statistic, natural log) --")
    q = quantiles(lognorm)
    print("      median %.3f   p90 %.3f   p99 %.3f   p99.9 %.3f   MAX %.3f"
          % (q[0.5], q[0.9], q[0.99], q[0.999], q[1.0]))
    prof = running_max_profile(rec, 0)
    print("      running max at n = " + "  ".join("%d:%.3f" % (n, m) for n, m in prof))
    grew = prof[-1][1] - prof[-2][1] if len(prof) >= 2 else 0.0
    print("      new record in the last half: %+.3f nats" % grew)
    print("      distortion log kappa: median %.3f  max %.3f"
          % (quantiles(lkap)[0.5], quantiles(lkap)[1.0]))
    print("      log|J|:               median %.3f  min %.3f"
          % (quantiles(logJ)[0.5], quantiles(logJ, (0.0,))[0.0]))
    print()
    print("   -- conjugate place (Vandehey's dead finiteness certificate) --")
    if len(logconj) > 20:
        n0, n1 = len(logconj) // 4, len(logconj) - 1
        slope = (logconj[n1] - logconj[n0]) / max(1, (n1 - n0))
        print("      start %.1f -> end %.1f   drift %.3f nats/step (%.2f bits/step)"
              % (logconj[0], logconj[-1], slope, slope / LOG2))
    print("      entry size at the end: %d bits" % td.bits())
    print()
    print("   -- state set --")
    print("      distinct post-emission states: %d after %d steps"
          % (len(seen), len(rec)))
    if half is not None:
        print("      new states discovered in the SECOND half: %d  (0 => finite state set)"
              % (len(seen) - half))
    print("   -- emission health --")
    m_out = len(td.out) - 1
    print("      output/input ratio c1 ~ %.4f   max burst %d   max wait %d"
          % (m_out / max(1, len(din)), td.max_burst, td.max_wait))
    print("      largest input digit seen: %d   largest output digit: %d"
          % (max(din), max(td.out[1:]) if m_out > 0 else 0))
    if isinstance(stream, AdversarialStream) and stream.planted_at:
        print()
        print("   -- planted-excursion response (the sharp form of the window question) --")
        print("      %-16s %-10s %-10s" % ("planted digit", "lognorm@", "lognorm+1"))
        idx = {}
        for i, (a, ln) in enumerate(per_digit):
            idx[i] = (a, ln)
        shown = 0
        for i, (a, ln) in enumerate(per_digit):
            if a >= 1000:
                nxt = per_digit[i + 1][1] if i + 1 < len(per_digit) else float("nan")
                print("      %-16d %-10.3f %-10.3f" % (a, ln, nxt))
                shown += 1
                if shown >= 12:
                    break
        big = [ln for (a, ln) in per_digit if a >= 1000]
        small = [ln for (a, ln) in per_digit if a < 1000]
        if big and small:
            print("      max lognorm after a HUGE digit: %.3f   after a normal digit: %.3f"
                  % (max(big), max(small)))
    return {"lognorm": lognorm, "prof": prof, "states": len(seen), "td": td,
            "digits_out": td.out[1:], "digits_in": din}


def mode_memory(args, rng):
    M, desc = MAPS[args.map]
    print("== MEMORY ==  map: %s" % desc)
    print("   Two runs started from DIFFERENT reachable states (different burn-in inputs).")
    print("   Pathwise merging and distributional merging are different questions here;")
    print("   both are measured.")
    burn = args.burn
    common = args.steps

    def burn_in(seed):
        r = random.Random(seed)
        s = LebesgueStream(r)
        td = Transducer(M)
        for _ in range(burn):
            td.feed(s.next())
        return td

    t1 = burn_in(args.seed + 11)
    t2 = burn_in(args.seed + 22)
    print("   burn-in %d digits each; states differ: %s"
          % (burn, canon(t1.G) != canon(t2.G)))

    # --- pathwise: same input suffix, do the states ever coincide? -------------
    shared = LebesgueStream(random.Random(args.seed + 33))
    o1_start, o2_start = len(t1.out), len(t2.out)
    merged_at = None
    for n in range(1, common + 1):
        a = shared.next()
        t1.feed(a)
        t2.feed(a)
        if merged_at is None and canon(t1.G) == canon(t2.G):
            merged_at = n
    tail1 = t1.out[o1_start:]
    tail2 = t2.out[o2_start:]
    best = (0, 0)
    L = min(len(tail1), len(tail2))
    if L > 20:
        for d in range(-40, 41):
            a1 = tail1[max(0, d):]
            a2 = tail2[max(0, -d):]
            k = 0
            for x, y in zip(reversed(a1), reversed(a2)):
                if x != y:
                    break
                k += 1
            if k > best[0]:
                best = (k, d)
    print()
    print("   -- pathwise (Vandehey's finite-state Doeblin mechanism) --")
    print("      exact state merge on a common input: %s"
          % ("step %d" % merged_at if merged_at else "NEVER in %d steps" % common))
    print("      longest common output tail: %d digits (shift %d) of %d/%d"
          % (best[0], best[1], len(tail1), len(tail2)))

    # --- distributional: independent inputs, different starts ------------------
    def profile(seed_state, seed_input):
        td = burn_in(seed_state)
        s = LebesgueStream(random.Random(seed_input))
        hist = Counter()
        outs = []
        base = len(td.out)
        for _ in range(common):
            td.feed(s.next())
            if td.phase != "cf":
                continue
            ln, _, lj, lk = td.stats()
            hist[(round(ln * 4), round(lk * 2))] += 1
        outs = td.out[base:]
        return hist, outs

    hA, oA = profile(args.seed + 11, args.seed + 101)
    hB, oB = profile(args.seed + 22, args.seed + 202)
    hC, oC = profile(args.seed + 11, args.seed + 303)  # same start, different input

    def hist_tv(h1, h2):
        n1, n2 = max(1, sum(h1.values())), max(1, sum(h2.values()))
        keys = set(h1) | set(h2)
        return 0.5 * sum(abs(h1.get(k, 0) / n1 - h2.get(k, 0) / n2) for k in keys)

    print()
    print("   -- distributional (what the counting argument actually needs) --")
    print("      state-law TV, different start + different input : %.4f" % hist_tv(hA, hB))
    print("      state-law TV, SAME start + different input      : %.4f  <- noise floor"
          % hist_tv(hA, hC))
    print("      output 2-block TV, different start              : %.4f" % tv_between(oA, oB))
    print("      output 2-block TV, same start (noise floor)     : %.4f" % tv_between(oA, oC))
    return {"merged_at": merged_at, "tail": best[0]}


def mode_freq(args, rng):
    M, desc = MAPS[args.map]
    stream = make_stream(args.input, rng, period=args.period)
    print("== FREQUENCY ==  map: %s" % desc)
    print("   input: %s" % stream.name)
    print("   NOTE: on a RANDOM input this is a correctness check on the transducer, not")
    print("   evidence for the theorem -- a.e. x has both x and Mx CF-normal for free.")
    td, rec, seen, din, _, _ = run_window(M, stream, args.steps, rng=rng,
                                          state_cap=1, max_bits=args.max_bits,
                                          track_states=False)
    dout = td.out[1:]
    i1, i2 = tv_against_gauss(din)
    o1, o2 = tv_against_gauss(dout)
    print()
    print("   %-28s %-10s %-10s %s" % ("stream", "TV 1-block", "TV 2-block", "n"))
    if i1 is not None:
        print("   %-28s %-10.4f %-10.4f %d" % ("input", i1, i2, len(din)))
    if o1 is not None:
        print("   %-28s %-10.4f %-10.4f %d" % ("output (Mx)", o1, o2, len(dout)))
        print("   %-28s %-10s %-10.4f" % ("noise floor (half-vs-half)", "-", noise_floor(dout)))
    return {"in": (i1, i2), "out": (o1, o2)}


# --------------------------------------------------------------------------- self-test


def independent_cf(num, den, k):
    """Plain CF expansion of the single number num/den in Q(sqrt5) -- an independent code
    path from the transducer (no intervals, no emission logic)."""
    digits = []
    for _ in range(k):
        if zsign(den) < 0:
            num, den = zneg(num), zneg(den)
        if den == ZERO:
            break
        a = zfloordiv(num, den)
        digits.append(a)
        rem = zsub(num, zscale(a, den))
        if zsign(rem) == 0:
            break
        num, den = den, rem
    return digits


def selftest(args):
    ok = True
    rng = random.Random(args.seed)
    print("=" * 78)
    print("SELF-TEST  (each instrument is shown failing on a case where it must fail,")
    print("            and passing on a case where it must pass)")
    print("=" * 78)

    # --- T1  transducer output verified against an independent CF computation ---
    print("\nT1  transducer correctness vs an independent exact CF of phi*(p/q)")
    for seed in (1, 2, 3):
        r = random.Random(seed)
        s = LebesgueStream(r)
        M = MAPS["phi"][0]
        td = Transducer(M)
        ins = []
        for _ in range(60):
            a = s.next()
            ins.append(a)
            td.feed(a)
        # interior rational of the input cylinder: [0; a1..an, 2]
        p, q, rr, ss = 1, 0, 0, 1
        for a in ins + [2]:
            p, q, rr, ss = q, p + q * a, ss, rr + ss * a
        xnum, xden = q, ss  # x_rat = q/ss  (the image of 0)
        # phi * x_rat  as a Z[phi] fraction
        val_n = zmul((0, 1), (xnum, 0))
        val_d = (xden, 0)
        indep = independent_cf(val_n, val_d, len(td.out) + 5)
        claimed = td.out
        agree = indep[: len(claimed)] == claimed
        print("      seed %d: %d determined digits, independent CF agrees: %s"
              % (seed, len(claimed), agree))
        ok &= agree
    if not ok:
        print("      !! transducer is WRONG -- nothing below means anything")

    # --- T2  integer control must show a FINITE state set -----------------------
    print("\nT2  integer control (Vandehey's theorem applies -> state set must saturate)")
    for name in ("2x", "3x"):
        r = random.Random(args.seed + 7)
        s = LebesgueStream(r)
        M = MAPS[name][0]
        td, rec, seen, din, _, (sat, half) = run_window(M, s, 2000, state_cap=100000)
        prof = running_max_profile(rec, 0)
        new2 = len(seen) - (half or 0)
        print("      %-4s distinct states %3d, new in 2nd half %3d   lognorm max %.3f"
              % (name, len(seen), new2, prof[-1][1]))
        ok &= (new2 * 8 < len(seen))
    print("      phi  (comparison, det a unit of Z[phi]):")
    r = random.Random(args.seed + 7)
    s = LebesgueStream(r)
    td, rec, seen, din, _, (sat, half) = run_window(MAPS["phi"][0], s, 2000,
                                                    state_cap=100000)
    print("           distinct states %d in 2000 steps, new in 2nd half %d"
          % (len(seen), len(seen) - (half or 0)))
    print("           -> finiteness is genuinely GONE, exactly as Dirichlet predicts")

    # --- T3  the window statistic must blow up when renormalisation is broken ---
    print("\nT3  teeth on the window statistic: skip legal emissions and it must blow up")
    for p in (0.0, 0.5):
        r = random.Random(args.seed + 5)
        s = LebesgueStream(r)
        td, rec, seen, din, _, _ = run_window(MAPS["phi"][0], s, 1500, break_p=p,
                                              rng=random.Random(args.seed + 9),
                                              track_states=False)
        prof = running_max_profile(rec, 0)
        print("      break_p=%.1f  lognorm max %.3f  (running: %s)"
              % (p, prof[-1][1], " ".join("%.2f" % m for _, m in prof)))
        if p == 0.0:
            base = prof[-1][1]
        else:
            broke = prof[-1][1]
    good = broke > base + 3.0
    print("      broken run exceeds intact run by %+.2f nats: %s" % (broke - base, good))
    ok &= good

    # --- T4  the frequency statistic must flag a non-normal OUTPUT ---------------
    print("\nT4  teeth on the frequency statistic (output side)")
    print("      red control must keep the output inside one real quadratic field:")
    print("      an INTEGER map does (2x of a periodic CF is again quadratic => periodic).")
    for kind in ("lebesgue", "periodic:1,2,3"):
        r = random.Random(args.seed + 3)
        st = make_stream(kind, r)
        td, rec, seen, din, _, _ = run_window(MAPS["2x"][0], st, 1500, track_states=False)
        i1, i2 = tv_against_gauss(din)
        o1, o2 = tv_against_gauss(td.out[1:])
        print("      2x   %-16s input TV2 %.4f   output TV2 %.4f"
              % (kind.split(":")[0], i2, o2))
        if kind == "lebesgue":
            rand_tv = o2
        else:
            per_tv = o2
    good = per_tv > 4 * rand_tv
    print("      periodic output is %.1fx further from Gauss than random: %s"
          % (per_tv / max(1e-9, rand_tv), good))
    ok &= good
    print("      (aside, a real finding: under x -> phi*x a PERIODIC input gives a")
    print("       Gauss-typical-looking output, because phi*(quadratic) is QUARTIC.)")

    # --- T5  the coupling detector must NOT fire on independent inputs ----------
    print("\nT5  teeth on the coupling detector: independent inputs must NOT couple")
    M = MAPS["2x"][0]
    t1, t2 = Transducer(M), Transducer(M)
    s1 = LebesgueStream(random.Random(args.seed + 41))
    s2 = LebesgueStream(random.Random(args.seed + 42))
    for _ in range(600):
        t1.feed(s1.next())
        t2.feed(s2.next())
    tail1, tail2 = t1.out[-200:], t2.out[-200:]
    best = 0
    for d in range(-30, 31):
        a1 = tail1[max(0, d):]
        a2 = tail2[max(0, -d):]
        k = 0
        for x, y in zip(reversed(a1), reversed(a2)):
            if x != y:
                break
            k += 1
        best = max(best, k)
    print("      longest common output tail on INDEPENDENT inputs: %d (must be small)" % best)
    ok &= best < 6

    print("\n" + "=" * 78)
    print("SELF-TEST %s" % ("PASSED" if ok else "FAILED"))
    print("=" * 78)
    return 0 if ok else 1


# --------------------------------------------------------------------------- verdict


def verdict(res):
    print()
    print("=" * 78)
    print("READING THE RESULT")
    print("=" * 78)
    print("""
  window / running max of lognorm_real
      flat over the last half, and unchanged after a planted 10^15 digit
          -> the compact-window lemma holds empirically.  Route A's crux (ii) is
             a real lemma to prove, not a wall.  Write the blueprint.
      grows like log n, or scales with the size of the planted digit
          -> W is not compact; the state escapes.  Route A is dead as stated, and
             the finite-fiber proof does not port.  Say so and stop.

  conjugate place
      linear drift alongside a flat real place is the whole thesis in one picture:
      Dirichlet's units destroy Vandehey's finiteness certificate while the dynamics
      never reads that place.

  memory
      NO exact state merge for a map with det a unit of Z[phi] is EXPECTED, and is a
      one-line fact, not a failure: exact merge needs V integral with M^-1 V M integral,
      which for M = diag(phi,1) forces V diagonal, i.e. the same input prefix.  So the
      finite-state Doeblin mechanism provably does not port; only the distributional
      statement can.  What must hold is the two state-law TVs converging to the noise
      floor.  If they separate, crux (i) is the wall the attack map priced at 35%.
""")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", choices=["window", "memory", "freq", "all", "selftest"])
    ap.add_argument("--map", default="phi", choices=sorted(MAPS))
    ap.add_argument("--input", default="lebesgue",
                    help="lebesgue | iid | adversarial | periodic:1,2,3")
    ap.add_argument("--steps", type=int, default=2000)
    ap.add_argument("--burn", type=int, default=150)
    ap.add_argument("--seed", type=int, default=20260824)
    ap.add_argument("--break-emission", dest="break_p", type=float, default=0.0)
    ap.add_argument("--period", type=int, default=25, help="adversarial planting period")
    ap.add_argument("--state-cap", type=int, default=2500)
    ap.add_argument("--max-bits", type=int, default=400000)
    args = ap.parse_args()

    if args.mode == "selftest":
        return selftest(args)

    rng = random.Random(args.seed)
    if args.mode in ("window", "all"):
        mode_window(args, rng)
        print()
    if args.mode in ("memory", "all"):
        mode_memory(args, random.Random(args.seed))
        print()
    if args.mode in ("freq", "all"):
        mode_freq(args, random.Random(args.seed))
    if args.mode == "all":
        verdict(None)
    return 0


if __name__ == "__main__":
    sys.exit(main())
