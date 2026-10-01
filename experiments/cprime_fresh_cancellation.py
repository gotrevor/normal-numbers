#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""Do the fresh primes cancel?  The instrument behind quantitative C′ (2026-09-30).

Quantitative C′ (docs/CPRIME-QUANTITATIVE-2026-09-30.md) bounds the transfer term by the
triangle inequality (2.1):

    |W - W_y| <= B := sum_j a_j [2 S_P(y_j, N) + J/N],   a_j = |e(h/4^j) - 1|,

so a prime set with fresh mass rho > 0 keeps a defect linear in rho.  This probe measures, on
residue-class and randomly thinned prime sets, how much of B the true difference uses:

    W    = (1/N) sum_{n<N} prod_{j=1..J} z_j^{omega_P(n+j)},          z_j = e(h/4^j)
    W_y  = the same with only the primes p <= y_j of P counted at site j  (frozen part)
    W_1  = the same with the primes p <= max(y_j, sqrt N) counted         (adds band F1)
    M    = (1/N) sum_n |full product - frozen product|                    (pointwise L1)

Reported: A = |W - W_y| against M and B (cancellation in the average, and slack in the
hit count), the RELATIVE defect A/|W_y| (the fable verdict of 2026-09-19 says fresh primes
rescale the frozen mean by an N-independent Dickman-type factor rather than adding noise, in
which case A/|W_y| stays bounded while A -> 0), and the split A1 = |W_1 - W_y| (fresh band
(y_j, sqrt N]) versus A2 = |W - W_1| (fresh band (sqrt N, N]).

Order split: W - W_y = T1 + T2 exactly, where T1 = mean of frozen * sum_j (z_j^fresh_j - 1)
keeps every n whose fresh primes sit at ONE site, and T2 collects n with fresh primes at two or
more sites (a prime-pair configuration p | n+j, p' | n+j', j != j').  If T2 = O(rho^2) the
parity-type wall enters only at second order in the fresh mass.

Relative first order (--report relative): the premise RelativeFirstOrder says T1 = W_y G_h + o(1)
with G_h bounded and N-independent.  Reported: G = T1 / W_y (modulus and phase), the
independent-sites model Sbar = mean of sum_j (z_j^fresh_j - 1) (what G would be if the fresh part
were uncorrelated with the frozen product), and the coupling C = T1 - W_y Sbar = cov(frozen,
fresh), as |C|/|T1|.  The premise predicts G stable in N at fixed a while T1 tracks W_y.

Second order (--report pair): T2 = W - W_y - T1, where the probe's T1 = mean[Phi_y * sum_j (z_j^fresh_j - 1)]
is the Lean T1' (freshOneSite).  PairSecondOrder says |T2| <= C * Fw^2 with Fw = sum_j |z_j - 1| S_P(y_j, N), C absolute.

Analytic G (--report sites).  Four nested values of G, each gap isolating one step:
    G     measured T1 / W_y;
    G_A   sum_k [Mf_k / My_k - 1], with Mf_k = mean z_k^omega_P(n+k), My_k = mean z_k^omega_{<=y_k}(n+k)
          measured exactly: what G is if the J sites are independent (CRT across sites), so that T1
          reduces to a single-integer ratio per site;
    G_SD  the same with the Selberg-Delange main term for Mf and the CRT product times the generalized
          Dickman factor F_{dw}(u), u = log N / log y, for My:
          Mf/My = (log N)^(dw) prod_{p<=N} (1-1/p)^(dw) prod_{p in P, y<p<=N} (1 + w/p) / (Gamma(1 + dw) F(u)),
          w = z - 1, d = the density of P among primes;
    G_inf the N -> infinity limit at y = N^s, s = a 2^-k:  g_k = 1/R_{dw}(1/s) - 1  (see dickman_R);
    site 1 My/CRT vs F(u_1): the exact frozen mean at site 1 over its CRT product prod_{p<=y_1} (1 + w/p),
          against the generalized Dickman factor that G_SD and G_inf use for it (u_1 = log N / log y_1);
    G_inf0 its u -> oo form s^(-dw) e^(-gamma dw) / Gamma(1 + dw) - 1, which drops the frozen mean's own
          size budget (wrong by ~35% for all primes at y = sqrt N).
The limit is N-independent, and to first order in d it is sum_k w_k d log(1/s_k), the linear fresh mass.  Also reported: prod_k My_k / W_y (site independence of
the frozen mean itself).

Cutoffs: y_j = N^(a 2^-j) with a = --a (default 1, so y_1 = sqrt N).  The paper's a = u^-2 with
u >= 66 is numerically degenerate (y_1 ~ 1 at N = 2^24); this probe measures the mechanism at
reachable scales, not the paper's constants.  J = floor(log2 log2 N) + 1 (the repo's windowJ).

    experiments/cprime_fresh_cancellation.py [--logN 20 22 24] [--h 1 3 5] [--a 1.0 0.5]
        [--sets "p = 1 mod 3" "thin 0.5"] [--report transfer|relative|sites|limit|frozen|pair]
Tests: experiments/test_cprime_fresh_cancellation.py
"""
import argparse
import math
import sys

import numpy as np
from scipy.special import rgamma

EULER_GAMMA = 0.5772156649015329


def primes_upto(m):
    s = np.ones(m + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(m ** 0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return np.nonzero(s)[0]


def window_J(N):
    """The repo's windowJ: floor(log2 log2 N) + 1."""
    l2 = N.bit_length() - 1
    return (l2.bit_length() - 1) + 1


def cutoffs(N, J, a):
    return [int(math.floor(N ** (a * 2.0 ** (-j)))) for j in range(1, J + 1)]


def band_counts(L, ps, edges):
    """counts[b][n] = #{p in ps : p | n, edges[b-1] < p <= edges[b]} for n <= L,
    with edges[-1] = 0 implicit and a final band above edges[-1].  int16 per band."""
    edges = sorted(set(edges))
    nb = len(edges) + 1
    out = [np.zeros(L + 1, dtype=np.int16) for _ in range(nb)]
    band = np.searchsorted(np.array(edges), ps, side="left")  # p <= edges[b] -> b
    for p, b in zip(ps.tolist(), band.tolist()):
        out[b][p::p] += 1
    return edges, out


def omega_le(edges, out, c):
    """#{p in P, p | n, p <= c} as an array, c must be one of the edges."""
    k = edges.index(c)
    acc = out[0].copy()
    for b in range(1, k + 1):
        acc += out[b]
    return acc


def g_inf(delta, w, s):
    """Limit site factor s^(-dw) e^(-gamma dw) / Gamma(1 + dw) - 1 (y = N^s, w = z - 1), the u -> oo
    form that ignores the size budget of the frozen mean itself."""
    dw = delta * w
    return complex(np.exp(-dw * math.log(s) - EULER_GAMMA * dw) * rgamma(1 + dw) - 1)


def dickman_R(kappa, u, M=4000):
    """R_kappa(u) = F_kappa(u) / (A u^kappa), A = e^(-gamma kappa) / Gamma(1 + kappa), where F_kappa is the
    generalized Dickman distribution function: F = A t^kappa on [0, 1] and t F'(t) = kappa (F(t) - F(t-1)).
    Equivalently R = 1 on [0, 1] and R'(t) = -(kappa/t) ((t-1)/t)^kappa R(t-1).  On [1, 2] in closed form,
    R = 1 - kappa sum_n b^(kappa+n+1)/(kappa+n+1), b = 1 - 1/t; beyond, trapezoid on unit segments.
    The fresh-band site factor at y = N^(1/u) is 1/R_kappa(u) - 1.  At a pole (kappa a negative integer)
    R = oo, i.e. the factor is -1.  Re kappa < -1 with u > 2 is not supported (returns nan)."""
    kappa = complex(kappa)
    if u <= 1:
        return 1.0 + 0j
    m = round(-kappa.real)
    if m >= 1 and abs(kappa + m) < 1e-9:
        return complex("inf")
    if kappa.real < -1 - 1e-9 and u > 2:
        return complex("nan")
    n = np.arange(80)

    def seg1(t):
        b = 1 - 1 / np.asarray(t, dtype=np.float64)
        out = np.ones(b.shape, dtype=np.complex128)
        pos = b > 0
        bb = b[pos][:, None]
        out[pos] = 1 - kappa * np.sum(bb ** (kappa + n + 1) / (kappa + n + 1), axis=1)
        return out

    if u <= 2:
        return complex(seg1(np.array([u]))[0])
    grid = np.linspace(0, 1, M + 1)
    prev = seg1(1 + grid)                       # R on [1, 2]
    for k in range(2, int(math.ceil(u))):
        t = k + grid
        f = -(kappa / t) * ((t - 1) / t) ** kappa * prev
        cum = np.concatenate([[0], np.cumsum((f[1:] + f[:-1]) / 2) / M])
        cur = prev[-1] + cum
        if u <= k + 1:
            return complex(np.interp(u - k, grid, cur.real) + 1j * np.interp(u - k, grid, cur.imag))
        prev = cur
    raise AssertionError("unreachable")


def g_dickman(delta, w, s):
    """Limit site factor with the frozen-mean size budget: 1/R_{dw}(1/s) - 1.  Tends to g_inf as s -> 0."""
    R = dickman_R(delta * w, 1 / s)
    return complex(-1) if np.isinf(R) else complex(1 / R - 1)


def dickman_F(kappa, u):
    """F_kappa(u) = A u^kappa R_kappa(u) (the frozen mean's size-budget factor at y = N^(1/u))."""
    if u <= 1 or not np.isfinite(u):
        return 1.0 + 0j
    R = dickman_R(kappa, u)
    return complex(np.exp(kappa * (math.log(u) - EULER_GAMMA)) * rgamma(1 + kappa) * R)


def g_sd(delta, w, N, ps, y, log_mertens):
    """Finite-N Selberg-Delange site factor; log_mertens = sum_{p<=N} log(1 - 1/p) over ALL primes."""
    dw = delta * w
    fresh = ps[(ps > y) & (ps <= N)].astype(np.float64)
    tail = np.sum(np.log(1 + w / fresh)) if len(fresh) else 0.0
    return complex(np.exp(dw * (math.log(math.log(N)) + log_mertens) + tail) * rgamma(1 + dw) - 1)


_LOG_MERTENS = {}


def log_mertens(N):
    if N not in _LOG_MERTENS:
        _LOG_MERTENS[N] = float(np.sum(np.log1p(-1.0 / primes_upto(N))))
    return _LOG_MERTENS[N]


def measure(N, ps, hs, a=1.0, delta=None):
    """All quantities for one prime set (sorted array ps of primes) and one N, for each h in hs.
    delta (density of ps among primes) enables the analytic columns G_SD and G_inf."""
    J = window_J(N)
    ys = cutoffs(N, J, a)
    r = math.isqrt(N)
    mids = [max(y, r) for y in ys]
    L = N + J
    edges, out = band_counts(L, ps, ys + mids + [L])
    full_cnt = omega_le(edges, out, L)
    frozen = [omega_le(edges, out, y) for y in ys]
    mid = [omega_le(edges, out, c) for c in mids]
    psN = ps[ps <= N]
    fresh = [float(np.sum(1.0 / psN[psN > y])) for y in ys]
    rho = float(np.sum(1.0 / psN[psN > r]))
    kmax = int(full_cnt.max()) + 1
    rows = []
    for h in hs:
        Wf = np.ones(N, dtype=np.complex128)
        Wy = np.ones(N, dtype=np.complex128)
        W1 = np.ones(N, dtype=np.complex128)
        S1 = np.zeros(N, dtype=np.complex128)  # sum_j (z_j^fresh_j(n+j) - 1)
        B = 0.0
        Fw = 0.0  # weighted fresh mass sum_j |z_j - 1| * S_P(y_j, N), PairSecondOrder's B_h
        GA = 0.0
        My_prod = 1.0
        GSD = GI = GI0 = 0.0 if delta is not None else complex("nan")
        My1_over_crt = F1 = complex("nan")
        for j in range(1, J + 1):
            z = np.exp(2j * math.pi * h / 4.0 ** j)
            tab = z ** np.arange(kmax)
            Wf *= tab[full_cnt[j:j + N]]
            Wy *= tab[frozen[j - 1][j:j + N]]
            W1 *= tab[mid[j - 1][j:j + N]]
            S1 += tab[full_cnt[j:j + N] - frozen[j - 1][j:j + N]] - 1
            B += abs(z - 1) * (2 * fresh[j - 1] + J / N)
            Fw += abs(z - 1) * fresh[j - 1]
            Mf = tab[full_cnt[j:j + N]].mean()
            My = tab[frozen[j - 1][j:j + N]].mean()
            GA += Mf / My - 1 if abs(My) > 1e-12 else complex("nan")
            My_prod *= My
            if delta is not None:
                y = ys[j - 1]
                u = math.log(N) / math.log(y) if y >= 2 else float("inf")
                F = dickman_F(delta * (z - 1), u)
                if j == 1:
                    frz = ps[ps <= y].astype(np.float64)
                    crt = np.prod(1 + (z - 1) / frz) if len(frz) else 1.0
                    My1_over_crt = My / crt if abs(crt) > 1e-12 else complex("nan")
                    F1 = F
                gsd = g_sd(delta, z - 1, N, ps, y, log_mertens(N))
                # at a pole 1/Gamma(1 + dw) = 0 makes gsd = -1 exactly, whatever F is
                GSD += -1 if gsd == -1 or not np.isfinite(F) or abs(F) < 1e-12 else (gsd + 1) / F - 1
                GI += g_dickman(delta, z - 1, a * 2.0 ** (-j))
                GI0 += g_inf(delta, z - 1, a * 2.0 ** (-j))
        W, Wyv, W1v = Wf.mean(), Wy.mean(), W1.mean()
        M = float(np.abs(Wf - Wy).mean())
        A = abs(W - Wyv)
        T1 = (Wy * S1).mean()
        T2 = W - Wyv - T1
        Sbar = S1.mean()
        G = T1 / Wyv if Wyv else complex("nan")
        C = T1 - Wyv * Sbar
        rows.append(dict(N=N, J=J, h=h, rho=rho, W=abs(W), Wy=abs(Wyv), A=A, M=M, B=B,
                         T1=abs(T1), T2=abs(T2), T2_over_rho2=abs(T2) / rho ** 2 if rho else float("nan"),
                         Fw=Fw, T2_over_Fw2=abs(T2) / Fw ** 2 if Fw else float("nan"),
                         A1=abs(W1v - Wyv), A2=abs(W - W1v),
                         A_over_M=A / M if M else float("nan"),
                         A_over_Wy=A / abs(Wyv) if abs(Wyv) else float("inf"),
                         G=G, Sbar=Sbar, C=C, Wy_c=Wyv, T1_c=T1, GA=GA, GSD=GSD, Ginf=GI, Ginf0=GI0, My1_over_crt=My1_over_crt, F1=F1,
                         My_prod_over_Wy=My_prod / Wyv if Wyv else complex("nan"),
                         C_over_T1=abs(C) / abs(T1) if T1 else float("nan")))
    return rows


def thinned(ps, theta):
    """Deterministic pseudo-random thinning: keep p iff frac(p * golden) < theta."""
    keep = ((ps.astype(np.float64) * 0.6180339887498949) % 1.0) < theta
    return ps[keep]


def prime_sets(ps):
    """(name, primes, density among primes)."""
    sets = [("all primes", ps, 1.0)]
    for q in (3, 5, 7, 11, 13, 23, 31, 61):
        phi = sum(1 for r in range(1, q) if math.gcd(r, q) == 1)
        sets.append((f"p = 1 mod {q}", ps[ps % q == 1], 1.0 / phi))
    sets.append(("p = 2 mod 31", ps[ps % 31 == 2], 1.0 / 30))
    for theta in (0.5, 0.25, 0.125, 0.0625, 0.03125):
        sets.append((f"thin {theta:g}", thinned(ps, theta), theta))
    return sets


def polar(c):
    return f"{abs(c):.3f}∠{math.degrees(np.angle(c)):.0f}°"


def rel(x, y):
    return abs(x - y) / abs(y) if abs(y) else float("nan")


def frozen_mean_ratio(N, P, z, y):
    """(1/N) sum_{1<=m<=N} z^#{p in P, p <= y, p | m}  over its CRT product prod_{p in P, p<=y} (1 + (z-1)/p).
    Tends to the generalized Dickman F_{d(z-1)}(log N / log y) (the frozen mean's size budget)."""
    small = P[P <= y]
    cnt = np.zeros(N + 1, dtype=np.int16)
    for q in small.tolist():
        cnt[q::q] += 1
    tab = np.asarray(z, dtype=np.complex128) ** np.arange(int(cnt.max()) + 1)
    mean = complex(tab[cnt[1:]].mean())
    crt = complex(np.prod(1 + (z - 1) / small.astype(np.float64))) if len(small) else 1.0
    return mean / crt


def report_frozen(args):
    """Frozen-mean ratio vs F_kappa(u) at y = N^(1/u), u = 2, 3: real z = 2 controls (kappa = d, where
    kappa = 1 is classical Dickman) and the probe's site-1 phases z = e(h/4)."""
    print("\n## Frozen mean / CRT product vs generalized Dickman F_kappa(u)")
    print("| N | set | z | u | kappa | My/CRT | F(u) | rel diff |")
    print("|---|---|---|---|---|---|---|---|")
    for lN in args.logN:
        N = 1 << lN
        ps = primes_upto(N)
        for name, P, d in prime_sets(ps):
            if args.sets is not None and name not in args.sets:
                continue
            zs = [("2", 2.0)] + [(f"e({h}/4)", complex(np.exp(2j * math.pi * h / 4))) for h in args.h]
            for zl, z in zs:
                for u in (2, 3):
                    y = int(round(N ** (1 / u)))
                    uu = math.log(N) / math.log(y)
                    r = frozen_mean_ratio(N, P, z, y)
                    F = dickman_F(d * (z - 1), uu)
                    print(f"| 2^{lN} | {name} | {zl} | {uu:.3f} | {d * (z - 1):.3f} | {polar(r)} | {polar(F)} | "
                          f"{rel(r, F):.4f} |")
                    sys.stdout.flush()


def extrapolate(Ls, Gs):
    """Fit G = G_oo + c / L (L = log N) through the last two points; return G_oo and the fit's miss at the
    first point, relative to |G_oo| (a check that the 1/log N form is right)."""
    (L1, G1), (L2, G2) = (Ls[-2], Gs[-2]), (Ls[-1], Gs[-1])
    c = (G1 - G2) / (1 / L1 - 1 / L2)
    Goo = G2 - c / L2
    miss = abs(Gs[0] - (Goo + c / Ls[0])) / abs(Goo) if len(Gs) > 2 and abs(Goo) else float("nan")
    return Goo, miss


def report_limit(args):
    """Per (set, h, a): measured G across N, its 1/log N extrapolation, and the two analytic limits."""
    Ns = [1 << lN for lN in args.logN]
    ps = primes_upto(max(Ns) + 64)
    sets = [(n, P, d) for n, P, d in prime_sets(ps) if args.sets is None or n in args.sets]
    print(f"\n## G = T1/W_y across N = 2^{args.logN}; G_oo fits G_oo + c/log N to the last two")
    print("| set | h | a | " + " | ".join(f"G at 2^{l}" for l in args.logN)
          + " | G_oo (fit) | fit miss | G_inf | G_inf0 | G_oo vs G_inf | G_oo vs G_inf0 |")
    print("|---|---|---|" + "---|" * len(Ns) + "---|---|---|---|---|---|")
    for name, P, d in sets:
        for a in args.a:
            per_h = {h: [] for h in args.h}
            lim = {}
            for N in Ns:
                for m in measure(N, P[P <= N + 64], args.h, a, delta=d):
                    per_h[m["h"]].append(m["G"])
                    lim[m["h"]] = (m["Ginf"], m["Ginf0"])
            for h in args.h:
                Goo, miss = extrapolate([math.log(N) for N in Ns], per_h[h])
                Gi, Gi0 = lim[h]
                print(f"| {name} | {h} | {a:g} | " + " | ".join(polar(g) for g in per_h[h])
                      + f" | {polar(Goo)} | {miss:.3f} | {polar(Gi)} | {polar(Gi0)} | "
                      f"{rel(Goo, Gi):.3f} | {rel(Goo, Gi0):.3f} |")
                sys.stdout.flush()


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--logN", type=int, nargs="+", default=[20, 22, 24])
    ap.add_argument("--h", type=int, nargs="+", default=[1, 3, 5])
    ap.add_argument("--a", type=float, nargs="+", default=[1.0])
    ap.add_argument("--sets", nargs="+", default=None,
                    help="keep only the prime sets with these exact names")
    ap.add_argument("--report", choices=["transfer", "relative", "sites", "limit", "frozen", "pair"], default="transfer")
    args = ap.parse_args(argv)
    if args.report == "limit":
        return report_limit(args)
    if args.report == "frozen":
        return report_frozen(args)
    for lN in args.logN:
        N = 1 << lN
        ps = primes_upto(N + 64)
        sets = [(n, P, d) for n, P, d in prime_sets(ps)
                if args.sets is None or n in args.sets]
        for a in args.a:
            print(f"\n## N = 2^{lN}, J = {window_J(N)}, y_j = N^({a:g}*2^-j)")
            if args.report == "transfer":
                print("| set | h | rho | abs W_y | abs W | A | M | B | A/M | A/abs W_y | A1 | A2 | T1 | T2 | T2/rho^2 |")
                print("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
            elif args.report == "pair":
                print("| set | h | rho | Fw | abs T2 | T2/rho^2 | T2/Fw^2 |")
                print("|---|---|---|---|---|---|---|")
            elif args.report == "relative":
                print("| set | h | rho | abs W_y | abs T1 | abs G | arg G (deg) | abs Sbar | arg Sbar (deg) | abs C / abs T1 |")
                print("|---|---|---|---|---|---|---|---|---|---|")
            else:
                print("| set | h | abs W_y | prod My / W_y | G | G_A | G_SD | G_inf | G_inf0 | G vs G_A | G_A vs G_SD | G_SD vs G_inf | G vs G_inf | site 1 My/CRT | F(u_1) |")
                print("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
            for name, P, d in sets:
                for m in measure(N, P, args.h, a, delta=d):
                    if args.report == "transfer":
                        print(f"| {name} | {m['h']} | {m['rho']:.4f} | {m['Wy']:.4f} | {m['W']:.4f} | "
                              f"{m['A']:.4f} | {m['M']:.4f} | {m['B']:.3f} | {m['A_over_M']:.3f} | "
                              f"{m['A_over_Wy']:.3f} | {m['A1']:.4f} | {m['A2']:.4f} | "
                              f"{m['T1']:.4f} | {m['T2']:.5f} | {m['T2_over_rho2']:.2f} |")
                    elif args.report == "pair":
                        print(f"| {name} | {m['h']} | {m['rho']:.4f} | {m['Fw']:.4f} | {m['T2']:.6f} | "
                              f"{m['T2_over_rho2']:.2f} | {m['T2_over_Fw2']:.3f} |")
                    elif args.report == "sites":
                        print(f"| {name} | {m['h']} | {m['Wy']:.4f} | {polar(m['My_prod_over_Wy'])} | "
                              f"{polar(m['G'])} | {polar(m['GA'])} | {polar(m['GSD'])} | {polar(m['Ginf'])} | "
                              f"{polar(m['Ginf0'])} | {rel(m['G'], m['GA']):.3f} | {rel(m['GA'], m['GSD']):.3f} | "
                              f"{rel(m['GSD'], m['Ginf']):.3f} | {rel(m['G'], m['Ginf']):.3f} | "
                              f"{polar(m['My1_over_crt'])} | {polar(m['F1'])} |")
                    else:
                        G, Sb = m["G"], m["Sbar"]
                        print(f"| {name} | {m['h']} | {m['rho']:.4f} | {m['Wy']:.4f} | {m['T1']:.4f} | "
                              f"{abs(G):.4f} | {math.degrees(np.angle(G)):.1f} | {abs(Sb):.4f} | "
                              f"{math.degrees(np.angle(Sb)):.1f} | {m['C_over_T1']:.3f} |")
                    sys.stdout.flush()


if __name__ == "__main__":
    main()
