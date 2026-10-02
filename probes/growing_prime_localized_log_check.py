#!/usr/bin/env -S uv run --quiet python3
"""Checks backing docs/GROWING-PRIME-LOCALIZED-LOG-AUDIT-2026-10-02.md.

1. Vandehey (arXiv:1606.07911) Theorem 5.1 exponent recursion: recompute alpha_k, gamma_k, nu_k
   exactly and compare with the constant c of eq. (17) and the Lemma 6.3 table printed in the
   paper (values hand-transcribed from the PDF, pp. 19-20, not from this script).
2. Arithmetic steps 2-3 of the zeta_Y skeleton with a VARYING smoothness bound Y(m): off the
   2-adic exceptional set the truncation R_n has odd denominator, 3-adic valuation exactly
   -floor(log_3 n), and prime support inside the primes <= Y(n).  Expected values come from the
   hand derivation in the audit doc, section 3.

Run: probes/growing_prime_localized_log_check.py   (exits nonzero on any failure)
"""
from fractions import Fraction as F
import math, sys

fails = 0
def check(cond, msg):
    global fails
    if not cond:
        fails += 1
        print("FAIL:", msg)

# ---- 1. Vandehey recursion -------------------------------------------------------------
a, g, v = [F(1, 2)], [F(0)], [F(1)]
for k in range(1, 40):
    A, G, V = a[-1], g[-1], v[-1]
    g.append((1 + G + A * V) / (2 * (1 + A)))
    v.append((1 + V) / 2 + (1 + G - V) * A / (2 * (1 + A)))
    a.append(F(1, 2 ** (k + 2) - 2))
    check(a[-1] == A / (2 * (1 + A)), f"alpha_{k} closed form")
    check(g[-1] + v[-1] == 2 - F(1, 2 ** k), f"eq (15) at k={k}")
K = 39
c_est = float((v[K] - g[K]) * 2 ** (K + 1)) - K - 1
c = -1.17094960687104654952          # eq. (17), as printed
check(abs(c_est - c) < 1e-6, f"c from recursion {c_est} vs eq (17) {c}")
# Lemma 6.3 table (paper p.20): alpha_k(k+c+2)+gamma_k-1 and -alpha_k(k+c+1)+nu_k-1
paper_first = {1: -0.195158, 2: -0.0836393, 3: -0.0378412, 4: -0.0176574, 5: -0.0084263, 6: -0.0040877}
paper_second = {1: -0.138175, 2: -0.0949322, 3: -0.0538255, 4: -0.0287136, 5: -0.0148872}
for k, val in paper_first.items():
    got = float(a[k]) * (k + c + 2) + float(g[k]) - 1
    check(abs(got - val) < 5e-7, f"Lemma 6.3 first table k={k}: {got} vs {val}")
    check(got <= -1 / 2 ** (k + 3), f"Lemma 6.3 first inequality k={k}")
for k, val in paper_second.items():
    got = -float(a[k]) * (k + c + 1) + float(v[k]) - 1
    check(abs(got - val) < 5e-7, f"Lemma 6.3 second table k={k}: {got} vs {val}")
    check(got <= -1 / 2 ** (k + 3), f"Lemma 6.3 second inequality k={k}")

# ---- 2. arithmetic of zeta_Y with varying Y ------------------------------------------------
def Y(m):                      # nondecreasing, >= 3, jumps inside the range
    return 3 if m < 60 else 5 if m < 400 else 7 if m < 1500 else 11

def pplus(m):
    best, d = 1, 2
    while d * d <= m:
        while m % d == 0:
            best, m = d, m // d
        d += 1
    return max(best, m) if m > 1 else best

def v_p(x, p):
    e = 0
    while x % p == 0:
        x //= p; e += 1
    return e

primes_upto = lambda y: [p for p in range(2, y + 1) if all(p % q for q in range(2, int(p ** .5) + 1))]
NMAX = 4000
retained = [False] + [pplus(m) <= Y(m) for m in range(1, NMAX + 1)]
B = math.ceil(math.log2(2 * NMAX)) + 1
exceptional = set()
for m in range(1, NMAX + 1):
    if retained[m]:
        exceptional.update(range(m, m + B))
R = F(0)
checked = 0
for n in range(1, NMAX + 1):
    R = 2 * R + (F(1, n) if retained[n] else 0)
    if n < 16 or n in exceptional:
        continue
    q = R.denominator
    k3 = 0
    while 3 ** (k3 + 1) <= n:
        k3 += 1
    check(q % 2 == 1, f"n={n}: denominator even off E")
    check(v_p(q, 3) == k3, f"n={n}: v_3(q)={v_p(q,3)} expected {k3}")
    rest = q
    for p in primes_upto(Y(n)):
        while rest % p == 0:
            rest //= p
    check(rest == 1, f"n={n}: prime support of q escapes primes <= Y(n)={Y(n)}")
    check(math.log(q) <= (len(primes_upto(Y(n))) - 1) * math.log(n) + 1e-9, f"n={n}: log q too big")
    checked += 1
check(checked > 100, f"only {checked} nonexceptional shifts checked")

print(f"{'OK' if not fails else 'FAILED'}: {fails} failures; {checked} nonexceptional shifts checked")
sys.exit(1 if fails else 0)
