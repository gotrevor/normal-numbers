"""C4 probe: block-i.i.d. sequences (the `blockSeq` class of AbelianWindowBlocks.lean).

s is read off a normal base-B sequence in blocks of q bits through a table g, so the blocks are
i.i.d. with law nu = pushforward of uniform, and n % q supplies the uniform offset.  For a window
of length L at offset r the weight generating function is

    gf_r(x) = Suf_r(x) * M(x)^k * Pre_b(x)

(suffix of the first block from position r, k whole blocks, prefix of length b of the last), with
M the full-block weight gf.  The process gf at length L is (1/q) sum_r gf_r, and
IsAbelianAt at L  <=>  that equals ((1+x)/2)^L.

Known-answer check: nu = uniform on {0,1}^q gives abelian at every L (the sequence is normal).
"""
from fractions import Fraction as F
from itertools import product

def pmul(a, b):
    r = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r

def ppow(a, n):
    r = [F(1)]
    for _ in range(n):
        r = pmul(r, a)
    return r

def u(n):
    """((1+x)/2)^n as a coefficient list."""
    from math import comb
    return [F(comb(n, i), 2 ** n) for i in range(n + 1)]

def seg_gf(nu, q, lo, hi):
    """weight gf of bits [lo,hi) of a nu-block."""
    g = [F(0)] * (hi - lo + 1)
    for w, p in nu.items():
        g[sum(w[lo:hi])] += p
    return g

def window_gf(nu, q, L):
    """(1/q) sum_r gf_r for window length L."""
    tot = [F(0)] * (L + 1)
    for r in range(q):
        if L <= q - r:
            g = seg_gf(nu, q, r, r + L)
        else:
            g = seg_gf(nu, q, r, q)
            rem = L - (q - r)
            k, b = divmod(rem, q)
            g = pmul(g, ppow(seg_gf(nu, q, 0, q), k))
            if b:
                g = pmul(g, seg_gf(nu, q, 0, b))
        for i, c in enumerate(g):
            tot[i] += c / q
    return tot

def abelian_at(nu, q, L):
    return window_gf(nu, q, L) == u(L)

def G(nu, q, Lmax):
    return tuple(L for L in range(1, Lmax + 1) if abelian_at(nu, q, L))

# known-answer check: uniform block law == normal sequence, abelian everywhere
for q in (1, 2, 3):
    nu = {w: F(1, 2 ** q) for w in product((0, 1), repeat=q)}
    assert G(nu, q, 10) == tuple(range(1, 11)), (q, G(nu, q, 10))

LMAX = 13
for q in (2, 3):
    words = list(product((0, 1), repeat=q))
    seen = {}
    for B in (8, 16) if q == 2 else (8,):
        # enumerate integer count vectors summing to B
        def rec(i, left, acc):
            if i == len(words) - 1:
                yield acc + [left]
                return
            for c in range(left + 1):
                yield from rec(i + 1, left - c, acc + [c])
        for counts in rec(0, B, []):
            nu = {w: F(c, B) for w, c in zip(words, counts) if c}
            g = G(nu, q, LMAX)
            if g and g not in seen:
                seen[g] = (B, counts)
    print(f"q={q}: realizable G up to L={LMAX}")
    for g in sorted(seen, key=lambda t: (len(t), t)):
        print("   ", g, " nu:", seen[g])
