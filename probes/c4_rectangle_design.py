"""C4 probe: the RECTANGLE DESIGN -- a block law excluding a PRESCRIBED FINITE set of lengths.

Framework (derived 2026-09-25).  Let nu be a law on {0,1}^q, and run the block-i.i.d. process
(i.i.d. nu-blocks, uniform offset) as in `c4_block_iid.py`.  Write nu in Fourier coordinates,
nuhat(U) = E[(-1)^{sum_{i in U} x_i}], and for an interval I = [p,p+L) inside a block set

    W_I(x) = sum_{U subset I} nuhat(U) x^{|U|}.

Then the window "defect" polynomial is  Phi_L(x) = (1/q) sum_r prod_b W_{I_b^{(r)}}(x), and
IsAbelianAt at L  <=>  Phi_L = 1.  Every trace of a window on a block is a prefix, a suffix, a
full block, or (only when L < q) an interior interval.  So:

    if W_I = 1 for every PREFIX and every SUFFIX I (hence for the full block),
    then the only possible defects come from interior intervals.

Rectangle design: for m1 < m2 <= M1 < M2 put nuhat on the four pairs
    {m1,M1}: +c   {m1,M2}: -c   {m2,M1}: -c   {m2,M2}: +c
Then  sum_U c_U [U subset [p,p+L)] = c*([p<=m1]-[p<=m2])*([P>=M1]-[P>=M2]),  P = p+L-1,
which for m2=m1+1, M2=M1+1 is  -c*[p=m2]*[P=M1]: a single interval, [m2,M1], of length
a = M1-m2+1.  Prefixes have p=0 and suffixes have P=q-1, so choosing m2>=1 and M1<=q-2 makes
every prefix/suffix W trivial.  Superposing such rectangles for distinct a is linear and the
defects land at distinct lengths, so ANY finite D subset [2, q-2] can be the exact defect set.

Design used here for D: for each a in D, (m1,m2,M1,M2) = (0,1,a,a+1), coefficient c_a,
with sum_a 4*c_a <= 1 so that nu >= 0.  q = max(D)+2.

Known-answer check: D = {} gives nu = uniform, abelian at every L (a normal sequence).
"""
from fractions import Fraction as F
from itertools import product
from math import comb

import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from c4_block_iid import window_gf, u


def rect_law(q, D, cs):
    """nu on {0,1}^q from the superposed rectangle design for defect set D."""
    nu = {}
    for w in product((0, 1), repeat=q):
        val = F(1)
        for a, c in zip(D, cs):
            # (chi_{m1} - chi_{m2}) * (chi_{M1} - chi_{M2}) with (m1,m2,M1,M2)=(0,1,a,a+1)
            s = ((-1) ** w[0] - (-1) ** w[1]) * ((-1) ** w[a] - (-1) ** w[a + 1])
            val += c * s
        nu[w] = val / F(2 ** q)
    assert sum(nu.values()) == 1
    assert all(p >= 0 for p in nu.values()), "law not nonnegative"
    return nu


def defect_set(nu, q, Lmax):
    out = []
    for L in range(1, Lmax + 1):
        if window_gf(nu, q, L) != u(L):
            out.append(L)
    return out


def run(D):
    q = (max(D) + 2) if D else 3
    cs = [F(1, 4 * len(D)) for _ in D] if D else []
    nu = rect_law(q, D, cs)
    got = defect_set(nu, q, 4 * q)
    print(f"D={D!s:14s} q={q}  defects up to {4*q}: {got}")
    assert got == sorted(D), f"MISMATCH: wanted {sorted(D)}, got {got}"


if __name__ == "__main__":
    # known-answer check: uniform law is abelian everywhere
    run([])
    for D in ([2], [3], [4], [5], [2, 3], [2, 4], [3, 5], [2, 3, 4], [2, 4, 5], [2, 3, 4, 5, 6]):
        run(D)
    print("all rectangle designs verified")
