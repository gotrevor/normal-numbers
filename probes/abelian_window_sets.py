#!/usr/bin/env -S uv run --quiet --with python-flint python3
"""Which SETS of window lengths can a binary sequence be abelian-normal at, and only there?

Abelian at L: the one-count of a length-L window is Binomial(L, 1/2) in the limit.  Work near
the uniform measure: a stationary law on k-blocks is the k-marginal of an order-(k−1) Markov
chain, and every small stationary perturbation with full support is realized by such a chain,
hence (a.s. sample path, or a deterministic typical concatenation) by an actual sequence.

Tangent space V = signed μ on {0,1}^k, total mass 0, left (k−1)-marginal = right.  For L ≤ k let
A_L μ = (Σ_{|w|=j} μ_L(w))_j, the count-law deviation of the L-marginal.  "Abelian exactly on S"
is realizable (locally) iff W_S = ∩_{L∈S} ker A_L is not inside ker A_L for any L ∉ S (then a
generic element of W_S violates every L ∉ S; finitely many proper subspaces don't cover W_S).
Exact integer ranks (flint fmpz_mat).  Usage: abelian_window_sets.py k
"""
import sys, itertools
from flint import fmpz_mat as fmpq_mat, fmpz as fmpq  # integer matrices: every basis stays integral

k = int(sys.argv[1]) if len(sys.argv) > 1 else 6
words = list(itertools.product((0, 1), repeat=k))
idx = {w: i for i, w in enumerate(words)}
n = len(words)

# constraints defining V: total mass 0, left marginal = right marginal
rows = [[1] * n]
for u in itertools.product((0, 1), repeat=k - 1):
    r = [0] * n
    for a in (0, 1):
        r[idx[u + (a,)]] += 1   # left (k−1)-marginal: first k−1 letters = u
        r[idx[(a,) + u]] -= 1   # right: last k−1 letters = u
    rows.append(r)


def nullspace(rowlist, ncols):
    M = fmpq_mat(len(rowlist), ncols, [fmpq(x) for r in rowlist for x in r])
    X, nul = M.nullspace()
    return [[X[i, j] for i in range(ncols)] for j in range(nul)]


V = nullspace(rows, n)  # basis of V as vectors in R^n


def A(L):
    """Rows of A_L acting on R^n (L-marginal = first L letters, by stationarity)."""
    out = []
    for j in range(L + 1):
        out.append([1 if sum(w[:L]) == j else 0 for w in words])
    return out


def rank(rowlist, basis):
    """rank of the map (rows) restricted to span(basis)."""
    if not basis or not rowlist:
        return 0
    M = fmpq_mat(len(rowlist), len(basis),
                 [sum(fmpq(r[i]) * b[i] for i in range(n)) for r in rowlist for b in basis])
    return M.rank()


def W(S):
    if not S:
        return V
    cons = [r for L in S for r in A(L)]
    M = fmpq_mat(len(cons), len(V), [sum(fmpq(r[i]) * b[i] for i in range(n)) for r in cons for b in V])
    X, nul = M.nullspace()
    return [[sum(X[i, j] * V[i][t] for i in range(len(V))) for t in range(n)] for j in range(nul)]


print(f"k={k}: dim V = {len(V)}")
Ls = range(1, k + 1)
ok, bad = [], []
for r in range(0, k + 1):
    for S in itertools.combinations(Ls, r):
        WS = W(S)
        viol = [L for L in Ls if L not in S and rank(A(L), WS) == 0]
        (bad if viol else ok).append((S, len(WS), viol))
print(f"realizable exact sets ({len(ok)}):")
for S, d, _ in ok:
    print(f"  S={set(S) or '{}'}  dim W_S={d}")
print(f"NOT realizable ({len(bad)}), with the lengths S forces:")
for S, d, v in bad:
    print(f"  S={set(S) or '{}'} forces {v}")
