#!/usr/bin/env -S uv run --quiet --with numpy python3
"""Prototype of Brier et al. Algorithm 1 (stage 1: positions mod 12, modulus
m12 = (10^12-1)/189) adapted to an even target: RHS = 2^t 3^(u+2) 7^w with
0 <= t <= tmax (Fonga), i.e. LHS = 9y = 10^a0 - 1 + sum 9(d_i-1) 10^a_i.

Uses the multiset symmetry (identical digits -> multisets of residues).
Measures throughput and the stage-1 pass rate with and without the 2^t factor.

usage: stage1.py '<json digit->count>' tmax [known_y ...]
"""
import sys, json, time, itertools, math
import numpy as np

m12 = (10**12 - 1) // 189
assert m12 == 11 * 13 * 37 * 101 * 9901

def subgroup37():
    u = np.arange(9900, dtype=object)
    p3 = np.array([pow(3, int(i), m12) for i in range(9900)], dtype=np.int64)
    p7 = np.array([pow(7, int(i), m12) for i in range(900)], dtype=np.int64)
    # products mod m12 (< 2^33, product < 2^66 -> use object-free trick: split)
    out = np.empty(9900 * 900, dtype=np.int64)
    for j, b in enumerate(p7):
        out[j * 9900:(j + 1) * 9900] = (p3.astype(object) * int(b) % m12).astype(np.int64)
    return np.unique(out)

def mulmod(a, c):
    """a: int64 array < m12 (< 2^33); c: python int < m12.  exact (a*c) % m12 without overflow."""
    ch, cl = divmod(c, 1 << 16)
    return ((a * ch % m12) * (1 << 16) % m12 + a * cl % m12) % m12

def digit_contribs(d, n):
    """all multisets of n residues mod 12 -> sum 9(d-1)10^r mod m12"""
    vals = []
    for combo in itertools.combinations_with_replacement(range(12), n):
        vals.append(sum(9 * (d - 1) * pow(10, r, m12) for r in combo) % m12)
    return np.array(vals, dtype=np.int64)

def main():
    D = {int(k): v for k, v in json.loads(sys.argv[1]).items()}
    tmax = int(sys.argv[2])
    known = [int(x) for x in sys.argv[3:]]
    t0 = time.time()
    G = subgroup37()
    tG = time.time() - t0
    print(f"|<3,7> mod m12| = {len(G)}  (m12 = {m12}; built in {tG:.1f}s); "
          f"odd-target pass rate ~ {len(G)/m12:.2e}")
    # LHS partial sums
    acc = np.array([(pow(10, r, m12) - 1) % m12 for r in range(12)], dtype=np.int64)  # a0 residue
    for d, n in D.items():
        if n:
            c = digit_contribs(d, n)
            acc = ((acc[:, None] + c[None, :]) % m12).ravel()
    n_tuples = len(acc)
    t1 = time.time()
    # RHS: 2^t * 9 * g, g in G.  test  LHS * inv(9 * 2^t) in G
    inv9 = pow(9, -1, m12)
    survivors_by_t = []
    for t in range(tmax + 1):
        mult = inv9 * pow(pow(2, t, m12), -1, m12) % m12
        x = mulmod(acc, mult)
        if True:
            idx = np.searchsorted(G, x); idx[idx == len(G)] = 0
            survivors_by_t.append(int((G[idx] == x).sum()))
    dt = time.time() - t1
    tot = sum(survivors_by_t)
    print(f"family {D}: tuples (multiset-reduced) = {n_tuples:,}; t in [0,{tmax}]")
    print(f"  survivors at t=0 only: {survivors_by_t[0]:,} ({survivors_by_t[0]/n_tuples:.2e});"
          f" summed over t: {tot:,} ({tot/n_tuples:.2e})")
    print(f"  stage-1 time {dt:.1f}s  -> {n_tuples*(tmax+1)/dt:,.0f} (tuple,t) checks/s in numpy")
    k1 = sum(D.values()) + 1
    print(f"  lifting to mod 24 would branch each survivor 2^{k1} = {2**k1:,} ways"
          f" -> {tot * 2**k1:,.3g} stage-2 candidates (naive)")
    for y in known:
        Y = 9 * y
        t = (Y & -Y).bit_length() - 1
        x = (Y % m12) * inv9 * pow(pow(2, t, m12), -1, m12) % m12
        i = int(np.searchsorted(G, x))
        ok = i < len(G) and int(G[i]) == x
        print(f"  known solution y={y}: v2={t}, stage-1 membership: {ok}")

if __name__ == "__main__":
    main()
