#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""Probe: the adder machine in BASE 3 - single-digit disjunctions (Babel #4).

In base 3 the open-word frontier drops to length ONE: an irrational may avoid
a ternary digit forever (Cantor middle-thirds), so "digit d occurs i.o." is
open for every specific constant and every d.  The machine is base-agnostic:
digit z = v mod 3, carry c' = v div 3, carry range [a^- + b^-, a^+ + b^+]
(fixed points of the min/max recursions; superset automaton is sound as in
adder_family_enum).

HEADLINE HUNT (escape-from-Cantor): all channels avoid digit 1.  A collapse
proves: for ANY reals X, Y not both rational, at least one channel a*X + b*Y
contains ternary digit 1 infinitely often.  Digit 1 is self-complementary
under the base-3 involution d -> 2-d, so this tuple is its own twin.
Blocking-pair sanity: coefficient m with ternary digit 1 in bin3(m) realizes
digit 1 on the sparse pair (m=1 works), so no known blocking pair forbids it.

Also hunted: general single-digit assignments (exhaustive per channel set),
then mixed words of length <= 2 by greedy if needed.

Self-tests: h(full) = log2(9); avoid-digit-2 on one track = log2(6);
independence additivity; base-3 complement involution h(w) = h(w-bar).
"""

import sys
import time
from itertools import product as iproduct
from math import log2
import numpy as np

G = 3
NSYM = G * G  # (x, y) digit pairs
STATE_CAP = 4_000_000
POWER_ITERS = 120


def kmp3(word: str):
    ell = len(word)
    fail = [0] * ell
    for i in range(1, ell):
        s = fail[i - 1]
        while s and word[i] != word[s]:
            s = fail[s - 1]
        fail[i] = s + 1 if word[i] == word[s] else 0
    table = [[0] * G for _ in range(ell)]
    for s in range(ell):
        for z in range(G):
            zc = str(z)
            t = s
            while t and word[t] != zc:
                t = fail[t - 1]
            table[s][z] = t + 1 if word[t] == zc else 0
    return table


class Channel3:
    """(a, b, word) over base-3 two-track streams; word over {0,1,2}."""

    def __init__(self, a: int, b: int, word: str):
        self.a, self.b, self.word = a, b, word
        rev = word[::-1]
        ac_table = kmp3(rev)
        n_ac = len(rev)
        c_min = min(a, 0) + min(b, 0)
        c_max = max(a, 0) + max(b, 0)
        self.c_min, self.c_max = c_min, c_max
        n_carry = c_max - c_min + 1
        self.n_states = n_ac * n_carry
        nxt = np.full((self.n_states, NSYM), -1, dtype=np.int64)
        for ci in range(n_carry):
            c = c_min + ci
            for ac in range(n_ac):
                s = ci * n_ac + ac
                for sym in range(NSYM):
                    x, y = sym % G, sym // G
                    v = a * x + b * y + c
                    z = v % G
                    c2 = v // G
                    if not (c_min <= c2 <= c_max):
                        continue
                    ac2 = ac_table[ac][z]
                    if ac2 == n_ac:
                        continue
                    nxt[s, sym] = (c2 - c_min) * n_ac + ac2
        self.nxt = nxt


def build_nxts3(channels):
    sizes = [ch.n_states for ch in channels]
    S = int(np.prod(sizes)) if channels else 1
    idx = np.arange(S, dtype=np.int64)
    digits = []
    rem = idx
    for ch in channels:
        digits.append(rem % ch.n_states)
        rem = rem // ch.n_states
    nxts = []
    for sym in range(NSYM):
        nx = np.zeros(S, dtype=np.int64)
        dead = np.zeros(S, dtype=bool)
        mult = 1
        for d, ch in zip(digits, channels):
            step = ch.nxt[d, sym]
            dead |= step < 0
            nx += np.where(step < 0, 0, step) * mult
            mult *= ch.n_states
        nx[dead] = -1
        nxts.append(nx)
    return S, nxts


def entropy3(channels, iters=POWER_ITERS) -> float:
    S = int(np.prod([c.n_states for c in channels])) if channels else 1
    if S > STATE_CAP:
        return float("nan")
    S, nxts = build_nxts3(channels)
    v = np.ones(S, dtype=np.float64)
    growth = []
    for _ in range(iters):
        w = np.zeros(S, dtype=np.float64)
        for nx in nxts:
            live = nx >= 0
            np.add.at(w, nx[live], v[live])
        total = w.sum()
        if total == 0:
            return float("-inf")
        growth.append(total / v.sum() if v.sum() else 0)
        v = w / total * S
    lam = float(np.median(growth[-20:]))
    return log2(lam) if lam > 0 else float("-inf")


def exact_zero3(channels):
    from scipy.sparse import csr_matrix
    from scipy.sparse.csgraph import connected_components

    S, nxts = build_nxts3(channels)
    alive = np.ones(S, dtype=bool)
    while True:
        out_deg = np.zeros(S, dtype=np.int64)
        for nx in nxts:
            ok = (nx >= 0) & alive
            ok[ok] &= alive[nx[ok]]
            out_deg += ok
        new_alive = alive & (out_deg > 0)
        if new_alive.sum() == alive.sum():
            break
        alive = new_alive
    rows, cols = [], []
    for nx in nxts:
        ok = (nx >= 0) & alive
        ok[ok] &= alive[nx[ok]]
        src = np.flatnonzero(ok)
        rows.append(src)
        cols.append(nx[src])
    rows, cols = np.concatenate(rows), np.concatenate(cols)
    if len(rows) == 0:
        return True, 0, []
    g = csr_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)),
                   shape=(S, S))
    n_comp, labels = connected_components(g, directed=True, connection="strong")
    same = labels[rows] == labels[cols]
    intra_out = np.bincount(rows[same], minlength=S)
    comp_size = np.bincount(labels[alive], minlength=n_comp)
    periods = []
    for comp in np.flatnonzero(comp_size > 0):
        members = np.flatnonzero((labels == comp) & alive)
        intra = intra_out[members]
        if len(members) == 1 and intra[0] == 0:
            continue
        if not (intra == 1).all():
            return False, int(alive.sum()), []
        periods.append(len(members))
    return True, int(alive.sum()), sorted(set(periods))


POOL = [(a, b) for a in range(4) for b in range(4) if (a, b) != (0, 0)]


def main() -> None:
    # --- self-tests -------------------------------------------------------
    h0 = entropy3([])
    assert abs(h0 - log2(9)) < 1e-9, h0
    h1 = entropy3([Channel3(1, 0, "2")])
    assert abs(h1 - log2(6)) < 1e-3, h1  # x-track on {0,1}, y free
    h2 = entropy3([Channel3(1, 0, "2"), Channel3(0, 1, "2")])
    assert abs(h2 - log2(4)) < 1e-3, h2  # independence additivity
    # base-3 complement involution: d -> 2-d
    ha = entropy3([Channel3(1, 2, "01"), Channel3(2, 1, "2")])
    hb = entropy3([Channel3(1, 2, "21"), Channel3(2, 1, "0")])
    assert abs(ha - hb) < 5e-3, (ha, hb)
    print(f"self-tests OK (log2(9), Cantor track log2(6), additivity, "
          f"involution {ha:.4f}={hb:.4f})\n")

    # --- headline: all channels avoid digit 1 (escape from Cantor) --------
    print("HEADLINE greedy: every channel avoids ternary digit 1")
    chosen = []
    for step in range(10):
        best = None
        for cand in POOL:
            if cand in [(c.a, c.b) for c in chosen]:
                continue
            trial = chosen + [Channel3(*cand, "1")]
            h = entropy3(trial)
            if np.isnan(h):
                continue
            if best is None or h < best[0]:
                best = (h, cand, trial)
        if best is None:
            print("  cap hit")
            break
        h, cand, chosen = best
        print(f"  +{cand}: h = {h:.4f}")
        if h <= 1e-3:
            ok, live, periods = exact_zero3(chosen)
            if ok:
                print(f"\n*** EXACT COLLAPSE ({live} live, periods {periods}) "
                      "***")
                print("*** CANDIDATE THEOREM: for any reals X, Y not both "
                      "rational, at least one channel below contains ternary "
                      "digit 1 infinitely often: ***")
                for c in chosen:
                    print(f"      {c.a}*X + {c.b}*Y   (instance ln(2^{c.a} "
                          f"3^{c.b}))")
            else:
                print("  float zero but exact check FAILED")
            break
    else:
        print(f"  floor after 10 channels: {entropy3(chosen):.4f}")

    # --- general single-digit assignments on the chosen-size sets ----------
    print("\ngeneral greedy: channels free to avoid ANY single digit")
    chosen = []
    for step in range(10):
        best = None
        for cand in POOL:
            if cand in [(c.a, c.b) for c in chosen]:
                continue
            for w in "012":
                trial = chosen + [Channel3(*cand, w)]
                h = entropy3(trial)
                if np.isnan(h):
                    continue
                if best is None or h < best[0]:
                    best = (h, cand, w, trial)
        if best is None:
            print("  cap hit")
            break
        h, cand, w, chosen = best
        print(f"  +{cand} avoid '{w}': h = {h:.4f}")
        if h <= 1e-3:
            ok, live, periods = exact_zero3(chosen)
            verdict = (f"EXACT ({live} live, periods {periods})" if ok
                       else "float only - FAILED exact")
            print(f"  {verdict}")
            if ok:
                print("*** CANDIDATE THEOREM: for any reals X, Y not both "
                      "rational, at least one channel realizes its ternary "
                      "digit i.o.: ***")
                for c in chosen:
                    print(f"      digit {c.word} in {c.a}*X + {c.b}*Y   "
                          f"(instance ln(2^{c.a} 3^{c.b}))")
            break
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
