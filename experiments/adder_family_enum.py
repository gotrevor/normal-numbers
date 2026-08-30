#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""Probe: enumerate the FAMILY of collapsing adder disjunctions (Babel W1b).

Extends adder_collapse_hunt.py three ways:
  1. distance-1 enumeration around the found six-channel family (swap one
     word, keep the rest) - how many exact-collapse neighbors exist;
  2. an alternative positive channel set (ln 2, 3, 6, 12, 24, 72);
  3. BORROW channels (negative coefficients) - the superparticular family
     ln(3/2), ln(4/3), ln(9/8) alongside ln 2, ln 3, ln 6.

Soundness note for mixed signs: T(n) = floor(2^n z) - a floor(2^n X)
- b floor(2^n Y) lies in [neg(a)+neg(b), pos(a-1)+pos(b-1)+1] (superset used
below); v = a x + b y + c, digit v mod 2, carry v div 2 (floor), out-of-range
carry = dead (true carries never leave the range, so the automaton contains
every true path; a superset automaton with h = 0 is still a valid collapse).

UNIVERSALITY (the reframing this probe documents): a collapsing family
(a_i, b_i, w_i) proves, for ANY reals X, Y not both rational: at least one
w_i occurs infinitely often in the binary expansion of a_i X + b_i Y.
(ln 2, ln 3) is the naming instance; (pi, e) etc. are free instances.
"""

import sys
from math import log2
import numpy as np
from adder_collapse_hunt import joint_entropy, build_nxts

WORDS_OPEN = ["00", "11", "000", "001", "010", "011", "100", "101", "110", "111"]
STATE_CAP = 8_000_000


def kmp_next(word: str):
    ell = len(word)
    fail = [0] * ell
    for i in range(1, ell):
        s = fail[i - 1]
        while s and word[i] != word[s]:
            s = fail[s - 1]
        fail[i] = s + 1 if word[i] == word[s] else 0
    table = [[0, 0] for _ in range(ell)]
    for s in range(ell):
        for z in (0, 1):
            zc = str(z)
            t = s
            while t and word[t] != zc:
                t = fail[t - 1]
            table[s][z] = t + 1 if word[t] == zc else 0
    return table


class GenChannel:
    """(a, b, word) with a, b any nonzero-allowed integers (a,b) != (0,0)."""

    def __init__(self, a: int, b: int, word: str):
        self.a, self.b, self.word = a, b, word
        rev = word[::-1]
        ac_table = kmp_next(rev)
        n_ac = len(rev)
        c_min = (a if a < 0 else 0) + (b if b < 0 else 0)
        c_max = ((a - 1) if a > 0 else 0) + ((b - 1) if b > 0 else 0) + 1
        self.c_min, self.c_max = c_min, c_max
        n_carry = c_max - c_min + 1
        self.n_states = n_ac * n_carry
        nxt = np.full((self.n_states, 4), -1, dtype=np.int64)
        for ci in range(n_carry):
            c = c_min + ci
            for ac in range(n_ac):
                s = ci * n_ac + ac
                for sym in range(4):
                    x, y = sym & 1, sym >> 1
                    v = a * x + b * y + c
                    z = v % 2
                    c2 = v // 2
                    if not (c_min <= c2 <= c_max):
                        continue
                    ac2 = ac_table[ac][z]
                    if ac2 == n_ac:
                        continue
                    nxt[s, sym] = (c2 - c_min) * n_ac + ac2
        self.nxt = nxt


def exact_zero(channels) -> tuple[bool, int, list[int]]:
    """Exact integer check: (is h=0, live states, sorted cycle periods)."""
    from scipy.sparse import csr_matrix
    from scipy.sparse.csgraph import connected_components

    S, nxts = build_nxts(channels)
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
    g = csr_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)), shape=(S, S))
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


def greedy(channels_ab, name):
    print(f"\n--- greedy on {name} ---")
    chosen = []
    for (a, b) in channels_ab:
        best = None
        for w in WORDS_OPEN:
            trial = chosen + [GenChannel(a, b, w)]
            if int(np.prod([c.n_states for c in trial])) > STATE_CAP:
                continue
            h = joint_entropy(trial)
            if np.isnan(h):
                continue
            if best is None or h < best[0]:
                best = (h, w, trial)
        if best is None:
            print(f"  ({a},{b}): cap hit, stop")
            break
        h, w, chosen = best
        print(f"  +({a:>2},{b:>2}) word '{w}':  h = {h:.4f}")
        if h <= 1e-3:
            ok, live, periods = exact_zero(chosen)
            if ok:
                print(f"  *** EXACT COLLAPSE ({live} live states, periods {periods}) ***")
                for c in chosen:
                    print(f"      2^{c.a} 3^{c.b} avoids '{c.word}'")
            else:
                print("  float zero but exact check FAILED - not a collapse")
            return ok
    print("  no collapse; floor h =", f"{joint_entropy(chosen):.4f}" if chosen else "-")
    return False


def main() -> None:
    base = [(1, 0, "00"), (0, 1, "001"), (1, 1, "11"),
            (1, 2, "001"), (2, 1, "010"), (1, 3, "000")]
    base_ch = [GenChannel(a, b, w) for a, b, w in base]

    # regression: the found family, on the generalized channel class
    ok, live, periods = exact_zero(base_ch)
    assert ok, "regression FAILED: base family no longer collapses"
    print(f"regression OK: base family exact h=0 ({live} live, periods {periods})")

    # --- 1. distance-1 neighbors ---------------------------------------------
    print("\ndistance-1 enumeration (swap one word, exact-check float zeros):")
    n_collapse = 0
    collapsing = []
    for i in range(6):
        a, b, w0 = base[i]
        for w in WORDS_OPEN:
            if w == w0:
                continue
            fam = [GenChannel(*base[j]) if j != i else GenChannel(a, b, w)
                   for j in range(6)]
            h = joint_entropy(fam)
            if h <= 1e-3:
                ok, live, periods = exact_zero(fam)
                if ok:
                    n_collapse += 1
                    collapsing.append((i, a, b, w))
    print(f"  exact-collapsing neighbors: {n_collapse} / 54")
    for i, a, b, w in collapsing:
        print(f"    channel (2^{a} 3^{b}): '{base[i][2]}' -> '{w}'")

    # --- 2. alternative positive set ------------------------------------------
    greedy([(1, 0), (0, 1), (1, 1), (2, 1), (3, 1), (3, 2)],
           "ln2, ln3, ln6, ln12, ln24, ln72")

    # --- 3. superparticular set (borrow channels) ------------------------------
    greedy([(1, 0), (0, 1), (-1, 1), (2, -1), (-3, 2), (1, 1)],
           "ln2, ln3, ln(3/2), ln(4/3), ln(9/8), ln6  [borrows]")

    print("\nUNIVERSALITY: every exact collapse above is a theorem-candidate for")
    print("ANY reals X, Y not both rational (instances: (ln2,ln3), (pi,e), ...)")
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
