#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""Probe: the adder-wing collapse hunt (Babel W1).

Object: two-track bit streams (x, y) standing for the binary digits of a pair
(X, Y) on the torus.  Each channel (a, b, w) demands that the bit stream of
frac(aX + bY) avoid the word w; carries couple the tracks, and the whole
family constraint is one deterministic finite automaton over the 4-letter
alphabet (x_n, y_n), read in the direction of carry flow.  The joint system
S_F is sofic: entropy computable by power iteration, and

    SHARPENED W2 CRITERION (found while building this probe):
    h(S_F) = 0 already suffices.  A zero-entropy sofic system has every
    infinite path eventually trapped in a simple cycle, hence every stream
    eventually periodic.  The (ln 2, ln 3) pair stream is aperiodic
    (irrationality, and irrationality of log2 3), so h(S_F) = 0 would prove
    UNCONDITIONALLY: at least one constant among the channel family
    {ln(2^a 3^b)} realizes its word infinitely often in binary.

This hunt: channels fixed in order of coefficient size, the word for each
added channel chosen greedily (all words of length 2, and length 3 while the
state space stays small) to minimize joint entropy.  Reported: the decay
curve h vs number of channels, and the verdict (floor or collapse).

Channel constants: (1,0)=ln2, (0,1)=ln3, (1,1)=ln6, (1,2)=ln18, (2,1)=ln12,
(1,3)=ln54, (3,1)=ln24.

Self-tests: h(full shift) = 2; h((1,0) avoid 11) = 1 + log2(golden) ~ 1.6942;
two independent track constraints add.
"""

import sys
from math import log2
import numpy as np

CHANNELS = [(1, 0), (0, 1), (1, 1), (1, 2), (2, 1), (1, 3), (3, 1)]
WORDS2 = ["00", "01", "10", "11"]
WORDS3 = ["000", "001", "010", "011", "100", "101", "110", "111"]
STATE_CAP = 3_000_000
POWER_ITERS = 120


def kmp_next(word: str):
    """Deterministic factor-avoidance automaton for `word` (read as emitted).
    States 0..len-1 live, len = dead.  Returns table[state][bit] -> state."""
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
            table[s][z] = t + 1 if word[t] == zc else 0  # ell means dead
    return table


class Channel:
    """(a, b, word): state = carry * n_ac + ac; input (x,y) -> next or -1."""

    def __init__(self, a: int, b: int, word: str):
        self.a, self.b, self.word = a, b, word
        rev = word[::-1]  # we read deep-to-shallow; z emitted reversed
        ac_table = kmp_next(rev)
        n_ac, n_carry = len(rev), a + b + 1
        self.n_states = n_ac * n_carry
        nxt = np.full((self.n_states, 4), -1, dtype=np.int64)
        for c in range(n_carry):
            for ac in range(n_ac):
                s = c * n_ac + ac
                for sym in range(4):
                    x, y = sym & 1, sym >> 1
                    v = a * x + b * y + c
                    z, c2 = v & 1, v >> 1
                    if c2 >= n_carry:
                        continue  # unreachable carry growth
                    ac2 = ac_table[ac][z]
                    if ac2 == n_ac:
                        continue  # word completed: dead
                    nxt[s, sym] = c2 * n_ac + ac2
        self.nxt = nxt


def build_nxts(channels: list[Channel]) -> tuple[int, list[np.ndarray]]:
    sizes = [ch.n_states for ch in channels]
    S = int(np.prod(sizes)) if channels else 1
    idx = np.arange(S, dtype=np.int64)
    digits = []
    rem = idx
    for ch in channels:
        digits.append(rem % ch.n_states)
        rem = rem // ch.n_states
    nxts = []
    for sym in range(4):
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


def joint_entropy(channels: list[Channel]) -> float:
    sizes = [ch.n_states for ch in channels]
    S = int(np.prod(sizes)) if channels else 1
    if S > STATE_CAP:
        return float("nan")
    S, nxts = build_nxts(channels)
    # power iteration on path counts
    v = np.ones(S, dtype=np.float64)
    growth = []
    for it in range(POWER_ITERS):
        w = np.zeros(S, dtype=np.float64)
        for nx in nxts:
            live = nx >= 0
            np.add.at(w, nx[live], v[live])
        total = w.sum()
        if total == 0:
            return float("-inf")  # empty system
        growth.append(total / v.sum() if v.sum() else 0)
        v = w / total * S  # renormalize
    lam = float(np.median(growth[-20:]))
    return log2(lam) if lam > 0 else float("-inf")


def main() -> None:
    # --- self-tests -------------------------------------------------------
    h0 = joint_entropy([])
    assert abs(h0 - 2.0) < 1e-9, h0
    h1 = joint_entropy([Channel(1, 0, "11")])
    assert abs(h1 - (1 + log2((1 + 5 ** 0.5) / 2))) < 1e-3, h1
    h2 = joint_entropy([Channel(1, 0, "11"), Channel(0, 1, "11")])
    assert abs(h2 - 2 * log2((1 + 5 ** 0.5) / 2)) < 1e-3, h2
    print("self-tests OK: h(full)=2, golden-mean channel, independence\n")

    # --- lesson: unrestricted words collapse VACUOUSLY ----------------------
    # Words 0, 1, 01, 10 are known to recur in every irrational
    # (Adamczewski-Rampersad), so a channel carrying one of them makes the
    # at-least-one conclusion trivially true.  The unrestricted greedy finds
    # exactly that cheat (avoid-01 kills a track to 1^a 0^inf):
    h_cheat = joint_entropy([Channel(1, 0, "01"), Channel(0, 1, "01"),
                             Channel(1, 1, "10")])
    print(f"unrestricted-word cheat family h = {h_cheat:.4f} (vacuous collapse;"
          " rediscovers the known-recurring-words boundary)\n")

    # --- greedy hunt over OPEN words only ------------------------------------
    # Open = occurrence not known for any specific natural irrational:
    # 00, 11, and all eight length-3 words.
    open_words = ["00", "11"] + WORDS3
    print("greedy hunt (OPEN words only): channels in coefficient order,")
    print("word chosen to minimize h")
    print(f"{'k':>2} {'channel':>8} {'constant':>6} {'word':>5} {'h(S_F)':>8} "
          f"{'states':>9}")
    chosen: list[Channel] = []
    for (a, b) in CHANNELS:
        best = None
        for w in open_words:
            trial = chosen + [Channel(a, b, w)]
            h = joint_entropy(trial)
            if np.isnan(h):
                continue
            if best is None or h < best[0]:
                best = (h, w, trial)
        if best is None:
            print(f"   ({a},{b}): state cap hit, stopping")
            break
        h, w, chosen = best
        S = int(np.prod([c.n_states for c in chosen]))
        const = f"2^{a}3^{b}"
        print(f"{len(chosen):>2} {f'({a},{b})':>8} {const:>6} {w:>5} {h:>8.4f} "
              f"{S:>9}")
        if h <= 1e-3:
            print("\n*** COLLAPSE: zero entropy reached - W2 satisfied by this "
                  "family (verify exactly!) ***")
            break

    if chosen and joint_entropy(chosen) > 1e-3:
        print("\nno collapse in this family; the decay curve above is the")
        print("finding: the entropy floor measures how much simultaneous")
        print("digit pathology the log-lattice can support (W3 currency).")
        print("done.")
        return

    # --- EXACT zero-entropy verification (no floats) --------------------------
    # h = 0 for a sofic system iff, after pruning states with no outgoing
    # edge, every strongly connected component of the live graph is a simple
    # cycle (each vertex exactly one intra-SCC out-edge).  Then every
    # infinite consistent stream tail is periodic, and the aperiodic
    # (ln 2, ln 3) pair stream (irrationality of ln 2, ln 3) must violate
    # some channel's avoidance infinitely often.
    from scipy.sparse import csr_matrix
    from scipy.sparse.csgraph import connected_components

    S, nxts = build_nxts(chosen)
    alive = np.ones(S, dtype=bool)
    while True:
        out_deg = np.zeros(S, dtype=np.int64)
        for nx in nxts:
            ok = (nx >= 0)
            ok &= alive
            ok[ok] &= alive[nx[ok]]
            out_deg += ok
        new_alive = alive & (out_deg > 0)
        if new_alive.sum() == alive.sum():
            break
        alive = new_alive
    live_idx = np.flatnonzero(alive)
    print(f"\nexact check: {len(live_idx)} live states after pruning")
    rows, cols = [], []
    for nx in nxts:
        ok = (nx >= 0) & alive
        ok[ok] &= alive[nx[ok]]
        src = np.flatnonzero(ok)
        rows.append(src)
        cols.append(nx[src])
    rows, cols = np.concatenate(rows), np.concatenate(cols)
    g = csr_matrix((np.ones(len(rows), dtype=np.int8), (rows, cols)), shape=(S, S))
    n_comp, labels = connected_components(g, directed=True, connection="strong")
    same = labels[rows] == labels[cols]
    intra_out = np.bincount(rows[same], minlength=S)
    comp_size = np.bincount(labels[alive], minlength=n_comp)
    bad = 0
    cycles = 0
    periods = []
    for comp in np.flatnonzero(comp_size > 0):
        members = np.flatnonzero((labels == comp) & alive)
        intra = intra_out[members]
        if len(members) == 1 and intra[0] == 0:
            continue  # transient vertex, no cycle through it
        if (intra == 1).all():
            cycles += 1
            periods.append(len(members))
        else:
            bad += 1
    if bad == 0:
        print("EXACT: h = 0 confirmed - every SCC is a simple cycle")
        print(f"surviving cycles: {cycles}, periods: {sorted(set(periods))}")
        print("\n*** CANDIDATE THEOREM (pending independent reimplementation +")
        print("    proof write-up + novelty sweep): at least one of the six")
        print("    channel words occurs infinitely often in its constant. ***")
    else:
        print(f"EXACT CHECK FAILED: {bad} SCCs are not simple cycles -")
        print("the float h=0 was numerical; the family does NOT collapse.")

    # --- drop-one minimality ---------------------------------------------------
    print("\ndrop-one minimality (h of each 5-channel subfamily):")
    for i in range(len(chosen)):
        sub = chosen[:i] + chosen[i + 1:]
        h = joint_entropy(sub)
        ch = chosen[i]
        print(f"  without ({ch.a},{ch.b})/'{ch.word}': h = {h:.4f}")
    print("done.")


if __name__ == "__main__":
    sys.exit(main())
