#!/usr/bin/env -S uv run --quiet --with numpy --with scipy python3
"""Certificate emitter for the adder six-fold disjunction (BRIEF-adder-disjunction).

Rebuilds the family automaton on the LEAN conventions exactly (window encoding,
tight carries [0, a+b-1], mixed-radix per-channel codes) — deliberately NOT the
probe's KMP encoding, so this is an independent reimplementation of the collapse.

Conventions (frozen here, mirrored bit-for-bit in AdderAutomaton.lean):
  * Channel i has (a, b, word); word is a list of bits, word[0] shallowest
    (matches OccursAt: word[j] at digit position n+j, digitOf index n+j,
    real-floor index m = n+j+1).
  * carry c in [0, C-1], C = max(a+b, 1).
  * window = the ell-1 DEEPER z-digits (d_{m+1},...,d_{m+ell-1}) at floor
    index m; encoded LSB-first: bit j = d_{m+1+j}.  ell = len(word).
  * channel code s_i = c * 2^(ell-1) + w;  channel size n_i = C * 2^(ell-1).
  * global state = sum_i s_i * prod_{j<i} n_j   (channel 0 least significant).
  * input sigma in {0,1,2,3}: x = sigma & 1, y = sigma >> 1.
  * HStep s sigma s'  ("s' is one step DEEPER"):  s = pred(sigma, s') where
    pred computes per channel  v = a*x + b*y + c'(s'),  z = v & 1, c = v >> 1,
    window(s) = (z :: window(s')) truncated to ell-1 bits, and the step is
    ILLEGAL (None) iff for some channel the ell-bit window z :: window(s')
    equals the channel word ("the word occurred at position m").

Certificate tables over the ambient space (all conditions local, decidable):
  live  : bool     (the set L)
  rho   : nat      (rank: condensation height of the live graph)
  forced: Option (sigma, s')  per state (unique intra-SCC edge on cycle states)
  omega : nat      (dead-depth: pruning round)

Conditions re-verified here at emit time (the emitter REFUSES to write a
certificate failing its own conditions):
  (C1)  s in L, HStep s sigma s', s' in L  =>  rho s' < rho s, or
        (forced s = (sigma, s') and rho s' = rho s).
  (C1') forced s = (sigma, s')  =>  HStep s sigma s' legal and s' in L.
  (C3') s not in L, HStep s sigma s'  =>  s' not in L and omega s' < omega s.

Usage:  adder_certificate_emit.py [toy|main]   (default: both)
Emits:  experiments/certs/adder_cert_<name>.json  (neutral intermediate)
"""

import json
import sys
from pathlib import Path

import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components

FAMILIES = {
    "main": [(1, 0, "00"), (0, 1, "001"), (1, 1, "11"),
             (1, 2, "001"), (2, 1, "010"), (1, 3, "000")],
    "toy": [(1, 0, "01"), (0, 1, "01"), (1, 1, "10")],
    # signed channels (BRIEF-adder-signed-engine objective 3): constants
    # ln2, ln3, ln(3/2), ln(4/3), ln(9/8), ln6 — the musical family.
    "musical": [(1, 0, "00"), (0, 1, "11"), (-1, 1, "100"),
                (2, -1, "11"), (-3, 2, "00"), (1, 1, "010")],
}


def _neg(t):
    return max(-t, 0)


def _pos(t):
    return max(t, 0)


class Family:
    def __init__(self, channels):
        self.channels = channels
        self.ells = [len(w) for _, _, w in channels]
        # signed windows: carry in [-(a-+b-), a++b+-1], Nat-encoded with
        # offset +(a-+b-); for a,b >= 0 this is exactly the old convention.
        self.offs = [_neg(a) + _neg(b) for a, b, _ in channels]
        self.pos_sums = [_pos(a) + _pos(b) for a, b, _ in channels]
        for a, b, _ in channels:
            assert _pos(a) + _pos(b) >= 1, (a, b, "need a positive coefficient")
        self.carry_sizes = [max(p + o, 1) for p, o in zip(self.pos_sums, self.offs)]
        self.win_sizes = [2 ** (e - 1) for e in self.ells]
        self.sizes = [c * w for c, w in zip(self.carry_sizes, self.win_sizes)]
        self.S = int(np.prod(self.sizes))
        self.words = [int(w[::-1], 2) for _, _, w in channels]  # bit j of word = w[j]

    def pred_tables(self):
        """For each sigma: pred[sigma][s'] = s (or -1 illegal).  Vectorized."""
        S = self.S
        idx = np.arange(S, dtype=np.int64)
        # decode per-channel codes of s'
        codes = []
        rem = idx
        for n in self.sizes:
            codes.append(rem % n)
            rem = rem // n
        preds = []
        for sigma in range(4):
            x, y = sigma & 1, sigma >> 1
            s = np.zeros(S, dtype=np.int64)
            illegal = np.zeros(S, dtype=bool)
            mult = 1
            for (a, b, _), ell, wsz, code, word, n, off, csz in zip(
                    self.channels, self.ells, self.win_sizes, codes,
                    self.words, self.sizes, self.offs, self.carry_sizes):
                cprime = code // wsz
                wprime = code % wsz
                # v = a*x + b*y + true deeper carry; Python & 1 / >> 1 are
                # floor-consistent for negatives (match Int.emod/Int.ediv)
                v = a * x + b * y + (cprime - off)
                z = v & 1
                c = (v >> 1) + off   # re-encode with offset
                assert (0 <= c).all() and (c < csz).all(), (a, b, "carry out of range")
                full = z + 2 * wprime          # the ell-bit formed window
                illegal |= (full == word)      # word occurred: no legal step
                wnew = full % wsz              # keep ell-1 shallow bits
                s += (c * wsz + wnew) * mult
                mult *= n
            s[illegal] = -1
            preds.append(s)
        return preds

    def word_check(self):
        """Sanity: word bit encoding round-trips."""
        for (a, b, w), word in zip(self.channels, self.words):
            bits = [(word >> j) & 1 for j in range(len(w))]
            assert bits == [int(ch) for ch in w], (w, word)


def build_certificate(name, channels):
    fam = Family(channels)
    fam.word_check()
    S = fam.S
    preds = fam.pred_tables()
    print(f"[{name}] ambient states: {S}")

    # successors: edges s -> s' where pred[sigma][s'] = s
    # build reverse adjacency arrays: for each sigma, src = pred (s), dst = s'
    sp = np.arange(S, dtype=np.int64)
    edges_src = np.concatenate([preds[g][preds[g] >= 0] for g in range(4)])
    edges_dst = np.concatenate([sp[preds[g] >= 0] for g in range(4)])
    edges_sig = np.concatenate([np.full((preds[g] >= 0).sum(), g, dtype=np.int64)
                                for g in range(4)])

    # --- prune: omega = removal round; live = survivors -----------------------
    alive = np.ones(S, dtype=bool)
    omega = np.zeros(S, dtype=np.int64)
    rnd = 0
    while True:
        out_deg = np.zeros(S, dtype=np.int64)
        ok = alive[edges_src] & alive[edges_dst]
        np.add.at(out_deg, edges_src[ok], 1)
        dying = alive & (out_deg == 0)
        if not dying.any():
            break
        omega[dying] = rnd
        alive[dying] = False
        rnd += 1
    live = alive
    n_live = int(live.sum())
    print(f"[{name}] live states after pruning: {n_live} (rounds: {rnd})")
    if n_live == 0:
        raise SystemExit(f"[{name}] EMPTY live set — no certificate (system dies)")

    # --- SCCs of live graph ----------------------------------------------------
    ok = live[edges_src] & live[edges_dst]
    lsrc, ldst, lsig = edges_src[ok], edges_dst[ok], edges_sig[ok]
    g = csr_matrix((np.ones(len(lsrc), dtype=np.int8), (lsrc, ldst)), shape=(S, S))
    n_comp, labels = connected_components(g, directed=True, connection="strong")

    same = labels[lsrc] == labels[ldst]
    intra_out = np.bincount(lsrc[same], minlength=S)

    # cycle membership: SCC with >=2 members, or singleton with self-loop
    comp_members = {}
    for s in np.flatnonzero(live):
        comp_members.setdefault(labels[s], []).append(s)
    forced_sig = np.full(S, -1, dtype=np.int64)
    forced_dst = np.full(S, -1, dtype=np.int64)
    self_loop = lsrc[same][lsrc[same] == ldst[same]]
    cycles = 0
    periods = set()
    for comp, members in comp_members.items():
        members = np.array(members)
        is_cycle_comp = len(members) > 1 or members[0] in self_loop
        if not is_cycle_comp:
            if intra_out[members[0]] != 0:
                raise SystemExit(f"[{name}] singleton SCC with intra edge but no self-loop?!")
            continue
        # simple cycle check: every member exactly one intra-SCC out-edge
        if not (intra_out[members] == 1).all():
            raise SystemExit(f"[{name}] SCC of size {len(members)} is NOT a simple cycle "
                             f"(intra out-degrees {sorted(set(intra_out[members]))}) — "
                             "certificate design does not apply; REFUSING")
        cycles += 1
        periods.add(len(members))
    # forced: the unique intra-SCC edge per cycle member; check single-labeled
    mask_cycle_edge = same.copy()
    # restrict to edges whose source is in a cycle SCC (intra_out==1 there)
    for i in np.flatnonzero(same):
        s = lsrc[i]
        if intra_out[s] == 1:
            if forced_sig[s] >= 0:
                raise SystemExit(f"[{name}] state {s}: two intra-SCC edges (multi-label) — REFUSING")
            forced_sig[s] = lsig[i]
            forced_dst[s] = ldst[i]
    print(f"[{name}] cycles: {cycles}, periods: {sorted(periods)}")

    # --- rho: condensation height (longest path from each SCC) ---------------
    # comp graph edges (inter-SCC only)
    inter = ~same
    csrc, cdst = labels[lsrc[inter]], labels[ldst[inter]]
    comp_edges = {}
    for u, v in zip(csrc, cdst):
        comp_edges.setdefault(u, set()).add(v)
    height = np.zeros(n_comp, dtype=np.int64)
    # topological order: condensation labels from scipy are already in
    # topological order? Not guaranteed; do memoized DFS.
    import sys as _sys
    _sys.setrecursionlimit(1_000_000)
    memo = {}
    def h(u):
        if u in memo:
            return memo[u]
        memo[u] = 0  # placeholder (DAG: no cycles among comps)
        best = 0
        for v in comp_edges.get(u, ()):
            best = max(best, h(v) + 1)
        memo[u] = best
        return best
    rho = np.zeros(S, dtype=np.int64)
    live_list = np.flatnonzero(live)
    for s in live_list:
        rho[s] = h(labels[s])
    print(f"[{name}] rho range: 0..{rho.max()}, omega range: 0..{omega[~live].max() if (~live).any() else 0}")

    # --- re-verify C1, C1', C3' exactly as the Lean checker will ---------------
    # iterate over (sigma, s'), compute s = pred; table lookups only.
    failures = 0
    for gI in range(4):
        p = preds[gI]
        legal = p >= 0
        s_arr = p[legal]
        sp_arr = sp[legal]
        # C1
        m = live[s_arr] & live[sp_arr]
        s1, sp1 = s_arr[m], sp_arr[m]
        drop = rho[sp1] < rho[s1]
        forc = (forced_sig[s1] == gI) & (forced_dst[s1] == sp1) & (rho[sp1] == rho[s1])
        bad = ~(drop | forc)
        failures += int(bad.sum())
        if bad.any():
            b = np.flatnonzero(bad)[0]
            print(f"[{name}] C1 FAIL e.g. s={s1[b]} sigma={gI} s'={sp1[b]} "
                  f"rho {rho[s1[b]]}->{rho[sp1[b]]} forced=({forced_sig[s1[b]]},{forced_dst[s1[b]]})")
        # C3'
        m = ~live[s_arr]
        s3, sp3 = s_arr[m], sp_arr[m]
        bad3 = live[sp3] | (omega[sp3] >= omega[s3])
        failures += int(bad3.sum())
        if bad3.any():
            b = np.flatnonzero(bad3)[0]
            print(f"[{name}] C3' FAIL e.g. s={s3[b]} sigma={gI} s'={sp3[b]} "
                  f"live'={live[sp3[b]]} omega {omega[s3[b]]}->{omega[sp3[b]]}")
    # C1'
    fs = np.flatnonzero(forced_sig >= 0)
    for s in fs:
        gI, d = int(forced_sig[s]), int(forced_dst[s])
        if preds[gI][d] != s or not live[d] or not live[s]:
            failures += 1
            print(f"[{name}] C1' FAIL s={s} forced=({gI},{d}) pred={preds[gI][d]}")
    if failures:
        raise SystemExit(f"[{name}] {failures} condition failures — REFUSING to emit")
    print(f"[{name}] C1/C1'/C3' verified in Python: OK")

    # --- emit -----------------------------------------------------------------
    out = {
        "name": name,
        "channels": [{"a": a, "b": b, "word": [int(ch) for ch in w]}
                     for a, b, w in channels],
        "sizes": fam.sizes,
        "ambient": S,
        "n_live": n_live,
        "cycles": cycles,
        "periods": sorted(periods),
        "live": live.astype(int).tolist(),
        "rho": rho.tolist(),
        "omega": omega.tolist(),
        "forced_sig": forced_sig.tolist(),
        "forced_dst": forced_dst.tolist(),
    }
    d = Path(__file__).parent / "certs"
    d.mkdir(exist_ok=True)
    path = d / f"adder_cert_{name}.json"
    path.write_text(json.dumps(out))
    print(f"[{name}] emitted {path} ({path.stat().st_size} bytes)")
    return out


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "both"
    names = ["toy", "main"] if which == "both" else [which]
    for n in names:
        build_certificate(n, FAMILIES[n])
    print("done.")


if __name__ == "__main__":
    main()
