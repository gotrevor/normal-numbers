#!/usr/bin/env python3
"""Emit a complete `HittingSet*.lean` upper-half file from a multiplier set.

Input: base `g`, word length `ell`, multipliers `ms`.  Output: the Lean module
proving `Literature.IsHittingSet g ell {ms}` on the carry-consistency reduction
(`HittingSetReduced.lean`), in the shape of `HittingSetBase2Len4.lean`:

  * `N = lcm {a·g^j : a ∈ ms, j ≤ ell-1}` and the state list `L`, the image of
    `stateOfKW g N ell ms` over `k < N` (the reachable curve);
  * reachability by RUN COMPRESSION — `stateOfKW` reads `k` only through the
    quotients `(b·k)/N`, `b ∈ coeffsOf g ms ell`, which are monotone, so the
    sweep over `k < N` collapses to one kernel check per run;
  * one `checkCertA` certificate per word, emitted with the same
    live/omega/rho/forced construction as `adder_reduced_emit_ell.py` and
    verified here (C1/C1'/C3') before anything is written.

Usage: emit_hitting_lean.py NAME G ELL M1,M2,... [THEOREM] > src/NormalNumbers/File.lean
"""
import sys
from math import gcd
from itertools import product


def lcm_all(xs):
    L = 1
    for x in xs:
        L = L * x // gcd(L, x)
    return L


def build(g, ell, ms):
    coeffs = [a * g ** j for a in ms for j in range(ell)]
    N = lcm_all(coeffs)
    W = g ** (ell - 1)

    def digitK(a, j, k):
        return (a * g ** (j + 1) * k) // N - g * ((a * g ** j * k) // N)

    def chanCodeK(a, k):
        return ((a * k) // N) * W + sum(digitK(a, j, k) * g ** j for j in range(ell - 1))

    def stateOfKW(k):
        s = 0
        for a in reversed(ms):
            s = chanCodeK(a, k) + (a * W) * s
        return s

    # run endpoints: every k at which some quotient (b*k)/N moves
    ends = {N}
    for b in set(coeffs):
        for q in range(1, b):
            ends.add(-((-q * N) // b))          # ceil(q*N/b)
    runs = sorted(e for e in ends if 0 < e <= N)
    # the state is constant on each run, so sample the run starts
    starts = [0] + runs[:-1]
    L = sorted({stateOfKW(k) for k in starts})
    idx = {s: i for i, s in enumerate(L)}
    # sanity: the run decomposition really is a decomposition
    for lo, hi in zip(starts, runs):
        assert all((b * lo) // N == (b * (hi - 1)) // N for b in coeffs), (lo, hi)
    return N, coeffs, runs, starts, L, idx, W


def cert(g, ell, ms, L, idx, W, word):
    """live/rho/omega/forced for one word, exactly as adder_reduced_emit_ell.py."""
    strides, acc = [], 1
    sizes = [a * W for a in ms]
    for n in sizes:
        strides.append(acc); acc *= n
    wordval = 0
    for d in reversed(word):
        wordval = d + g * wordval
    M = len(L)

    def pred(x, j):
        sp = L[j]; s = 0
        for a, n, st in zip(ms, sizes, strides):
            code = (sp // st) % n
            cprime = code // W
            wprime = code % W
            v = a * x + cprime
            z = v % g
            c = v // g
            full = z + g * wprime
            if full == wordval:
                return -1
            s += (c * W + full % W) * st
        return idx.get(s, -2)

    P = [[pred(x, j) for j in range(M)] for x in range(g)]
    assert all(v != -2 for row in P for v in row), "state list not closed under gfamPred"
    edges = [(P[x][j], j, x) for x in range(g) for j in range(M) if P[x][j] >= 0]
    alive = [True] * M; omega = [0] * M; rnd = 0
    while True:
        out = [0] * M
        for (s, sp, _) in edges:
            if alive[s] and alive[sp]: out[s] += 1
        dying = [s for s in range(M) if alive[s] and out[s] == 0]
        if not dying: break
        for s in dying: omega[s] = rnd; alive[s] = False
        rnd += 1
    if not any(alive):
        raise SystemExit(f"word {word}: EMPTY live set")
    ledges = [(s, sp, x) for (s, sp, x) in edges if alive[s] and alive[sp]]
    adj = {}
    for (s, sp, _) in ledges: adj.setdefault(s, []).append(sp)
    import importlib.util
    from pathlib import Path
    spec = importlib.util.spec_from_file_location("emit", Path(__file__).parent / "adder_baseg_emit.py")
    em = importlib.util.module_from_spec(spec); spec.loader.exec_module(em)
    _, lab = em.tarjan_scc(M, adj)
    intra = [0] * M
    for (s, sp, _) in ledges:
        if lab[s] == lab[sp]: intra[s] += 1
    mem = {}
    for s in range(M):
        if alive[s]: mem.setdefault(lab[s], []).append(s)
    selfl = {s for (s, sp, _) in ledges if s == sp}
    for c, Ms in mem.items():
        if (len(Ms) > 1 or Ms[0] in selfl) and not all(intra[s] == 1 for s in Ms):
            raise SystemExit(f"word {word}: SCC of size {len(Ms)} is not a simple cycle - NON-COLLAPSE")
    fsig = [-1] * M; fdst = [-1] * M
    for (s, sp, x) in ledges:
        if lab[s] == lab[sp] and intra[s] == 1:
            assert fsig[s] < 0, (word, s)
            fsig[s] = x; fdst[s] = sp
    cedges = {}
    for (s, sp, _) in ledges:
        if lab[s] != lab[sp]: cedges.setdefault(lab[s], set()).add(lab[sp])
    memo = {}
    def height(u0):
        stack = [(u0, False)]
        while stack:
            u, done = stack.pop()
            if done:
                memo[u] = max((memo[v] + 1 for v in cedges.get(u, ())), default=0); continue
            if u in memo: continue
            stack.append((u, True))
            for v in cedges.get(u, ()):
                if v not in memo: stack.append((v, False))
        return memo[u0]
    rho = [height(lab[s]) if alive[s] else 0 for s in range(M)]
    fail = 0
    for x in range(g):
        for sp in range(M):
            s = P[x][sp]
            if s < 0: continue
            if alive[s]:
                if alive[sp] and not (rho[sp] < rho[s] or (fsig[s] == x and fdst[s] == sp and rho[sp] == rho[s])):
                    fail += 1
            else:
                if alive[sp] or omega[sp] >= omega[s]: fail += 1
    for s in range(M):
        if fsig[s] >= 0 and (P[fsig[s]][fdst[s]] != s or not alive[fdst[s]] or not alive[s]):
            fail += 1
    if fail:
        raise SystemExit(f"word {word}: {fail} certificate condition failures - REFUSING")
    return alive, rho, omega, fsig, fdst


def lst(xs):
    return "[" + ", ".join(map(str, xs)) + "]"


def main(name, g, ell, ms, thm=None):
    thm = thm or (name + "_hitting")
    N, coeffs, runs, starts, L, idx, W = build(g, ell, ms)
    M = len(L)
    ambient = 1
    for a in ms: ambient *= a * W
    sys.stderr.write(f"[{name}] g={g} ell={ell} ms={ms}\n"
                     f"[{name}] ambient {ambient}, N {N}, reduced states {M}, runs {len(runs)}\n")
    p = name
    words = [list(w) for w in product(range(g), reversed=False) ] if False else [list(w) for w in product(range(g), repeat=ell)]
    certs = {}
    for w in words:
        certs[tuple(w)] = cert(g, ell, ms, L, idx, W, w)
        sys.stderr.write(f"[{name}] word {''.join(map(str,w))}: "
                         f"{sum(certs[tuple(w)][0])} live of {M}\n")
    out = []
    A = out.append
    A(f"""/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.HittingSetReduced
import NormalNumbers.Literature

/-!
# `S({g},{ell}) ≤ {len(ms)}`: {len(ms)} multipliers hit every base-{g} word of length {ell} 🧵

Emitted by `experiments/emit_hitting_lean.py` from the multiplier set
`{{{', '.join(map(str, ms))}}}` (`experiments/hitting_set_search_reduced.py`).

The ambient state space of this `gfamPred` family is `∏ᵢ mᵢ·{g}^{ell-1} = {ambient}`.
The carry-consistency reduction (`HittingSetReduced.lean`) cuts it to **{M} states**:
all channels read the same `X`, so with `t = fract(X·{g}ᵐ)` the joint state is
`stateOfKW {g} N {ell} ms ⌊N·t⌋` for `N = lcm {{a·{g}^j}} = {N}`.

Reachability is kernel `decide +kernel` by **run compression**: `stateOfKW` reads
`k` only through the monotone quotients `(b·k)/N`, so the sweep over `k < {N}`
is one check per run — **{len(runs)} runs**.  No `native_decide` anywhere.

* `{thm}` : `S({g},{ell}) ≤ {len(ms)}` via `{{{', '.join(map(str, ms))}}}`.

Nothing here claims the matching lower bound.
-/

set_option maxRecDepth 100000

namespace NormalNumbers.Adder

open NormalNumbers

/-- The {len(ms)} multipliers. -/
def {p}ms : List ℕ := {lst(ms)}

/-- `lcm {{a·{g}^j : a ∈ ms, j ≤ {ell-1}}}`: the index range of the reachable curve. -/
def {p}N : ℕ := {N}

/-- The {M} reachable joint states, sorted. -/
def {p}L : Array ℕ := #{lst(L)}

def {p}Lget (j : ℕ) : ℕ := {p}L.getD j 0

def {p}idx (s : ℕ) : ℕ := (bfind {p}L s).getD 0

def {p}step (w : List ℕ) : ℕ → ℕ → Option ℕ :=
  fun σ j => (gfamPred {g} (chansOfW {p}ms w) (σ % {g}) (σ / {g}) ({p}Lget j)).map {p}idx

/-- The reachability check at one index. -/
def {p}ok (k : ℕ) : Bool :=
  decide ({p}Lget ({p}idx (stateOfKW {g} {p}N {ell} {p}ms k)) = stateOfKW {g} {p}N {ell} {p}ms k)
    && decide ({p}idx (stateOfKW {g} {p}N {ell} {p}ms k) < {M})

/-- The run endpoints: {len(runs)} runs tile `[0, {N})`. -/
def {p}runs : List ℕ := {lst(runs)}

/-- The per-run check: the quotients are constant across the run, and the run's
first index is reachable. -/
def {p}P (lo hi : ℕ) : Bool :=
  (coeffsOf {g} {p}ms {ell}).all (fun b => decide ((b * lo) / {p}N = (b * (hi - 1)) / {p}N))
    && {p}ok lo

theorem {p}_runs_ok : runsCover {p}P 0 {p}runs {p}N = true := by decide +kernel

/-- **Reachability**, by run compression: {len(runs)} kernel checks instead of {N}. -/
theorem {p}_section (k : ℕ) (hk : k < {p}N) :
    {p}Lget ({p}idx (stateOfKW {g} {p}N {ell} {p}ms k)) = stateOfKW {g} {p}N {ell} {p}ms k
      ∧ {p}idx (stateOfKW {g} {p}N {ell} {p}ms k) < {M} := by
  refine runsCover_spec (P := {p}P) (Q := fun k =>
    {p}Lget ({p}idx (stateOfKW {g} {p}N {ell} {p}ms k)) = stateOfKW {g} {p}N {ell} {p}ms k
      ∧ {p}idx (stateOfKW {g} {p}N {ell} {p}ms k) < {M}) ?_ {p}runs 0 {p}N {p}_runs_ok k (by omega) hk
  intro lo hi hP j hj1 hj2
  simp only [{p}P, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hP
  have hconst : stateOfKW {g} {p}N {ell} {p}ms j = stateOfKW {g} {p}N {ell} {p}ms lo := by
    refine stateOfKW_congr {g} {p}N {ell} (by omega) {p}ms j lo ?_
    intro b hb
    exact quot_const_of_run b {p}N lo hi j hj1 hj2 (hP.1 b hb)
  have h := hP.2
  simp only [{p}ok, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [hconst]
  exact h
""")
    for w in words:
        tag = "".join(map(str, w))
        alive, rho, omega, fsig, fdst = certs[tuple(w)]
        A(f"""
/-- Certificate for the word `{lst(w)}`: {sum(alive)} live states of the {M}. -/
def {p}w{tag}live : ℕ → Bool := fun j => {lst([j for j in range(M) if alive[j]])}.contains j

def {p}w{tag}rho : ℕ → ℕ := fun j => (({lst([f"({j}, {rho[j]})" for j in range(M) if rho[j]])} : List (ℕ × ℕ)).lookup j).getD 0

def {p}w{tag}omega : ℕ → ℕ := fun j => (({lst([f"({j}, {omega[j]})" for j in range(M) if omega[j]])} : List (ℕ × ℕ)).lookup j).getD 0

def {p}w{tag}forced : ℕ → Option (ℕ × ℕ) :=
  fun j => ({lst([f"({j}, ({fsig[j]}, {fdst[j]}))" for j in range(M) if fsig[j] >= 0])} : List (ℕ × ℕ × ℕ)).lookup j

theorem {p}w{tag}_cert : checkCertA ({p}step {lst(w)}) {g} {M}
    {p}w{tag}live {p}w{tag}rho {p}w{tag}omega {p}w{tag}forced = true := by decide +kernel
""")
    A(f"""
/-- The section hypothesis of `signed_engine_g_single_reduced`, from `{p}_section`. -/
theorem {p}_sec (X : ℝ) (w : List ℕ) (hw : w.length = {ell}) (m : ℕ) :
    {p}Lget ({p}idx (gfamState {g} (chansOfW {p}ms w) X 0 m))
        = gfamState {g} (chansOfW {p}ms w) X 0 m
      ∧ {p}idx (gfamState {g} (chansOfW {p}ms w) X 0 m) < {M} := by
  have hms : ∀ a ∈ {p}ms, 1 ≤ a := by decide
  have hdvd : ∀ a ∈ {p}ms, ∀ j, j ≤ {ell} - 1 → a * {g} ^ j ∣ {p}N := by decide
  have ht1 : Int.fract (X * (({g} : ℕ) : ℝ) ^ m) < 1 := Int.fract_lt_one _
  rw [gfamState_window {g} (by norm_num) {p}ms hms w {ell} hw {p}N (by norm_num [{p}N]) hdvd X m]
  refine {p}_section _ ?_
  have hN0 : (0 : ℝ) < ({p}N : ℝ) := by norm_num [{p}N]
  have hfl : ⌊({p}N : ℝ) * Int.fract (X * (({g} : ℕ) : ℝ) ^ m)⌋ < ({p}N : ℤ) := by
    apply Int.floor_lt.2
    push_cast
    calc ({p}N : ℝ) * Int.fract (X * (({g} : ℕ) : ℝ) ^ m) < ({p}N : ℝ) * 1 :=
          mul_lt_mul_of_pos_left ht1 hN0
      _ = ({p}N : ℝ) := by ring
  have hpos' : 0 < {p}N := by norm_num [{p}N]
  omega

/-- **`S({g},{ell}) ≤ {len(ms)}`.** -/
theorem {thm} : Literature.IsHittingSet {g} {ell} {{{', '.join(map(str, ms))}}} := by
  intro α hα w hw hd
  have hpos : ∀ v : List ℕ, ∀ ch ∈ chansOfW {p}ms v, 1 ≤ ch.posSum := by
    intro v ch hch
    simp only [chansOfW, {p}ms, List.mem_map] at hch
    obtain ⟨a, ha, rfl⟩ := hch
    simp only [ZChannel.posSum]
    fin_cases ha <;> decide
  have hell : ∀ v : List ℕ, v.length = {ell} → ∀ ch ∈ chansOfW {p}ms v, 1 ≤ ch.ell := by
    intro v hv ch hch
    simp only [chansOfW, List.mem_map] at hch
    obtain ⟨a, _, rfl⟩ := hch
    simp [ZChannel.ell, hv]
  have hword : ∀ v : List ℕ, (∀ c ∈ v, c < {g}) → ∀ ch ∈ chansOfW {p}ms v, ∀ c ∈ ch.word, c < {g} := by
    intro v hv ch hch c hc
    simp only [chansOfW, List.mem_map] at hch
    obtain ⟨a, _, rfl⟩ := hch
    exact hv c hc""")
    assert ell == 1, "only ell = 1 is emitted for the final assembly so far"
    A(f"""  obtain ⟨d, rfl⟩ : ∃ d, w = [d] := by
    rcases w with _ | ⟨d, _ | ⟨e, t⟩⟩ <;> simp at hw
    exact ⟨d, rfl⟩
  have hd' : d < {g} := hd d (by simp)
  have key : ∃ ch ∈ chansOfW {p}ms [d],
      ∀ N, ∃ n, N ≤ n ∧ OccursAt {g} (ch.a * α) ch.word n := by
    interval_cases d""")
    for w in words:
        tag = "".join(map(str, w))
        A(f"""    · exact signed_engine_g_single_reduced {g} (by norm_num) (chansOfW {p}ms {lst(w)})
        {p}Lget {p}idx {p}w{tag}_cert α hα (hpos _) (hell _ rfl) (hword _ (by decide))
        (fun m => ({p}_sec α {lst(w)} rfl m).2)
        (fun m => ({p}_sec α {lst(w)} rfl m).1)""")
    A(f"""  obtain ⟨ch, hch, hio⟩ := key
  simp only [chansOfW, {p}ms, List.map_cons, List.map_nil] at hch
  fin_cases hch""")
    for a in ms:
        A(f"  · exact ⟨{a}, by simp, by norm_num, by simpa using hio⟩")
    A("\nend NormalNumbers.Adder")
    print("\n".join(out))


if __name__ == "__main__":
    name, g, ell, msv = sys.argv[1:5]
    thm = sys.argv[5] if len(sys.argv) > 5 else None
    main(name, int(g), int(ell), [int(x) for x in msv.split(",")], thm)
