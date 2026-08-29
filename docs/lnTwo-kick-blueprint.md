# The kick blueprint: digit runs of ln 2 from the surrogate dynamics 🦵

Option-4 dig, 2026-08-29 (charter: weaken the ln-two orbit hypothesis / find what is
*unconditionally provable* about `lnTwoOrbit`).  Lean surface: `src/NormalNumbers/LnTwoRuns.lean`
(all stated theorems sorry-free, standard axiom triple, verified 2026-08-29).  Probe:
`experiments/lntwo_runs.py`.

## 1. The mechanism

The Bailey–Crandall surrogate `x_{n+1} = fract(2·x_n + 1/(n+1))` carries two pieces of structure
the raw doubling orbit of `ln 2` does not have:

- **the kick** `1/(n+1)`, injected every step;
- **the tail bracket** `τ_n := 2^n·(ln 2 − Σ_{k<n} 1/(k·2^k)) ∈ [1/(2(n+1)), 1/(n+1)]`
  (`lnTwoTail_ge` + `lnTwoTail_le`), with the exact relation
  `orbit(ln 2)_n = fract(x_n + τ_n)` (`orbit_log_two_eq`).

A run of `k` zeros (ones) in binary `ln 2` at position `n` is exactly
`orbit_n ∈ [0, 2^{-k})` (`[1 − 2^{-k}, 1)`) — the run dictionary
(`occursAt_replicate_zero_iff` / `_one_iff`).

**The τ-floor kills the bottom channel.**  If `x_n + τ_n < 1` (no wraparound), then
`orbit_n = x_n + τ_n ≥ τ_n ≥ 1/(2(n+1))`: a 0-run at position `n` cannot exceed
`log₂ n + 1` bits *unless* the surrogate sits in the **top sliver** `x_n ≥ 1 − 1/(n+1)`.
The 1-run case is symmetric (a wraparound would leave the orbit at `≤ τ_n`, too small).
This is the **sliver dichotomy**, proved sorry-free:

> `lnTwoOrbit_top_sliver_of_zeroRun` / `_of_oneRun`: any run with `2^k > 2(n+1)` forces
> `x_n ≥ 1 − 2/(n+1)`.

So the *entire* long-run question for `ln 2` lives in an interval of width `~2/n` around `1`,
at the single position where the run starts.

**Near 1 the kick is neutral-unstable.**  Writing `δ_n = 1 − x_n`, the in-sliver dynamics is
`δ_{n+1} = 2δ_n − 1/(n+1)`: the profile `δ_n = 1/n` is an (unstable) fixed profile, deviations
double each step.  Riding the sliver to depth `2^{-k}` requires hitting a window of width
`~2^{-k}/n` around the unstable profile — the random-like model predicts longest rides
`~log₂ n`, which is exactly what the data shows.

## 2. Probe data (200 000 bits, exact arithmetic)

- Record 0-runs: `(93, 9), (1254, 10), (4855, 13), (39172, 16)`; record 1-runs:
  `(1002, 8), (2572, 10), (3984, 12), (10357, 13), (26249, 15)`.  Every record has
  `len / log₂(pos) ≈ 1.0` (range 0.8–1.4) — **random-like run behavior**.
- Surrogate top-sliver visits (`1 − x_n < 4/n`): 29 in 4000 steps, and they coincide with the
  record-run positions (93, 1002, 1254, 2572, 3984 all appear) — the dichotomy is visibly the
  mechanism, not an artifact.
- Near-zero surrogate values (`x_n < 1/(2n)`): essentially never (n = 1, 5 only) — the kick
  floor works.

## 3. The tower

| Tier | Statement | Status | Digit conclusion |
|---|---|---|---|
| 0 | run dictionary + sliver dichotomy + `dyadicSep_run_bound` wiring | ✅ **proved, sorry-free** | super-log runs ⇔ top-sliver events |
| 1 | `LnTwoExpSep β`: `‖2ⁿ·ln 2‖ ≥ 2^{−βn}` | 🟡 frozen Prop; citable (Marcovecchio 2009, μ ≤ 3.5746 ⇒ β ≈ 2.58); in-house route = shifted-Legendre (Alladi–Robinson β ≈ 3.63, machinery partially built in collatz-moonshot `FrontA/Legendre.lean`) | runs at `n` bounded by `βn` (`run_le_of_expSep`) |
| 2 | `LnTwoPolySep C`: `‖2ⁿ·ln 2‖ ≥ (n+2)^{−C}` | 🔴 frozen Prop; **Mahler-class open** (family of `‖(3/2)ⁿ‖`); empirically true at `C ≈ 1` | runs at `n` bounded by `C·log₂ n` (`run_le_of_polySep`) |

Novelty status — **swept 2026-08-29, see `docs/lit-sweep-2026-08-29.md`** (supersedes the first
web probe's owed list).  Headlines: Tier 1's `(μ−1)n` corollary is in print (Rivoal 2008), so
Tier 1 is confirmed classical; the nearest prior art for the lattice route is Rivoal 2007
(lcm-class restricted measures, run constants 3.6–3.8n for ln 2 — weaker than 2.57n); the
surrogate-numerator pigeonhole + per-n coincidence exclusion is NOT FOUND and its window sits at
a scale (q⁻¹) measure methods structurally cannot reach; the kick-floor-as-resource and
run-forcing sliver direction are NOT FOUND / PARTIAL (Bailey–Borwein 2012 Stoneham nonnormality
is the converse-direction precedent).  Lagarias 2001's acid: a kick-magnitude floor alone can
never yield u.d.-or-finite — conclusions must stay at the forcing level, as ours do.

## 4. Why this is the alien path

- **One problem, not two**: Tier 1/2 are effective linear-form separations for `(2, ln 2)` —
  the same object family as collatz-moonshot's `sep_two_three` (`‖m·log₂3‖` separations).  The
  moonshot's single-kernel Legendre package (which caps at `log 2` — exactly our constant!) is
  the natural donor for an in-house Tier 1 proof.  The two repos meet at one Diophantine wall.
- **Ensemble-blind, pointwise-visible**: the sliver dichotomy is a *pointwise* mechanism —
  the kick structure is invisible to the measure-level instruments (Wall, equidistribution)
  and is precisely the kind of per-point coupling object the transmission-2 synthesis said to
  hunt (its Galois move).
- It answers the option-4 crux question "what is the weakest hypothesis we could hope to prove
  unconditionally?": Tier 1 is the honest reachable target; Tier 2 is the true shape of the
  problem; below Tier 1, the τ-floor half of every run bound is **already unconditional**.

## 5. Next moves

*(Rewritten 2026-08-29 after the lit sweep + the D8 lattice dig; the original list is in git.)*

1. ~~Literature sweep~~ ✅ done → `docs/lit-sweep-2026-08-29.md`.
2. ~~Lattice reformulation (alien R1)~~ ✅ done and **costume-refuted the same day** →
   `LnTwoLattice.lean`: the coincidence-failure node ⟺ dyadic separation re-coordinatized
   (`latticeAvoid_of_dyadicSep` / `dyadicSep_of_latticeAvoid`).  ⚠️ Item 3's old phrasing
   "a genuine weakening-lattice rung not passing through Diophantine input" is hereby
   retracted for the run-window family — the window position depends on `ln 2` and the
   avoidance collapses onto `‖2ⁿ·ln 2‖` exactly.
3. **R2 — the kicked-orbit dichotomy, abstract + π** (now top of the board for novel math):
   extract the τ-floor/sliver dichotomy as an abstract lemma (orbit `x_{n+1} = b·x_n + kick_n
   mod 1`, kick floor `≥ c/n`, tail bracket), re-derive the ln-2 case as its instance, then
   instantiate π's base-16 BBP orbit.  Sweep verdict: kick-floor-as-resource NOT FOUND;
   Bailey–Borwein 2012 (Stoneham nonnormality) is the converse-direction precedent to cite.
   🚨 Lagarias guardrail (sweep doc): a magnitude-only kick floor can never conclude
   u.d.-or-finite — keep every conclusion at the forcing level (run ⟹ ride).
4. **R3 — the congruence attack surface**: window avoidance for structured `n` via the exact
   numerator `lnTwoNum` — start at `n = p−1` where `A_{p−1} ≡ unit·q_p(2) (mod p)`
   (Glaisher / Z.-H. Sun, formulas in the sweep doc).  Low odds, real magnitude; hold as a
   node, not a campaign.
5. **Tier-1 discharge** (lane 2, when scheduled): shifted-Legendre package → `LnTwoExpSep`
   → the unconditional `βn` run bound.  Classical (Rivoal 2008 has the `(μ−1)n` corollary);
   value is formalization-first plus lighting the tower end-to-end.
6. The other option-4 flavors (mixing/discrepancy hypotheses) remain open as conditional
   rungs beside `LnTwoHypothesisFreq`.
