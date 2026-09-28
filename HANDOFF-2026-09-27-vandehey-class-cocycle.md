# HANDOFF — Vandehey 2017 Theorem 1.1: the route was wrong, the crux is relocated

**Branch** `wip/vandehey-matrix-action` · **HEAD** `8733144` · `lake build` 🟢 9285 jobs ·
working tree clean · nothing pushed.

**Scoped objective (`LEAN_DONE_WHEN`)**: `sorry`-free
`src/NormalNumbers/LiteratureVandehey.lean`, i.e. prove
`Literature.vandeheyUniformFreq_holds` (no weakening/renaming of the `def` or theorem).

## READ THIS FIRST: the previous handoff's "NEXT 1" is dead

`HANDOFF-2026-09-27-vandehey-matrix-action.md` said the next step was to close
`VandeheyAut.exists_jointFreq_limit` — "pure bookkeeping, every input exists".  **Do not do
this.**  That lemma's `Synchronizing` hypothesis is *unsatisfiable* for the transducer
Theorem 1.1 needs, so proving it would prove something about an empty hypothesis.  The lemma
itself is not false; it is simply inapplicable.  Full write-up:
`PROBE-2026-09-27-transducer-not-synchronizing.md`.

## What this lap established

### 1. The det-±D CF transducer is NOT synchronizing (decided, not guessed)

Over ℤ the state set is finite, so synchronizability is **decidable**.
`probes/cf_transducer_sync.py` builds the transducer (state = primitive integer `M`,
`|det M| = D`, as a Möbius map on `(0,1)`; ingest `M ↦ M·B_a`, emit `M ↦ B_d⁻¹·M`) and decides
it: reachable reduced states 80 / 77 / 78 / 223 for `x↦2x`, `x↦x/2`, `x↦(x+1)/2`, `x↦3x`; **no
synchronizing word up to length 20**; the image of the state set stalls at `D+1` forever;
1953/3160 pairs unmergeable for `D=2`, 16151/24753 for `D=3`.

The obstruction, with a proof: after common input `w` the two states are `P M W` and `Q N W`
with `P, Q, W ∈ GL₂(ℤ)`, so projective equality forces `N = λ(Q⁻¹P)M` with `Q⁻¹P ∈ GL₂(ℤ)`,
i.e. **equality of the row lattice `ℤ²M` up to scaling** — and `W` is invertible, so no input
can ever change it.  `probes/cf_transducer_class.py` confirms mergeable ⟺ same row-lattice
class with **0 mismatches** over 3160 + 14878 pairs.

### 2. The crux, named exactly, and it is the Gauss map mod D

The state is an extension `state = (class ∈ ℙ¹(ℤ/D)) × (fiber, mergeable inside a class)`.
A row lattice of index `D` is `L_b = {(u,v) : v ≡ b u}` or `L_∞ = {(u,v) : u ≡ 0}`; ingesting
a digit right-multiplies by `B_a = [[0,1],[1,a]]`, i.e. `(u,v) ↦ (v, u + a v)`, giving
`L_b ↦ L_{a+b⁻¹}`, `L_0 ↦ L_∞`, `L_∞ ↦ L_a`.  So

> **the class cocycle is the continued-fraction map `s ↦ a + 1/s` read modulo `D`.**

Verified against the transducer on **8488 transitions** over `D = 2,3,5` and four matrices,
zero mismatches (`probes/cf_transducer_class.py`, `check_model`).  Each `B_a` is invertible mod
`D`, so the class acts by bijections and never forgets — this is precisely the content Vandehey
buys from the Airey–Mance-refuted Moshchevitin–Shkredov lemma.  **Not** Wall-shaped: Wall's
base-`b` carry automaton *is* synchronizing, which is why Wall is elementary and this is not.

### 3. New src files, all sorry-free and `[propext, Classical.choice, Quot.sound]`

| file | contents |
|---|---|
| `VandeheyCocycle.lean` | the engine + the corrected transfer principle |
| `VandeheyClass.lean` | the class automaton: Gauss map mod `D`, transitive, aperiodic |
| `VandeheyMixing.lean` | ψ-mixing against a finite / countable **family** of cylinders |
| `VandeheyRenewal.lean` | the class kernel is doubly stochastic |

Key results:

* `cesaro_shift_bound` — `‖∑_{i<n} a i‖ ≤ ∑_{i<n} ‖K⁻¹ • ∑_{k<K} a(i+k)‖ + 2CK`.  How a
  non-synchronizing cocycle is tamed: local `K`-averages cost only an `O(K)` boundary.
* `vanDerCorput_bound` — one Cauchy–Schwarz on top, turning an `L¹` bound on local averages
  (a variance) into decay of correlations in the gap (a first moment).
* `VandeheyAut.stateAt_add` — the plain cocycle identity, the substitute for the *false*
  "state is a function of the window"; `cfWindow_take / _drop / _drop_take`.
* `localAvg_eq`, `windowBound`, `abs_sum_jointDev_le`, `sum_jointDev_eq` — the local average is
  a function of the window **and the finite hidden state**; worst-casing the latter leaves a
  function of the window alone, so `|∑ jointDev| ≤ ∑ windowBound(window) + 2(1+|L|)K`.
* `ClassEquidistribution` — **the crux as one named `Prop`**; and
  `tendsto_jointCount_of_classEquidistribution` — **the corrected transfer principle**, proving
  `jointCount/n → L·γ(I_q)` for every CF-normal `x` and every initial state.  Because the `Prop`
  speaks only of `γ` and windows, its `L` is automatically `x`-independent — the
  `VandeheyUniformFreq` contract.  Non-vacuity anchored by `classEquidistribution_unit`.
* `VandeheyClass.classStep` + 7 `decide`-checked anchors against measured table rows;
  `exists_word_reach` (transitivity in `≤ 3` digits), `exists_return_two_and_three`
  (aperiodicity **on `X`**).
* `VandeheyMix.gaussMeasure_familySet_psi_mixing` /
  `gaussMeasure_familySetC_psi_mixing` — `|γ(E ∩ T^{-(n+g)}A) − γ(E)γ(A)| ≤ (79/100)^g γ(A) γ(E)`
  for `E` any finite/**countable** union of length-`n` cylinders.  This removes the obstruction
  `PENDING_WORK.md` had recorded twice: the multiplicative (ψ) error survives summation over a
  disjoint family, where an additive (α) error would not.
* `VandeheyRenewal.classStep_bijective`, `classSigma_bijective`, `exists_unique_source`,
  `classEvent_disjoint`, `iUnion_classEvent`, `sum_classKernel_col` — **double stochasticity**,
  hence uniform on `ℙ¹(ℤ/D)` is *exactly* stationary with nothing to compute.

## Findings recorded so they are not re-derived

* **Do not chase the scalar-character cancellation.**  For a 1-dim cocycle van der Corput kills
  the cocycle outright.  Unavailable here: the class group is `PGL₂(ℤ/D)`, for `D=2` that is
  `S₃` on three points, whose only scalar character is the sign — too coarse.  (The sign alone
  *is* accessible with no hidden state, and would give a genuine partial result if wanted.)
* **Aperiodicity must be argued on `X`, never on `G`.**  Every `B_a` has `det = −1`, so all
  generators lie in the non-identity coset of `PSL₂`: the walk **is** periodic in the group,
  period 2.  Harmless only because `PSL₂` is already transitive on `ℙ¹`.
* `ClassEquidistribution` originally demanded its bound at **all** `n`, which small `n` makes
  unsatisfiable; it is now `∀ᶠ n in atTop`.  Keep it that way.
* The digit truncation (`boundedWords`, `digitTail_le`) is **not** needed for the class renewal —
  the countable ψ-mixing lemma handles unbounded digits directly.
* Measurability of `cfDigit` is never needed: class events are countable cylinder unions *by
  definition*.
* Mathlib: `Set.Countable.measurableSet_biUnion` does not exist (use `MeasurableSet.biUnion`);
  `tsum_sub` is ENNReal-only (real: `Summable.tsum_sub`); `tsum_le_tsum` → `Summable.tsum_le_tsum`;
  `norm_tsum_le_tsum_norm` wants `Summable (‖f ·‖)`; `inner` takes the field explicitly
  (`inner ℝ x y`); `decide` cannot evaluate `ZMod` inverses (use `inv_eq_of_mul_eq_one_right`).

## NEXT (in order)

1. **Doeblin minorization at `M = 3`.**  Refine `VandeheyClass.exists_word_reach` from
   "length `≤ 3`" to "length **exactly** 3" for every pair: `some s → some t → some t' → some z`
   with `t,t' ≠ 0`; `some 0 → ∞ → some a → some z`; and the two cases targeting `∞`.  Mind the
   parity trap — `some 0` reaches `∞` in exactly 1 step and *not* in 2.  Then
   `classKernel D 3 d d' ≥ γ(I_w) > 0` uniformly.
2. **The contraction step.**  Express `ν_{n+g+3}` via `ν_n` using
   `gaussMeasure_familySetC_psi_mixing` across a gap `g` (error `(79/100)^g`), and contract the
   deviation from uniform by `1 − ε` using (1).  Iterate for `ν_m → 1/|X|` geometrically.  Double
   stochasticity means the limit is known in advance; only the contraction is owed.
3. **`ClassEquidistribution`** from (2) via `vanDerCorput_bound`, then
   `tendsto_jointCount_of_classEquidistribution` closes the transfer half.
4. **The fiber**: merging *inside* a class (the surviving half of the synchronizing story — the
   probe confirms same-lattice states do merge), so `Synchronizing` becomes a class-relative
   notion and `stateAt_eq_of_window_sync` is restated over it.
5. **§2 transducer + identity (9)**, then **§5–§6 trigger counting**, to convert joint
   (window, class, fiber) frequencies into word frequencies in `Mx`.  Only then does
   `vandeheyUniformFreq_holds` close.

`Maze.lean` still cites Vandehey 1.1 as `.cited` — repoint only once
`vandehey_matrix_action_holds` is genuinely sorry-free.
