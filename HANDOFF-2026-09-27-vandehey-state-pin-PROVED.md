# HANDOFF — Vandehey 2017 Theorem 1.1: **the crux is proved**

**Branch** `wip/vandehey-matrix-action` · **HEAD** `5701e7d` · `lake build` 🟢 9288 jobs ·
working tree clean · nothing pushed.

**Scoped objective (`LEAN_DONE_WHEN`)**: `sorry`-free
`src/NormalNumbers/LiteratureVandehey.lean`, i.e. prove
`Literature.vandeheyUniformFreq_holds` (no weakening/renaming of the `def` or theorem).
`DIRECTION.md` CURRENT DIRECTIVE governs and was obeyed: its mandated items 1–3 (gap-0 Rényi,
Doeblin at length 3, **the contraction**) are now all done.

## Headline of this session

`VandeheyState.stateHorizonIntegral_pin` in `src/NormalNumbers/VandeheyStatePin.lean` is
**sorry-free**, trust triple `[propext, Classical.choice, Quot.sound]`:

> For an automaton `δ` on a finite nonempty state space whose every digit step `d ↦ δ d a` is a
> bijection, and whose every pair of states is joined by a genuine digit word of length `M ≥ 2`,
> there exist `C ≥ 0` and `θ < 1` with
> `|F_n(d,s)(τ) − (card S)⁻¹·γ(A)| ≤ C·θⁿ·γ(A)` for every `n`, every `d, s`, every `τ ∈ [0,1]`,
> where `F_n(d,s)(τ) = ∫_{y : Tⁿy ∈ A, runState δ d (W_n y) = s} h_τ`.

This is the state-refined equidistribution that the **adjacency obstruction** had blocked (the
class at time `n` and the digit window at time `n` overlap; every `classStep` is a bijection so
nothing is forgotten; no ψ-mixing gap can separate them).  The resolution: the transfer operator
IS the tool for adjacency, because it computes the conditional law of the future given the past
with no gap at all.

## What was proved, in order (all in `src/`, all sorry-free)

`src/NormalNumbers/VandeheyStatePin.lean` (new, wired into `NormalNumbers.lean`):

* `stateHorizonIntegral_succ` — the refined recursion `F_{n+1}(d,s) = Σ_a w_τ(a)F_n(δ d a,s)(τ_a)`.
* `measurableSet_stateEq`, `stateHorizonIntegral_nonneg / _le / _le_two` — the cone.
* `sum_stateHorizonIntegral` (`Σ_s F_n(d,s) = G_n`) and
  **`sum_over_initial_stateHorizonIntegral`** (`Σ_d F_n(d,s) = G_n` for every `s`, from
  bijectivity).  Together: the disintegration is **doubly stochastic**, so the limit constant is
  forced to `(card S)⁻¹γ(A)` and never has to be computed.
* `InCone`, `stepWeight_ge`, `stateStepIter`, `stateHorizonIntegral_iter / _add`,
  `stateStepIter_add`, the affine algebra (`stateStepOp_sub_const`, `stateStepIter_const_sub`, …),
  the range API (`famRange / famSup / famInf / exists_gt_famSup_sub / …`).
* **`stateStepIter_ge_word`** — the Doeblin minorization at operator level:
  `wordWeight w · c ≤ L^{|w|}Φ(d,τ)` when `c ≤ Φ(runState δ d w, ·)`, with
  `wordWeight w = ∏_{a∈w} 1/((a+1)(a+2)) > 0`.  No word expansion: a nonnegative `tsum`
  dominates the term indexed by the next letter, and induction runs along `w`.
* **`stateStepOp_logLipschitz`** — the tail direction contracts by `2/5` per step:
  `|LΦ(d,t) − LΦ(d,t')| ≤ ((2/5)L + (3/5)r)·d(t,t')`.
* **`stateStepIter_doeblin_two_sided`** — the state direction contracts by `1 − 2β` per
  `M`-block, by the **one-point** Doeblin argument (one word per `(d, target)`; no expansion).
* **`stateStepIter_osc_geom`** — the Lyapunov step: `V = osc + 2β·Lip` obeys `V' ≤ (1−β)V`.
* `stateHorizonIntegral_zero`, `horizonIntegral_zero_le`, `stateStepIter_osc_le`,
  `geom_block_bound`, `famRange_congr`, and the assembly `stateHorizonIntegral_pin`.

`src/NormalNumbers/VandeheyWeightTV.lean` (new, wired):

* **`tsum_abs_stepWeight_sub_le`** — `Σ_k |w_τ(k) − w_{τ'}(k)| ≤ (3/5)·d(τ,τ')`.
* **`tsum_abs_Afamily_le`** — the `A`-series for a `k`-indexed family, `≤ (2/5)·L·d`.
* Supporting: `stepWeight_sub_eq` (exact factorization), `stepWeight_mono_two_le`,
  `two_mul_sub_div_le_log_sub`, `abs_stepWeight_zero_sub_le`, `abs_stepWeight_one_sub_le`,
  `abs_Aterm_le`.

`src/NormalNumbers/CFPsiPin.lean`: only `abs_log_stepPt_sub_le` and `summable_sq_bound'` were
**de-privatised** for reuse.  No proof in that file was modified.

## Two findings worth not re-deriving

1. **The Abel resummation is unnecessary.**  The previous plan was to generalize
   `CFPsiPin.stepOp_logLipschitz`'s `B`-series by Abel-resumming in blocks of `D` (using that
   `classStep D` reads the digit only mod `D`).  Don't.  Because `Σ_k w_τ(k) = 1` for every `τ`,
   the `B`-series is invariant under subtracting a constant from `ψ`, hence bounded by
   `½·osc(ψ)·Σ_k|Δ_k|`.  The whole family question collapses to the scalar
   `tsum_abs_stepWeight_sub_le`.  Its proof: `Δ_k` factors as
   `(a−b)(k²+k−ab)/((k+a)(k+1+a)(k+b)(k+1+b))` with `a = 1+τ`, `b = 1+τ'`, so `Δ_k ≥ 0` for
   **every** `k ≥ 2` (`k²+k ≥ 6 > 4 ≥ ab`); with `Σ_kΔ_k = 0` the entire ℓ¹ norm sits on the two
   lowest branches, `Σ|Δ_k| ≤ 2|Δ₀| + 2|Δ₁| ≤ (¼ + 1/30)·2·d = (17/30)d`.
2. **The constants are load-bearing, not cosmetic.**  The Lyapunov step needs
   `log 2 + (2/5)^M ≤ 1 − β`.  With the scalar file's deliberately loose `3/4` in place of `2/5`
   the cross term exceeds `1` and the scheme fails outright.  Likewise the ℓ¹ modulus needed
   `< 1/(2 log 2) ≈ 0.7213` and came out at `0.567`.  If either constant is ever loosened during
   a refactor, the contraction dies silently.

## NEXT (in order)

1. **Instantiate `stateHorizonIntegral_pin` at the class automaton.**  `S = ClassSpace D`
   (`= Option (ZMod D)`; confirm `Fintype`, `DecidableEq`, `Nonempty` instances are in scope —
   they should be for `D > 0`), `δ = classStep D`, `M = 3` from
   `VandeheyRenyi.Doeblin.exists_classWord_three`, `hbij` from
   `VandeheyRenewal.classStep_bijective`.  This is bookkeeping; the mathematics is done.
2. **Derive `VandeheyCocycle.ClassEquidistribution (classStep D) t q`** from the pin.  The pin is
   its quantitative form; the passage runs through `vanDerCorput_bound` / `cesaro_shift_bound`
   (already in `VandeheyCocycle.lean`).  Mind that `ClassEquidistribution` is stated with
   `∀ᶠ n in atTop` — keep it that way (small `n` makes an all-`n` version unsatisfiable).
3. `tendsto_jointCount_of_classEquidistribution` then closes the transfer half, giving
   `VandeheyUniformFreq`-shaped data for every CF-normal `x` and every initial state.
4. **The fiber**: merging *inside* a class (`Synchronizing` becomes a class-relative notion;
   `probes/cf_transducer_class.py` confirms same-row-lattice states do merge).
5. **§2 transducer + identity (9)**, then **§5–§6 trigger counting**, converting joint
   (window, class, fiber) frequencies into word frequencies in `Mx`.  Only then does
   `vandeheyUniformFreq_holds` close.
6. Repoint the `Maze.lean` row citing Vandehey 1.1 from `.cited` once
   `vandehey_matrix_action_holds` is genuinely sorry-free.

## Designated-open, do not touch

`VandeheyAut.exists_jointFreq_limit` (`VandeheyAutomaton.lean:622`) — its `Synchronizing`
hypothesis is **unsatisfiable** for the transducer Theorem 1.1 needs
(`PROBE-2026-09-27-transducer-not-synchronizing.md`).  Proving it would prove something about an
empty hypothesis.  Leave it.
