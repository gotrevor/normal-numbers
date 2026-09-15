# HANDOFF — lap 126: 🏁 `IsNormal 2 fullRealW` — the expedition's endpoint, proved

**Branch** `wip/g4-entropy`.  **HEAD** `6abd3f0`+.  `lake build` 🟢 **9024 jobs**.
`src/` carries **two** `sorry`s, both pre-expedition and off-path and both on the
forbidden-drift list (`PrimeLambertOscillation.phaseOscillation`,
`MahlerDriftOne.exists_drift_one_background`).  **The entropy expedition's part of `src/` is
sorry-free.**

## The result

```
G4.Sched.isNormal_fullRealW : IsNormal 2 fullRealW
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

`fullRealW = realOfDigits 2 (fullDigW (primeLambertAtBase 4))` — the real whose `j`-th **binary**
digit is `G₄`'s `fullPosW j`-th binary digit.  The unwound audit statement
(`G4EntropyWStatement.isNormal_two_of_schedule_read`):

> `∃ p : ℕ → ℕ, StrictMono p ∧ (∀ j, digitOf 2 fullRealW j = digitOf 2 (Int.fract G₄) (p j))`
> `∧ IsNormal 2 fullRealW`

`fullPosW` takes **no real argument at all** — that is the machine-checkable form of "schedule
only".  `digitOf_fullRealW` is the faithfulness step: `fullRealW`'s **own** binary expansion *is*
the read, not merely a number assembled from those digits.  Corollaries:
`fullRealW_mem_Ico`, `isDisjunctive_fullRealW`, `irrational_fullRealW`.

**Scope, stated exactly**: this is a theorem about `fullRealW`.  It says **nothing** about the
normality of `G₄` itself, and the ACTIVE override forbids claiming otherwise.

## This lap's four commits

| commit | content |
|---|---|
| `927ad8c` | review lap 126: direction KEPT, narrowed to the squeeze + the endpoint |
| `d58cb25` | skeleton — the mediant lemma proved, five named leaves |
| `c1a55b7` | 🎯 `abs_ratio_mid_le` — mid-band control at an ARBITRARY read index |
| `c840b22` | 🎯🎯 `IsNormal 2 fullRealW` |
| `6abd3f0` | the audit surface (`G4EntropyWStatement`) + corollaries |

## The two ideas that closed it (do not re-derive)

1. **`kk_mul_KK_le_fTW` — `head_frac_tiny` at `a = 1`.**  One read window is a `1/KK` fraction of
   the history before it.  That single fact pays for the ungated head, the partial window at the
   end of the increment, and the `a = 0` stub; none of them then needs a certificate of its own.
   It follows because `headW i ≥ 1` (`bandWtr i (16·wFloor i)` is nonempty, `P₀ ≤ wFloor`).

2. **The case threshold is `a` vs `⌊√(KK j)⌋`, and it *must* move with `K`.**  A fixed threshold
   cannot work: at `a = 1` the certified branch's leftover `2·kk/s` is `O(1)`.  Balancing the two
   branches at `2/√K` each gives
   `midErrW i ℓ = 2√(808·log2·ℓ/√(KK i)) + 128/KK i + 2ℓ/kk i + 2/⌊√(KK i)⌋`, and all three
   branches (short / gated / ungated) land under it:
   * `a ≤ A`: `s·A ≤ (A²+A)·kk ≤ 2·kk·KK ≤ 2T`, error `2/A`;
   * `a > A`, gated: leftover `2E/s = 2aℓ/s + 2kk/s ≤ 2ℓ/kk + 2/a ≤ 2ℓ/kk + 2/A`;
   * `a > A`, ungated: `aLe_le_headW` + `head_frac_tiny` give `s·KK ≤ 2T` again.

3. **Non-vacuity was free.**  Lap 125 expected `exists_matchesAt_fullDigW` to need "a wide
   non-vacuity witness".  It does not: once the frequency limit holds at every `n`, the limit
   `2^{−|v|} > 0` forces `winCount v n > 0` directly.

## New modules

* `G4EntropyWMediant.lean` — `mediant_abs_le`, `mediant_abs_le_max`, `mediant_abs_le_trivial`
  (pure ℝ; deviations of history and increment simply add).
* `G4EntropyWSqueeze.lean` — `winCount_mono`, `winCount_sub_le`, `one_le_headW`,
  `kk_mul_KK_le_fTW`, `incr_bounds`, `midErrW`, `mid_gated_core`, `mid_trivial_core`,
  `mid_assemble_gated`, `mid_assemble_trivial`, `abs_ratio_mid_le`, `tendsto_natSqrt_KK_atTop`,
  `tendsto_midErrW`, `tendsto_fgrpW_atTop`, `tendsto_winCount_fullDigW`,
  `isNormalSequence_fullDigW`, `exists_matchesAt_fullDigW`, `properDigits_fullDigW`,
  `fullRealW`, `isNormal_fullRealW`.
* `G4EntropyWStatement.lean` — the audit surface and the corollaries.

## Hygiene (new this lap)

* `abs_add` does not exist here — it is **`abs_add_le a b`**.
* `div_le_div_iff` does not exist here — it is **`div_le_div_iff₀`**.
* `Nat.sqrt_le' n : (Nat.sqrt n)^2 ≤ n` (a `^2`, not `n.sqrt * n.sqrt`); convert with `nlinarith`.
* `div_le_div_of_nonneg_right h hpos` wants `0 ≤ c`, not `0 < c`, in this mathlib.
* `omega` **does** atomize a nonlinear product like `a * kk i`, but `(a+1) * kk i` and
  `kk i * a` are *different atoms*.  Normalize the shape first (`rw [add_mul, one_mul]`, or add
  `Nat.mul_comm` as a hypothesis) before handing it to `omega`.
* `Nat.div_lt_of_lt_mul` wants `m < k * n` — the *other* factor order from `fLW`'s definition.
* Implicit variables that occur only in a lemma's **conclusion** (`mid_gated_core`'s `G`) cannot
  be inferred from the hypotheses: pass `(G := …)` explicitly when using it in a `have`.

## Status of the governing documents

* `DIRECTION.md`'s lap-126 CURRENT DIRECTIVE 🎯 objective: **MET**.
* The ACTIVE operator override's stop condition ("stop when the endpoint is proved axiom-clean"):
  **DISCHARGED**.
* Route trigger **E-T7** applies: this lap does **not** pick its own successor.  Candidates for
  the next altitude lap are recorded in `STATUS.md` → Outstanding → Short-term (chiefly
  `IsNormal 4 fullRealW` / `IsNormal (2^k)`, which needs the read's word frequencies restricted
  to a residue class of positions; the entropy machinery supports it at a cost of `√k`, since the
  block-entropy deficit over a sub-class is bounded by the total deficit).
* An independent NL→formalization **faithfulness cross-check** of the headline was submitted to
  Aristotle from prose only (project `48c7d703-d18e-4e47-ae9c-6734f6737047`); its returned
  statement should be compared with `isNormal_two_of_schedule_read` for logical equivalence.
