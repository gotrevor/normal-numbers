/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-AU: the vacuity audit of the §7 hypothesis bundles

S7-SC found that this lap's own `BlockCoupling` bundle was satisfiable for free.  The lesson —
*an existentially quantified hypothesis must have its witnesses pinned, or it reduces to its own
conclusion* — applies to every other `∃`-bundle on the §7 front, so all of them were audited.  The
results, with the two that are certifiable recorded here as kernel lemmas:

| bundle | `∃` over | verdict |
|---|---|---|
| `ImageTight` | `T` | **sound.**  The `∃ T` weakens it, but `cellSet [] T` shrinks in `T`, so the frequency claim has content at every `T`. |
| `AnchoredPullback` | `u, v, c` | **sound.**  `anchoredHitCount` counts the *exceptional* orbit times (`G^n x < u n` or `v n < G^n x`), so the cheap choice `c = 0` makes the count `0` and the hypothesis *stronger*, not weaker.  It is at least as strong as `ImageTight`, which is what the reduction needs. |
| `StateClock` | `s : ℕ → MobState` | **sound overall, but EMPTY below `T ≈ 1/η`** — certified below. |
| `BlockCoupling` / `TransducerData` | `S` | **vacuous** (S7-SC); repaired as `StateCoupling` / `StateData`. |

## What is certified here

`lowState η` is the state with image `[0, η]`: width exactly `η`, distortion exactly `1`, and
`mob t = η·t`.  When `η·T < 1` its image lies entirely below `1/T`, so **every** orbit time is
counted by `StateClock`'s comparison set and the inequality holds for free
(`blockCount_le_card_lowState`).  Hence `StateClock q r₀ η K` carries no information at thresholds
`T < 1/η`, and a future lap must use it at `T ≥ 1/η` — where the width floor forces the image
interval (length `≥ η ≥ 1/T`) to stick out above `1/T` and the condition becomes a real constraint
on `G^n x`.

This is the quantitative version of directive fact (β): the interesting regime is exactly
`T ≳ 1/η`, i.e. target scale at or below the state width.
-/
import NormalNumbers.VandeheyS7StateCouple

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-- The state whose image is `[0, η]`: `a = η, b = 0, c = 0, d = 1`. -/
noncomputable def lowState (η : ℝ) (hη : 0 < η) : MobState where
  a := η
  b := 0
  c := 0
  d := 1
  ha := hη.le
  hb := le_refl 0
  hc := le_refl 0
  hd := one_pos
  hdet := by
    show η * 1 - 0 * 0 ≠ 0
    simpa using hη.ne'

@[simp] lemma lowState_mob (η : ℝ) (hη : 0 < η) (t : ℝ) :
    (lowState η hη).mob t = η * t := by
  show (η * t + 0) / (0 * t + 1) = η * t
  ring_nf

lemma lowState_width (η : ℝ) (hη : 0 < η) : (lowState η hη).width = η := by
  rw [MobState.width_eq]
  show |η * 1 - 0 * 0| / ((0 + 1) * 1) = η
  rw [show η * 1 - 0 * 0 = η by ring, abs_of_pos hη]
  norm_num

lemma lowState_distortion (η : ℝ) (hη : 0 < η) : (lowState η hη).distortion = 1 := by
  show ((0:ℝ) + 1) / 1 = 1
  norm_num

/-- Below the threshold `1/η` the state's whole image sits under `1/T`. -/
lemma lowState_mob_lt (η : ℝ) (hη : 0 < η) {T : ℕ} (hT : 1 ≤ T)
    (hηT : η * (T : ℝ) < 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (lowState η hη).mob t < 1 / (T : ℝ) := by
  have hT0 : (0:ℝ) < (T : ℝ) := by exact_mod_cast hT
  rw [lowState_mob, lt_div_iff₀ hT0]
  calc η * t * (T : ℝ) ≤ η * 1 * (T : ℝ) := by gcongr
    _ = η * (T : ℝ) := by ring
    _ < 1 := hηT

/-- **The certificate.**  At a threshold `T < 1/η`, `StateClock`'s comparison set is *everything*,
so its inequality holds for free: the hypothesis carries no information there. -/
theorem blockCount_le_card_lowState {η : ℝ} (hη : 0 < η) {T : ℕ} (hT : 1 ≤ T)
    (hηT : η * (T : ℝ) < 1) (A : Set ℝ) (p : ℕ) (y z : ℝ)
    (hz0 : ∀ n, 0 ≤ gaussMap^[n] z) (hz1 : ∀ n, gaussMap^[n] z ≤ 1) :
    blockCount A p y
      ≤ (((Finset.range p).filter
          (fun n => (lowState η hη).mob (gaussMap^[n] z) < 1 / (T : ℝ))).card : ℝ) := by
  classical
  have hfilter : (Finset.range p).filter
      (fun n => (lowState η hη).mob (gaussMap^[n] z) < 1 / (T : ℝ)) = Finset.range p := by
    refine Finset.filter_true_of_mem fun n _ => ?_
    exact lowState_mob_lt η hη hT hηT (hz0 n) (hz1 n)
  rw [hfilter, Finset.card_range]
  -- and a block count never exceeds the number of steps
  rw [blockCount_apply]
  calc ∑ k ∈ Finset.range p, blockIndic A (gaussMap^[k] y)
      ≤ ∑ _k ∈ Finset.range p, (1:ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        unfold blockIndic
        by_cases h : gaussMap^[k] y ∈ A
        · rw [Set.indicator_of_mem h]; exact le_refl _
        · rw [Set.indicator_of_notMem h]; exact zero_le_one
    _ = (p : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

section Audit

#print axioms lowState_width
#print axioms lowState_distortion
#print axioms lowState_mob_lt
#print axioms blockCount_le_card_lowState

end Audit

end NormalNumbers.VandeheyS7
