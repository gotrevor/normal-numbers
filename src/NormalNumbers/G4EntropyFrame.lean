/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyJackson

/-!
# Entropy expedition §3C on the torus: (C) against the real Fourier machinery

`G4EntropyCapture.capture_inequality` proves (C) on an abstract pseudo-metric space.  Here it
is reproved directly on `Torus r` in the **average** metric `dAv` — which is the metric the
whole G4 argument runs in, and which is strictly weaker than the sup metric, so the abstract
version would lose the dimension dependence — with every input supplied by the machinery that
already exists:

* the Haar side from `one_sub_tube_le_integral_clipTest` (`G4Wiring`);
* the sample↔Haar transfer from `abs_sampleAvg_sub_integral_le` (`G4EntropyCapture`);
* the approximation from `jackson_of_clipTest` (`G4EntropyJackson`), whose budgets
  `κ = 1/(ρ√(D+1))` and `Λ = (2D+1)^r` **do not depend on `E`**;
* the character decay from the frame's `PropC`, which is also independent of `E`.

Conclusion (`capture_inequality_torus`): for any nonempty `E` and any `Good ⊆ P` whose
transported points land in `E`,

  `|Good|/|P| ≤ vol(tube E ρ) + δ₂ + 2/(ρ√(D+1)) + (2D+1)^r·δ₃`.

`Frame.capture_le` states it with the frame's own `PropC`/`PropD` and resolution `res = εη`, so
the only quantity in it that still has to be estimated for a *chosen collection of joint boxes*
is `vol(tube (E_K ℬ) res)` — that is exactly the cover bound (G) of brief §3B, and it is now
the single remaining obligation between the implemented schedule and E0.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace NormalNumbers.G4Entropy

open NormalNumbers.G4

/-- **(C) on the torus.**  Capture of a sub-sample forces mass on the tube. -/
theorem capture_inequality_torus {r : ℕ} (D : ℕ) {E : Set (Torus r)} (hE : E.Nonempty)
    {ρ : ℝ} (hρ : 0 < ρ)
    (P : Finset ℕ) (hP : P.Nonempty) (F S : ℕ → Torus r)
    (Good : Finset ℕ) (hGood : Good ⊆ P) (hcap : ∀ n ∈ Good, F n ∈ E)
    {δ₂ δ₃ : ℝ}
    (hD : (P.card : ℝ)⁻¹ * ∑ n ∈ P, dAv (S n) (F n) ≤ δ₂ * ρ)
    (hC : ∀ q ∈ fourierBox r D, q ≠ 0 → ‖sampleAvg P S (torusChar q)‖ ≤ δ₃)
    (hδ₃ : 0 ≤ δ₃) :
    (Good.card : ℝ) / P.card
      ≤ (volume (tube E ρ)).toReal + δ₂
        + 2 * (1 / (ρ * Real.sqrt (D + 1))) + (((2 * D + 1) ^ r : ℕ) : ℝ) * δ₃ := by
  classical
  have hcard : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  obtain ⟨c, h_approx, h_budget⟩ := jackson_of_clipTest D hE hρ
  -- the sample ↔ Haar transfer for this test
  have htrans := abs_sampleAvg_sub_integral_le (μ := (volume : Measure (Torus r)))
    (fourierBox r D) 0 (zero_mem_fourierBox _ _) torusChar torusChar_zero
    (fun q _ => integrable_torusChar q) (fun q _ hq => integral_torusChar_eq_zero hq)
    P hP S (clipTest E ρ) (integrable_clipTest hE hρ) c (1 / (ρ * Real.sqrt (D + 1)))
    h_approx hC h_budget hδ₃
  have hlow := (abs_le.1 htrans).1
  -- Haar side
  have hhaar := one_sub_tube_le_integral_clipTest (E := E) hE hρ
  -- sample side: the captured points contribute at most their transport error
  have hsample : ∑ n ∈ P, clipTest E ρ (S n)
      ≤ (∑ n ∈ P, dAv (S n) (F n)) / ρ + ((P.card : ℝ) - Good.card) := by
    have hsplit : ∑ n ∈ P, clipTest E ρ (S n)
        = ∑ n ∈ Good, clipTest E ρ (S n) + ∑ n ∈ P \ Good, clipTest E ρ (S n) :=
      (Finset.sum_sdiff hGood).symm.trans (by rw [add_comm])
    have h1 : ∑ n ∈ Good, clipTest E ρ (S n) ≤ ∑ n ∈ Good, dAv (S n) (F n) / ρ :=
      Finset.sum_le_sum fun n hn => clipTest_le_dAv hρ (hcap n hn)
    have h1' : ∑ n ∈ Good, dAv (S n) (F n) / ρ ≤ (∑ n ∈ P, dAv (S n) (F n)) / ρ := by
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right
        (Finset.sum_le_sum_of_subset_of_nonneg hGood fun n _ _ => dAv_nonneg _ _) hρ.le
    have h2 : ∑ n ∈ P \ Good, clipTest E ρ (S n) ≤ ((P \ Good).card : ℝ) := by
      calc ∑ n ∈ P \ Good, clipTest E ρ (S n) ≤ ∑ _n ∈ P \ Good, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => clipTest_le_one _ _ _
        _ = ((P \ Good).card : ℝ) := by simp
    have h3 : ((P \ Good).card : ℝ) = (P.card : ℝ) - Good.card := by
      have hle : (P \ Good).card + Good.card = P.card :=
        Finset.card_sdiff_add_card_eq_card hGood
      have : ((P \ Good).card : ℝ) + Good.card = P.card := by exact_mod_cast hle
      linarith
    rw [hsplit, ← h3]
    linarith
  have havg : sampleAvg P S (clipTest E ρ) ≤ δ₂ + 1 - (Good.card : ℝ) / P.card := by
    have hmul : ((P.card : ℝ))⁻¹ * ∑ n ∈ P, clipTest E ρ (S n)
        ≤ ((P.card : ℝ))⁻¹ * ((∑ n ∈ P, dAv (S n) (F n)) / ρ + ((P.card : ℝ) - Good.card)) :=
      mul_le_mul_of_nonneg_left hsample (by positivity)
    have hexp : ((P.card : ℝ))⁻¹ * ((∑ n ∈ P, dAv (S n) (F n)) / ρ + ((P.card : ℝ) - Good.card))
        = (((P.card : ℝ))⁻¹ * ∑ n ∈ P, dAv (S n) (F n)) / ρ + 1 - (Good.card : ℝ) / P.card := by
      field_simp
      ring
    have hD' : (((P.card : ℝ))⁻¹ * ∑ n ∈ P, dAv (S n) (F n)) / ρ ≤ δ₂ := by
      rw [div_le_iff₀ hρ]
      exact hD
    simp only [sampleAvg, smul_eq_mul]
    rw [hexp] at hmul
    linarith
  linarith

namespace Frame

variable (fr : NormalNumbers.G4.Frame)

/-- **(C) for a frame.**  With the frame's own `PropC` and `PropD`, capture of a sub-sample of
`fr.P` inside a set `E` forces `E`'s `res`-tube to carry the corresponding Haar mass, up to the
frame's own budget terms.  `E` is arbitrary: the old `fr.image` is one choice, `E_K(ℬ)` for a
data-dependent collection of joint boxes is another, and the budget terms are the same. -/
theorem capture_le {E : Set (Torus fr.r)} (hE : E.Nonempty)
    (Good : Finset ℕ) (hGood : Good ⊆ fr.P) (hcap : ∀ n ∈ Good, fr.Ffull n ∈ E)
    {δ₂ δ₃ : ℝ} (hD : fr.PropD δ₂) (hC : fr.PropC δ₃) (hδ₃ : 0 ≤ δ₃) :
    (Good.card : ℝ) / fr.P.card
      ≤ (volume (tube E fr.res)).toReal + δ₂
        + 2 * (1 / (fr.res * Real.sqrt (fr.D + 1)))
        + (((2 * fr.D + 1) ^ fr.r : ℕ) : ℝ) * δ₃ :=
  capture_inequality_torus fr.D hE fr.res_pos fr.P fr.hP fr.Ffull fr.S Good hGood hcap hD hC hδ₃

end Frame

end NormalNumbers.G4Entropy
