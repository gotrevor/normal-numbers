/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadTailWiring

/-!
# Gate 5 crux, split by base: small bases certified, large bases by a crude tail

The loss of `TailReview.loss` splits over any partition of the tail bases: a lost child (parent
surviving every tail window) is killed by a window of a base in one part.  `lossIn P m` keeps the
FULL survivor set as parents and counts children killed by bases satisfying `P`.

`splitChargeBudget449_suffices`: separate delayed charges for bases `≤ B` and `> B`, with the
summed discounted budget, give `TailChargeBudget449`.

Measurement (lap 1, `scripts/cstar_models/tail5_*`, all SAMPLED): totals `loss m / mass m ≈ 0.21`
(bases 5..7, m = 2, 3); per-ancestor charging at the natural level fails, one block higher gives
7.50 at stages `n ≤ 6` (rising with depth), two blocks higher 2.84.
-/

namespace NormalNumbers.UniformBadThreshold.TailReview

open Coherent

/-- Tail windows of the non-perfect-power bases `b ≥ 5` with `P b`. -/
def tailBadIn (P : ℕ → Prop) (k a : ℕ) : Prop :=
  ∃ b : ℕ, 5 ≤ b ∧ ¬ IsPerfPow b ∧ P b ∧ ∃ n A : ℕ, Count.cell k a ⊆ Coherent.window b n A

open Classical in
/-- Weight of good children of surviving parents killed by a tail window of a base with `P`. -/
noncomputable def lossIn (P : ℕ → Prop) (m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * m))).filter (survives (6 * m)),
    ∑ j ∈ (Finset.range 64).filter (fun j =>
      Good449 (6 * (m + 1)) (64 * a + j) ∧
      ¬ Count.Alive (tailBadIn P) (6 * (m + 1)) (64 * a + j)),
      coreWeight (6 * (m + 1)) (64 * a + j)

theorem alive_of_or_left {B₁ B₂ : ℕ → ℕ → Prop} :
    ∀ {k a : ℕ}, Count.Alive (fun k a => B₁ k a ∨ B₂ k a) k a → Count.Alive B₁ k a
  | 0, _, h => h
  | _ + 1, _, h => ⟨alive_of_or_left h.1, fun hb => h.2 (Or.inl hb)⟩

theorem alive_of_or_right {B₁ B₂ : ℕ → ℕ → Prop} :
    ∀ {k a : ℕ}, Count.Alive (fun k a => B₁ k a ∨ B₂ k a) k a → Count.Alive B₂ k a
  | 0, _, h => h
  | _ + 1, _, h => ⟨alive_of_or_right h.1, fun hb => h.2 (Or.inr hb)⟩

theorem alive_congr {B₁ B₂ : ℕ → ℕ → Prop} (h : ∀ k a, B₁ k a ↔ B₂ k a) :
    ∀ {k a : ℕ}, Count.Alive B₁ k a ↔ Count.Alive B₂ k a
  | 0, _ => Iff.rfl
  | _ + 1, _ => and_congr (alive_congr h) (not_congr (h _ _))

theorem tailBad449_iff (B k a : ℕ) :
    tailBad449 k a ↔ tailBadIn (· ≤ B) k a ∨ tailBadIn (B < ·) k a := by
  unfold tailBad449 tailBadIn
  constructor
  · rintro ⟨b, h5, hp, rest⟩
    rcases le_or_gt b B with h | h
    · exact Or.inl ⟨b, h5, hp, h, rest⟩
    · exact Or.inr ⟨b, h5, hp, h, rest⟩
  · rintro (⟨b, h5, hp, -, rest⟩ | ⟨b, h5, hp, -, rest⟩) <;> exact ⟨b, h5, hp, rest⟩

/-- **The loss splits over a base cutoff.** -/
theorem loss_le_split (B m : ℕ) : loss m ≤ lossIn (· ≤ B) m + lossIn (B < ·) m := by
  classical
  unfold loss lossIn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.sum_union_inter]
  refine le_add_of_le_of_nonneg ?_ (Finset.sum_nonneg fun _ _ => coreWeight_nonneg _ _)
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_)
    (fun _ _ _ => coreWeight_nonneg _ _)
  obtain ⟨hjr, hg, hna⟩ := Finset.mem_filter.1 hj
  simp only [Finset.mem_union, Finset.mem_filter]
  by_contra hc
  push Not at hc
  apply hna
  have h1 := hc.1 hjr hg
  have h2 := hc.2 hjr hg
  exact (alive_congr (tailBad449_iff B)).2 (alive_or h1 h2)

/-- **Split crux.**  Delayed charges for the small bases `5 ≤ b ≤ B` and the large bases
`b > B` separately, whose summed discounted charges fit the gate-5 budget. -/
def SplitChargeBudget449 (B : ℕ) : Prop :=
  ∃ gamma : ℚ, 1 < gamma ∧ ∃ small large : ℕ → ℚ,
    (∀ lag, 0 ≤ small lag) ∧ (∀ lag, 0 ≤ large lag) ∧
    (∀ m, lossIn (· ≤ B) m ≤ ∑ lag ∈ Finset.range (m + 1), small lag * mass (m - lag)) ∧
    (∀ m, lossIn (B < ·) m ≤ ∑ lag ∈ Finset.range (m + 1), large lag * mass (m - lag)) ∧
    (∀ m, (∑ lag ∈ Finset.range (m + 1), (small lag + large lag) / gamma ^ lag) ≤
      (9 / 5 : ℚ) ^ 6 - gamma)

theorem splitChargeBudget449_suffices {B : ℕ} (h : SplitChargeBudget449 B) :
    TailChargeBudget449 := by
  obtain ⟨γ, hγ, s, l, hs, hl, hS, hL, hbud⟩ := h
  refine ⟨γ, hγ, fun lag => s lag + l lag, fun lag => add_nonneg (hs lag) (hl lag),
    fun m => ?_, hbud⟩
  refine (loss_le_split B m).trans ?_
  calc _ ≤ _ := add_le_add (hS m) (hL m)
    _ = _ := by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring

end NormalNumbers.UniformBadThreshold.TailReview
