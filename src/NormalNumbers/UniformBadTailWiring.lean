/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadTailReview

/-!
# Gate 5 wiring: a tail charge budget bounds `cStar` by `449/100`

* `coreDeletionRecurrence449`: summing the gate-4 growth `Coherent.wq_grow` over the disjoint
  surviving parents, `(9/5)^6 · mass m ≤ mass (m+1) + loss m`.
* `mass_pos_of_budget`: the delayed-charge induction, `γ · mass m ≤ mass (m+1)` and `mass m > 0`.
* `tailBudgetSuffices449_proof`: positive mass at every block level gives alive cells of
  `twoThreeBad ∨ tailBad449` at every level, compactness gives a limit point, which avoids every
  open window of a non-perfect-power base at exponent `449/100`; so every `c > 449/100` is
  admissible.
-/

namespace NormalNumbers.UniformBadThreshold.TailReview

open NormalNumbers.UniformBad (dnear)
open Coherent NextReview

theorem coreWeight_nonneg (k a : ℕ) : 0 ≤ coreWeight k a := wq_nonneg _

/-- Re-index a double sum over parents and digit `j < 64` as a sum over the children `64a+j`. -/
theorem sum_children_le {S : Finset ℕ} {K : ℕ} (hS : ∀ a ∈ S, a < 2 ^ K)
    (P : ℕ → ℕ → Prop) [∀ a j, Decidable (P a j)] (Q : ℕ → Prop) [DecidablePred Q]
    (hPQ : ∀ a ∈ S, ∀ j < 64, P a j → Q (64 * a + j)) (f : ℕ → ℚ) (hf : ∀ c, 0 ≤ f c) :
    ∑ a ∈ S, ∑ j ∈ (Finset.range 64).filter (P a), f (64 * a + j) ≤
      ∑ c ∈ (Finset.range (2 ^ (K + 6))).filter Q, f c := by
  have e : ∑ a ∈ S, ∑ j ∈ (Finset.range 64).filter (P a), f (64 * a + j) =
      ∑ p ∈ (S ×ˢ Finset.range 64).filter (fun p => P p.1 p.2), f (64 * p.1 + p.2) := by
    rw [Finset.sum_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.sum_filter]
  rw [e, ← Finset.sum_image (g := fun p : ℕ × ℕ => 64 * p.1 + p.2)
    (f := f) (fun p hp q hq h => by
      simp only [Finset.coe_filter, Finset.mem_product, Finset.mem_range, Set.mem_setOf_eq]
        at hp hq
      simp only at h
      ext <;> omega)]
  · refine Finset.sum_le_sum_of_subset_of_nonneg (fun c hc => ?_) (fun c _ _ => hf c)
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hc
    obtain ⟨⟨a, j⟩, ⟨⟨ha, hj⟩, hp⟩, rfl⟩ := hc
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, hPQ a ha j hj hp⟩
    have := hS a ha
    rw [pow_add]; norm_num; omega

open Classical in
/-- **Gate-4 growth summed over disjoint surviving parents.** -/
theorem coreDeletionRecurrence449 : CoreDeletionRecurrence449 := by
  intro m
  unfold mass loss
  set S := (Finset.range (2 ^ (6 * m))).filter (survives (6 * m))
  have hS : ∀ a ∈ S, a < 2 ^ (6 * m) := fun a ha => Finset.mem_range.1 (Finset.mem_filter.1 ha).1
  -- growth at each parent, split into surviving and lost children
  have hgrow : ∀ a ∈ S, (9 / 5 : ℚ) ^ 6 * coreWeight (6 * m) a ≤
      ∑ j ∈ (Finset.range 64).filter (fun j =>
          Good449 (6 * (m + 1)) (64 * a + j) ∧ Count.Alive tailBad449 (6 * (m + 1)) (64 * a + j)),
        coreWeight (6 * (m + 1)) (64 * a + j) +
      ∑ j ∈ (Finset.range 64).filter (fun j =>
          Good449 (6 * (m + 1)) (64 * a + j) ∧ ¬ Count.Alive tailBad449 (6 * (m + 1)) (64 * a + j)),
        coreWeight (6 * (m + 1)) (64 * a + j) := by
    intro a ha
    have hg := (Finset.mem_filter.1 ha).2.1
    have := wq_grow hg
    rw [show 6 * m + 6 = 6 * (m + 1) by ring] at this
    unfold coreWeight
    rw [← Finset.sum_union]
    · convert this using 2
      ext j; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    · exact Finset.disjoint_filter.2 fun j _ h1 h2 => h2.2 h1.2
  calc (9 / 5 : ℚ) ^ 6 * ∑ a ∈ S, coreWeight (6 * m) a
      = ∑ a ∈ S, (9 / 5 : ℚ) ^ 6 * coreWeight (6 * m) a := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum hgrow
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := by
      gcongr
      have := sum_children_le hS
        (fun a j => Good449 (6 * (m + 1)) (64 * a + j) ∧
          Count.Alive tailBad449 (6 * (m + 1)) (64 * a + j))
        (survives (6 * (m + 1))) (fun a _ j _ h => h) (coreWeight (6 * (m + 1)))
        (coreWeight_nonneg _)
      rwa [show 6 * m + 6 = 6 * (m + 1) by ring] at this

theorem survives_zero : survives 0 0 := by
  refine ⟨⟨by norm_num, fun n m h1 h2 => by omega, fun n A hn => absurd hn ?_⟩, rfl⟩
  have := δ3_bounds.2
  have h1 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  norm_num at this ⊢; linarith

open Classical in
theorem mass_zero : mass 0 = 1 := by
  unfold mass
  rw [show 6 * 0 = 0 from rfl, pow_zero, Finset.range_one, Finset.filter_singleton,
    if_pos survives_zero, Finset.sum_singleton]
  unfold coreWeight classify wq; simp

/-- **Delayed-charge induction.**  Under a tail charge budget, block mass grows by `γ > 1`. -/
theorem mass_pos_of_budget (h : TailChargeBudget449) : ∀ m, 0 < mass m := by
  obtain ⟨γ, hγ, c, hc0, hloss, hbud⟩ := h
  have hγ0 : 0 < γ := by linarith
  have key : ∀ m, 0 < mass m ∧ ∀ l ≤ m, γ ^ l * mass (m - l) ≤ mass m := by
    intro m
    induction m with
    | zero => exact ⟨by rw [mass_zero]; norm_num, fun l hl => by
        obtain rfl : l = 0 := by omega
        simp⟩
    | succ m ih =>
      obtain ⟨hpos, hdec⟩ := ih
      have hL : loss m ≤ ((9 / 5 : ℚ) ^ 6 - γ) * mass m := by
        refine (hloss m).trans ?_
        calc ∑ l ∈ Finset.range (m + 1), c l * mass (m - l)
            ≤ ∑ l ∈ Finset.range (m + 1), c l / γ ^ l * mass m := by
              refine Finset.sum_le_sum fun l hl => ?_
              have h1 := hdec l (by simpa [Nat.lt_succ_iff] using hl)
              have hgl : 0 < γ ^ l := pow_pos hγ0 l
              rw [div_mul_eq_mul_div, le_div_iff₀ hgl]
              have := mul_le_mul_of_nonneg_left h1 (hc0 l)
              linarith
          _ = (∑ l ∈ Finset.range (m + 1), c l / γ ^ l) * mass m := (Finset.sum_mul _ _ _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right (hbud m) hpos.le
      have hrec := coreDeletionRecurrence449 m
      have hnext : γ * mass m ≤ mass (m + 1) := by nlinarith
      refine ⟨lt_of_lt_of_le (mul_pos hγ0 hpos) hnext, fun l hl => ?_⟩
      rcases l with _ | l
      · simp
      · have := hdec l (by omega)
        rw [show m + 1 - (l + 1) = m - l by omega, pow_succ]
        calc γ ^ l * γ * mass (m - l) = γ * (γ ^ l * mass (m - l)) := by ring
          _ ≤ γ * mass m := mul_le_mul_of_nonneg_left this hγ0.le
          _ ≤ _ := hnext
  exact fun m => (key m).1

/-- The combined pruning: base-2/3 windows or a tail window. -/
def allBad449 (k a : ℕ) : Prop := twoThreeBad (449 / 100) k a ∨ tailBad449 k a

theorem alive_or {B₁ B₂ : ℕ → ℕ → Prop} :
    ∀ {k a : ℕ}, Count.Alive B₁ k a → Count.Alive B₂ k a →
      Count.Alive (fun k a => B₁ k a ∨ B₂ k a) k a
  | 0, a, h, _ => h
  | k + 1, a, h₁, h₂ => ⟨alive_or h₁.1 h₂.1, fun h => h.elim h₁.2 h₂.2⟩

open Classical in
theorem exists_alive_of_mass_pos {m : ℕ} (h : 0 < mass m) :
    ∃ a, Count.Alive allBad449 (6 * m) a := by
  unfold mass at h
  obtain ⟨a, ha, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  obtain ⟨-, hg, hal⟩ := Finset.mem_filter.1 ha
  exact ⟨a, alive_or (clean449_alive (good449_clean hg)) hal⟩

/-- **Limit point**: under a tail charge budget some `ξ` lies in an alive cell of every level. -/
theorem exists_limit (h : TailChargeBudget449) :
    ∃ ξ : ℝ, ∀ k, ∃ a, Count.Alive allBad449 k a ∧ ξ ∈ Count.cell k a := by
  refine Count.exists_mem_cells allBad449 fun k => ?_
  obtain ⟨a, ha⟩ := exists_alive_of_mass_pos (mass_pos_of_budget h k)
  have := Count.alive_anc allBad449 (k := k) (5 * k) (by rwa [show k + 5 * k = 6 * k by ring])
  exact Finset.card_pos.2 ⟨_, (Count.mem_aliveSet allBad449).2 this⟩

/-- A cell containing `ξ` sits inside every window whose interior contains `ξ` with room to
spare. -/
theorem cell_sub_window {ξ : ℝ} {b n k a : ℕ} {A : ℤ} (hb : 1 ≤ b) (hξ : ξ ∈ Count.cell k a)
    (hroom : |(b : ℝ) ^ n * ξ - A| + (b : ℝ) ^ n / 2 ^ k ≤ (b : ℝ) ^ (-(449 / 100 : ℝ))) :
    Count.cell k a ⊆ Set.Icc (((A : ℝ) - (b : ℝ) ^ (-(449 / 100 : ℝ))) / (b : ℝ) ^ n)
      (((A : ℝ) + (b : ℝ) ^ (-(449 / 100 : ℝ))) / (b : ℝ) ^ n) := by
  intro y hy
  have hbn : (0 : ℝ) < (b : ℝ) ^ n := pow_pos (by exact_mod_cast hb) n
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  obtain ⟨hξ1, hξ2⟩ := hξ
  obtain ⟨hy1, hy2⟩ := hy
  have hd : |y - ξ| ≤ 1 / 2 ^ k := by
    rw [abs_le]
    constructor
    · have : ((a : ℝ) + 1) / 2 ^ k - a / 2 ^ k = 1 / 2 ^ k := by ring
      linarith
    · have : ((a : ℝ) + 1) / 2 ^ k - a / 2 ^ k = 1 / 2 ^ k := by ring
      linarith
  have hby : |(b : ℝ) ^ n * y - A| ≤ (b : ℝ) ^ (-(449 / 100 : ℝ)) := by
    calc |(b : ℝ) ^ n * y - A| = |((b : ℝ) ^ n * ξ - A) + (b : ℝ) ^ n * (y - ξ)| := by ring_nf
      _ ≤ |(b : ℝ) ^ n * ξ - A| + |(b : ℝ) ^ n * (y - ξ)| := abs_add_le _ _
      _ ≤ |(b : ℝ) ^ n * ξ - A| + (b : ℝ) ^ n / 2 ^ k := by
        rw [abs_mul, abs_of_pos hbn, div_eq_mul_one_div]
        gcongr
      _ ≤ _ := hroom
  rw [abs_le] at hby
  constructor
  · rw [div_le_iff₀ hbn]; linarith
  · rw [le_div_iff₀ hbn]; linarith

/-- **Weak avoidance at 449/100** for every non-perfect-power base. -/
theorem weak_avoid {ξ : ℝ} (hξ : ∀ k, ∃ a, Count.Alive allBad449 k a ∧ ξ ∈ Count.cell k a)
    {b : ℕ} (hb : 2 ≤ b) (hpp : ¬ IsPerfPow b) (n : ℕ) :
    (b : ℝ) ^ (-(449 / 100 : ℝ)) ≤ dnear ((b : ℝ) ^ n * ξ) := by
  by_contra hlt
  push Not at hlt
  set r := (b : ℝ) ^ (-(449 / 100 : ℝ))
  set x := (b : ℝ) ^ n * ξ
  have hbn : (0 : ℝ) < (b : ℝ) ^ n := pow_pos (by exact_mod_cast (by omega : 0 < b)) n
  -- ξ ≥ 0 (it lies in cell 0 0 = [0,1])
  have hξ0 : 0 ≤ ξ := by
    obtain ⟨a, ha, hx⟩ := hξ 0
    have : a = 0 := ha
    subst this
    simpa using hx.1
  have hx0 : 0 ≤ x := mul_nonneg hbn.le hξ0
  set A : ℤ := round x
  have hA0 : 0 ≤ A := by
    by_contra hc; push Not at hc
    have h1 : (A : ℝ) ≤ -1 := by exact_mod_cast (show A ≤ -1 by omega)
    have h2 := abs_sub_round x
    rw [abs_le] at h2
    linarith [h2.2]
  have hdA : dnear x = |x - A| := rfl
  -- a fine enough level
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one (show 0 < (r - dnear x) / (b : ℝ) ^ n from
    div_pos (by linarith) hbn) (by norm_num : (1 / 2 : ℝ) < 1)
  set k := k₀ + 1
  obtain ⟨a, ha, hxa⟩ := hξ k
  have hroom : |x - A| + (b : ℝ) ^ n / 2 ^ k ≤ r := by
    have h1 : (b : ℝ) ^ n / 2 ^ k ≤ (b : ℝ) ^ n * (1 / 2) ^ k₀ := by
      rw [div_eq_mul_inv]
      gcongr
      rw [one_div, inv_pow, pow_succ]
      exact inv_anti₀ (by positivity) (by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k₀])
    have h2 : (b : ℝ) ^ n * (1 / 2) ^ k₀ < r - dnear x := by
      rw [lt_div_iff₀ hbn] at hk₀; linarith
    linarith
  have hsub := cell_sub_window (A := A) (by omega) hxa hroom
  have hbad : allBad449 k a := by
    rcases (show b = 2 ∨ b = 3 ∨ b = 4 ∨ 5 ≤ b by omega) with rfl | rfl | rfl | h5
    · exact Or.inl ⟨2, Or.inl rfl, n, A.toNat, by
        rw [show ((A.toNat : ℕ) : ℝ) = (A : ℝ) by exact_mod_cast Int.toNat_of_nonneg hA0]
        simpa using hsub⟩
    · exact Or.inl ⟨3, Or.inr rfl, n, A.toNat, by
        rw [show ((A.toNat : ℕ) : ℝ) = (A : ℝ) by exact_mod_cast Int.toNat_of_nonneg hA0]
        simpa using hsub⟩
    · exact absurd ⟨2, 2, le_rfl, by norm_num⟩ hpp
    · refine Or.inr ⟨b, h5, hpp, n, A.toNat, ?_⟩
      unfold Coherent.window
      rw [show ((A.toNat : ℕ) : ℝ) = (A : ℝ) by exact_mod_cast Int.toNat_of_nonneg hA0]
      exact hsub
  exact ha.2 hbad

/-- **Gate 5 wiring.** -/
theorem tailBudgetSuffices449_proof : TailBudgetSuffices449 := by
  intro h
  obtain ⟨ξ, hξ⟩ := exists_limit h
  have hadm : ∀ c : ℝ, 449 / 100 < c → Admissible c := by
    intro c hc
    refine (admissible_iff_nonPerfectPow (by linarith)).2 ⟨ξ, fun b hb hpp n => ?_⟩
    refine lt_of_lt_of_le ?_ (weak_avoid hξ hb hpp n)
    have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
    exact Real.rpow_lt_rpow_of_exponent_lt hb1 (by linarith)
  exact le_of_forall_gt_imp_ge_of_dense fun c hc => csInf_le bddBelow_admissible (hadm c hc)

end NormalNumbers.UniformBadThreshold.TailReview
