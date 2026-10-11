/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.UniformBadTail

/-!
# Operator gate 6, fallback (a): fold small tail bases into the shared-phase core

A second route to the frozen headline `Tail.cStar_le_449`, beside the gate-5 statements
(`TailReview.TailChargeBudget449`, `Tail.tailBudgetSuffices449`), which stay untouched.
The core runs over `{2,3} ∪ F` with `F ⊆ {5,6,7}`; the weighted tail runs over the remaining
non-perfect-power bases `b ≥ 5`, `b ∉ F`.

## Screen (2026-10-11, `scripts/cstar_models/gate6/`, sampled, so upper bounds on a certificate)

`sharedF.js` is `shared3.js` with one extra phase `(x_b, u_b)` per base of `F`.  Controls:
`F = ∅` gives 1.8382 (gate 4: 1.8373), zero radius for base 5 gives the same value, and
deleting every child kills the tree.  Growth per level at 4.49, block `D = 6`:
* `F = {5}`: 1.8311 (base-5 phase bins 64, 128, 256 give 1.8311, 1.8310, 1.8327).
  The target was 1.79 + 0.02.
* `F = {5,6}` and `{5,6,7}`, coarse phases: 1.8368 and 1.8382, against targets 1.75 and 1.715.

The pick is the cheapest `F` that clears its target, `F = {5}`.  The tail was then re-screened
(`tail_kf.py`, the refinements (i)+(ii)+(iii) of `tail5_refined.py`) with this core's own run
sums `f` and layer-cake `e'`, computed on real cells (levels 10..16, screen weights), at core
growth `9/5`:
* `F = {5}`: gap 0.742.  The same instrument with `F = ∅` weights gives 0.664, where the
  certified gate-4 weights give 0.737.  Scaled by that control, the estimate is about 0.82.
* `F = {5,6}`, as a backup: gap 0.372.
Both are below 1, so the gate-6 kill did not fire.  The 0.82 leaves little headroom for
certification losses, and `{5,6}` is the fallback if the exact core or tail certificate for
`{5}` comes in short.  These are sampled numbers, not certificates.

## Statements (frozen for Codex's semantic review before any proof)

* `CoherentCore449F F g`: the gate-4 probe gate `NextReview.CoherentTwoThree449`, with `F` added
  to the core's bases.
* `WeightedCore449F F g wt Good`: the interface the wiring consumes.  It mirrors the facts gate 4
  proved about `Coherent.wq ∘ Coherent.classify` on `Coherent.Good449`: nonnegative weights,
  root weight 1, good cells alive in the core, and six-level growth `g^6`.
* `TailChargeBudget449F F g wt Good`: `TailReview.TailChargeBudget449` with the fold-tail bases,
  the given core, and the budget `g^6 - γ`.
* `TailBudgetSuffices449F`: the wiring to `cStar ≤ 449/100`.
-/

namespace NormalNumbers.UniformBadThreshold.Fold

open NextReview

/-- The chosen fold set (gate-6 screen). -/
def F5 : Finset ℕ := {5}

/-- Core containment pruning over `{2,3} ∪ F` at exponent `449/100`. -/
def coreBadF (F : Finset ℕ) (k a : ℕ) : Prop :=
  ∃ b : ℕ, (b = 2 ∨ b = 3 ∨ b ∈ F) ∧ ∃ n A : ℕ,
    Count.cell k a ⊆ Coherent.window b n A

/-- Remaining tail: non-perfect-power bases `b ≥ 5` outside `F`, including stage zero. -/
def tailBadF (F : Finset ℕ) (k a : ℕ) : Prop :=
  ∃ b : ℕ, 5 ≤ b ∧ ¬ IsPerfPow b ∧ b ∉ F ∧ ∃ n A : ℕ,
    Count.cell k a ⊆ Coherent.window b n A

/-- Gate-6 probe gate: an exact joint core over `{2,3} ∪ F` at 4.49 with bounded finite-state
weights and block growth at least `g`.  Mirrors `NextReview.CoherentTwoThree449`. -/
def CoherentCore449F (F : Finset ℕ) (g : ℚ) : Prop :=
  ∃ D : ℕ, D ≤ 12 ∧ CoherentBlockCertificate (coreBadF F) D g

open Classical in
/-- What the exact gate-6 certificate must deliver to the wiring (the analogue of
`Coherent.wq_nonneg`, the root `Good 0 0` with weight 1, `good449_clean`/`clean449_alive`, and
`Coherent.wq_grow`).  No upper bound on the weights and no heredity of `Good` is required. -/
def WeightedCore449F (F : Finset ℕ) (g : ℚ) (wt : ℕ → ℕ → ℚ) (Good : ℕ → ℕ → Prop) : Prop :=
  (∀ k a, 0 ≤ wt k a) ∧ Good 0 0 ∧ wt 0 0 = 1 ∧
  (∀ k a, Good k a → Count.Alive (coreBadF F) k a) ∧
  (∀ k a, Good k a →
    g ^ 6 * wt k a ≤
      ∑ j ∈ (Finset.range 64).filter (fun j => Good (k + 6) (64 * a + j)),
        wt (k + 6) (64 * a + j))

/-- A good core cell that has survived every fold-tail containment test so far. -/
def survivesF (F : Finset ℕ) (Good : ℕ → ℕ → Prop) (k a : ℕ) : Prop :=
  Good k a ∧ Count.Alive (tailBadF F) k a

open Classical in
/-- Total surviving core weight at binary level `6m`. -/
noncomputable def massF (F : Finset ℕ) (wt : ℕ → ℕ → ℚ) (Good : ℕ → ℕ → Prop) (m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * m))).filter (survivesF F Good (6 * m)), wt (6 * m) a

open Classical in
/-- Weight of good depth-six descendants lost to the fold tail, from surviving parents. -/
noncomputable def lossF (F : Finset ℕ) (wt : ℕ → ℕ → ℚ) (Good : ℕ → ℕ → Prop) (m : ℕ) : ℚ :=
  ∑ a ∈ (Finset.range (2 ^ (6 * m))).filter (survivesF F Good (6 * m)),
    ∑ j ∈ (Finset.range 64).filter (fun j =>
      Good (6 * (m + 1)) (64 * a + j) ∧
      ¬ Count.Alive (tailBadF F) (6 * (m + 1)) (64 * a + j)),
      wt (6 * (m + 1)) (64 * a + j)

/-- Gate-6 tail crux: `TailReview.TailChargeBudget449` over the fold tail, for the given core,
with the budget `g^6 - γ`.  Every finite partial budget must fit. -/
def TailChargeBudget449F (F : Finset ℕ) (g : ℚ) (wt : ℕ → ℕ → ℚ)
    (Good : ℕ → ℕ → Prop) : Prop :=
  ∃ gamma : ℚ, 1 < gamma ∧ ∃ charge : ℕ → ℚ,
    (∀ lag, 0 ≤ charge lag) ∧
    (∀ m, lossF F wt Good m ≤
      ∑ lag ∈ Finset.range (m + 1), charge lag * massF F wt Good (m - lag)) ∧
    (∀ m, (∑ lag ∈ Finset.range (m + 1), charge lag / gamma ^ lag) ≤ g ^ 6 - gamma)

/-- Gate-6 wiring: a weighted fold core plus a fold-tail budget bounds `cStar` by `449/100`.
Same proof shape as `TailReview.tailBudgetSuffices449_proof`. -/
def TailBudgetSuffices449F : Prop :=
  ∀ (F : Finset ℕ) (g : ℚ) (wt : ℕ → ℕ → ℚ) (Good : ℕ → ℕ → Prop),
    WeightedCore449F F g wt Good → TailChargeBudget449F F g wt Good → cStar ≤ 449 / 100

section Wiring

open NormalNumbers.UniformBad (dnear)
open TailReview (sum_children_le alive_or cell_sub_window)

variable {F : Finset ℕ} {g : ℚ} {wt : ℕ → ℕ → ℚ} {Good : ℕ → ℕ → Prop}

open Classical in
/-- Core growth summed over ALL surviving parents (zero-weight ones included). -/
theorem recurrenceF (hc : WeightedCore449F F g wt Good) (m : ℕ) :
    g ^ 6 * massF F wt Good m ≤ massF F wt Good (m + 1) + lossF F wt Good m := by
  obtain ⟨hnn, -, -, halive, hgrowth⟩ := hc
  unfold massF lossF
  set S := (Finset.range (2 ^ (6 * m))).filter (survivesF F Good (6 * m))
  have hS : ∀ a ∈ S, a < 2 ^ (6 * m) := fun a ha => Finset.mem_range.1 (Finset.mem_filter.1 ha).1
  have hgrow : ∀ a ∈ S, g ^ 6 * wt (6 * m) a ≤
      ∑ j ∈ (Finset.range 64).filter (fun j =>
          Good (6 * (m + 1)) (64 * a + j) ∧ Count.Alive (tailBadF F) (6 * (m + 1)) (64 * a + j)),
        wt (6 * (m + 1)) (64 * a + j) +
      ∑ j ∈ (Finset.range 64).filter (fun j =>
          Good (6 * (m + 1)) (64 * a + j) ∧
            ¬ Count.Alive (tailBadF F) (6 * (m + 1)) (64 * a + j)),
        wt (6 * (m + 1)) (64 * a + j) := by
    intro a ha
    have := hgrowth _ _ (Finset.mem_filter.1 ha).2.1
    rw [show 6 * m + 6 = 6 * (m + 1) by ring] at this
    rw [← Finset.sum_union]
    · convert this using 2
      ext j; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    · exact Finset.disjoint_filter.2 fun j _ h1 h2 => h2.2 h1.2
  calc g ^ 6 * ∑ a ∈ S, wt (6 * m) a
      = ∑ a ∈ S, g ^ 6 * wt (6 * m) a := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum hgrow
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := by
      gcongr
      have := sum_children_le hS
        (fun a j => Good (6 * (m + 1)) (64 * a + j) ∧
          Count.Alive (tailBadF F) (6 * (m + 1)) (64 * a + j))
        (survivesF F Good (6 * (m + 1))) (fun a _ j _ h => h) (wt (6 * (m + 1))) (hnn _)
      rwa [show 6 * m + 6 = 6 * (m + 1) by ring] at this

open Classical in
theorem massF_zero (hc : WeightedCore449F F g wt Good) : massF F wt Good 0 = 1 := by
  obtain ⟨-, hg0, hw0, -, -⟩ := hc
  unfold massF
  have : survivesF F Good 0 0 := ⟨hg0, rfl⟩
  rw [show 6 * 0 = 0 from rfl, pow_zero, Finset.range_one, Finset.filter_singleton,
    if_pos this, Finset.sum_singleton, hw0]

theorem massF_pos (hc : WeightedCore449F F g wt Good) (h : TailChargeBudget449F F g wt Good) :
    ∀ m, 0 < massF F wt Good m := by
  obtain ⟨γ, hγ, c, hc0, hloss, hbud⟩ := h
  have hγ0 : 0 < γ := by linarith
  have key : ∀ m, 0 < massF F wt Good m ∧
      ∀ l ≤ m, γ ^ l * massF F wt Good (m - l) ≤ massF F wt Good m := by
    intro m
    induction m with
    | zero => exact ⟨by rw [massF_zero hc]; norm_num, fun l hl => by
        obtain rfl : l = 0 := by omega
        simp⟩
    | succ m ih =>
      obtain ⟨hpos, hdec⟩ := ih
      have hL : lossF F wt Good m ≤ (g ^ 6 - γ) * massF F wt Good m := by
        refine (hloss m).trans ?_
        calc ∑ l ∈ Finset.range (m + 1), c l * massF F wt Good (m - l)
            ≤ ∑ l ∈ Finset.range (m + 1), c l / γ ^ l * massF F wt Good m := by
              refine Finset.sum_le_sum fun l hl => ?_
              have h1 := hdec l (by simpa [Nat.lt_succ_iff] using hl)
              have hgl : 0 < γ ^ l := pow_pos hγ0 l
              rw [div_mul_eq_mul_div, le_div_iff₀ hgl]
              have := mul_le_mul_of_nonneg_left h1 (hc0 l)
              linarith
          _ = (∑ l ∈ Finset.range (m + 1), c l / γ ^ l) * massF F wt Good m :=
              (Finset.sum_mul _ _ _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right (hbud m) hpos.le
      have hrec := recurrenceF hc m
      have hnext : γ * massF F wt Good m ≤ massF F wt Good (m + 1) := by nlinarith
      refine ⟨lt_of_lt_of_le (mul_pos hγ0 hpos) hnext, fun l hl => ?_⟩
      rcases l with _ | l
      · simp
      · have := hdec l (by omega)
        rw [show m + 1 - (l + 1) = m - l by omega, pow_succ]
        calc γ ^ l * γ * massF F wt Good (m - l) = γ * (γ ^ l * massF F wt Good (m - l)) := by
              ring
          _ ≤ γ * massF F wt Good m := mul_le_mul_of_nonneg_left this hγ0.le
          _ ≤ _ := hnext
  exact fun m => (key m).1

/-- The combined pruning: core windows over `{2,3} ∪ F` or a fold-tail window. -/
def allBadF (F : Finset ℕ) (k a : ℕ) : Prop := coreBadF F k a ∨ tailBadF F k a

open Classical in
theorem exists_limitF (hc : WeightedCore449F F g wt Good)
    (h : TailChargeBudget449F F g wt Good) :
    ∃ ξ : ℝ, ∀ k, ∃ a, Count.Alive (allBadF F) k a ∧ ξ ∈ Count.cell k a := by
  refine Count.exists_mem_cells (allBadF F) fun k => ?_
  have hm := massF_pos hc h k
  unfold massF at hm
  obtain ⟨a, ha, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm.ne'
  obtain ⟨-, hg, hal⟩ := Finset.mem_filter.1 ha
  have ha' : Count.Alive (allBadF F) (6 * k) a := alive_or (hc.2.2.2.1 _ _ hg) hal
  have := Count.alive_anc (allBadF F) (k := k) (5 * k) (by rwa [show k + 5 * k = 6 * k by ring])
  exact Finset.card_pos.2 ⟨_, (Count.mem_aliveSet (allBadF F)).2 this⟩

/-- **Weak avoidance at 449/100** for every non-perfect-power base. -/
theorem weak_avoidF {ξ : ℝ} (hξ : ∀ k, ∃ a, Count.Alive (allBadF F) k a ∧ ξ ∈ Count.cell k a)
    {b : ℕ} (hb : 2 ≤ b) (hpp : ¬ IsPerfPow b) (n : ℕ) :
    (b : ℝ) ^ (-(449 / 100 : ℝ)) ≤ dnear ((b : ℝ) ^ n * ξ) := by
  by_contra hlt
  push Not at hlt
  set r := (b : ℝ) ^ (-(449 / 100 : ℝ))
  set x := (b : ℝ) ^ n * ξ
  have hbn : (0 : ℝ) < (b : ℝ) ^ n := pow_pos (by exact_mod_cast (by omega : 0 < b)) n
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
  have hwin : Count.cell k a ⊆ Coherent.window b n A.toNat := by
    unfold Coherent.window
    rw [show ((A.toNat : ℕ) : ℝ) = (A : ℝ) by exact_mod_cast Int.toNat_of_nonneg hA0]
    exact hsub
  have hbad : allBadF F k a := by
    rcases (show b = 2 ∨ b = 3 ∨ b = 4 ∨ 5 ≤ b by omega) with rfl | rfl | rfl | h5
    · exact Or.inl ⟨2, Or.inl rfl, n, A.toNat, hwin⟩
    · exact Or.inl ⟨3, Or.inr (Or.inl rfl), n, A.toNat, hwin⟩
    · exact absurd ⟨2, 2, le_rfl, by norm_num⟩ hpp
    · by_cases hF : b ∈ F
      · exact Or.inl ⟨b, Or.inr (Or.inr hF), n, A.toNat, hwin⟩
      · exact Or.inr ⟨b, h5, hpp, hF, n, A.toNat, hwin⟩
  exact ha.2 hbad

end Wiring

/-- **Gate 6, wiring.**  The gate-5 wiring with the core's facts taken from `WeightedCore449F`. -/
theorem tailBudgetSuffices449F : TailBudgetSuffices449F := by
  intro F g wt Good hc h
  obtain ⟨ξ, hξ⟩ := exists_limitF hc h
  have hadm : ∀ c : ℝ, 449 / 100 < c → Admissible c := by
    intro c hc
    refine (admissible_iff_nonPerfectPow (by linarith)).2 ⟨ξ, fun b hb hpp n => ?_⟩
    refine lt_of_lt_of_le ?_ (weak_avoidF hξ hb hpp n)
    have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
    exact Real.rpow_lt_rpow_of_exponent_lt hb1 (by linarith)
  exact le_of_forall_gt_imp_ge_of_dense fun c hc => csInf_le bddBelow_admissible (hadm c hc)

/-- **Gate 6, route.**  The exact `{2,3,5}` core and its tail budget at `g = 9/5`.
Screen: core growth 1.831 sampled, tail gap about 0.82 (module docstring). -/
theorem foldRoute449 : ∃ (wt : ℕ → ℕ → ℚ) (Good : ℕ → ℕ → Prop),
    WeightedCore449F F5 (9 / 5) wt Good ∧ TailChargeBudget449F F5 (9 / 5) wt Good := by
  sorry

/-- The headline by the gate-6 route. -/
theorem cStar_le_449_fold : cStar ≤ 449 / 100 := by
  obtain ⟨wt, Good, hc, ht⟩ := foldRoute449
  exact tailBudgetSuffices449F F5 (9 / 5) wt Good hc ht

end NormalNumbers.UniformBadThreshold.Fold
