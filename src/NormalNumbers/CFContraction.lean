/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFDefs

/-!
# W3 analytic core — one-step Lipschitz contraction of the tail-parameter chain

The crux kernel of `cylinder_mixing` (W3 route step 2), reduced to pure real
analysis, no measure theory.  Extending a cylinder word `w` by a digit
`k ≥ 1` sends the tail parameter `t = qₙ₋₁/qₙ` to `1/(k+t)` with relative
volume `|I_{w·k}|/|I_w| = (1+t)/((k+t)(k+1+t))`.  The induced averaging
operator on functions of `t` is

  `(P φ)(t) = Σ_{k≥1} (1+t)/((k+t)(k+1+t)) · φ(1/(k+t))`.

**Main result** (`stepOp_lipschitz`): if `φ` is `L`-Lipschitz on `[0,1]`
then `P φ` is `(9/10)·L`-Lipschitz on `[0,1]`.  Consequently `Pᵏ φ` is
`(9/10)ᵏL`-Lipschitz — the geometric mixing rate, with no coupling, no
Wasserstein, no Birkhoff cones.  Proof: split the difference into a
same-digit part (bounded by `S₁ ≤ 1/2 + 1/9`) and an Abel-summed
weight-difference part using the exact tail identity
`Σ_{k≥K}(w_t − w_{t'})(k) = (t−t')·(K−1)/((K+t)(K+t'))` (bounded by
`S₂ ≤ 1/4`), total `31/36 ≤ 9/10`.  Numerically the true contraction
factor is ≈ 0.41 (and the spectral rate is Wirsing's 0.3036); `9/10` is a
comfortable rigorous envelope.

Indexing: `k : ℕ` denotes the digit `k+1`, so sums run over all of `ℕ`.
-/

namespace NormalNumbers

open scoped BigOperators

/-- Digit weight of the tail-parameter chain: probability that the next
digit is `k+1` given tail parameter `t`; equals `|I_{w·(k+1)}|/|I_w|` when
`t = t(w)`. -/
noncomputable def stepWeight (t : ℝ) (k : ℕ) : ℝ :=
  (1 + t) / (((k : ℝ) + 1 + t) * ((k : ℝ) + 2 + t))

/-- Image of the tail parameter `t` after appending digit `k+1`:
`t ↦ 1/(k+1+t)` (Euler gluing `K(w ++ [a]) = a·K(w) + K(w⁻)`). -/
noncomputable def stepPt (t : ℝ) (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1 + t)

/-- The tail-parameter transfer operator: the conditional expectation of
`φ` of the next tail parameter. -/
noncomputable def stepOp (φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' k : ℕ, stepWeight t k * φ (stepPt t k)

/-! ## Basics -/

lemma stepWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : 0 ≤ stepWeight t k := by
  unfold stepWeight; positivity

lemma stepPt_mem_Icc {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    stepPt t k ∈ Set.Icc (0 : ℝ) 1 := by
  unfold stepPt
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith

/-- The telescoping form of the weight:
`w_t(k) = (1+t)/(k+1+t) − (1+t)/(k+2+t)`. -/
lemma stepWeight_eq_sub {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    stepWeight t k = (1 + t) / ((k : ℝ) + 1 + t) - (1 + t) / ((k : ℝ) + 2 + t) := by
  have h1 : ((k : ℝ) + 1 + t) ≠ 0 := by positivity
  have h2 : ((k : ℝ) + 2 + t) ≠ 0 := by positivity
  rw [stepWeight, div_sub_div _ _ h1 h2]
  congr 1
  ring

/-- The weights sum to `1`. -/
lemma hasSum_stepWeight {t : ℝ} (ht : 0 ≤ t) :
    HasSum (stepWeight t) 1 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (stepWeight_nonneg ht)]
  have hps : ∀ n : ℕ, ∑ k ∈ Finset.range n, stepWeight t k =
      (1 + t) / ((0 : ℝ) + 1 + t) - (1 + t) / ((n : ℝ) + 1 + t) := by
    intro n
    calc ∑ k ∈ Finset.range n, stepWeight t k
        = ∑ k ∈ Finset.range n, ((1 + t) / ((k : ℝ) + 1 + t) -
            (1 + t) / (((k + 1 : ℕ) : ℝ) + 1 + t)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [stepWeight_eq_sub ht k]
          push_cast
          ring_nf
      _ = (1 + t) / (((0 : ℕ) : ℝ) + 1 + t) - (1 + t) / ((n : ℝ) + 1 + t) :=
          Finset.sum_range_sub' (fun k : ℕ => (1 + t) / ((k : ℝ) + 1 + t)) n
      _ = (1 + t) / ((0 : ℝ) + 1 + t) - (1 + t) / ((n : ℝ) + 1 + t) := by
          norm_num
  simp only [hps]
  have h0 : (1 + t) / ((0 : ℝ) + 1 + t) = 1 := by
    rw [show (0 : ℝ) + 1 + t = 1 + t by ring]
    exact div_self (by positivity)
  rw [h0]
  have : Filter.Tendsto (fun n : ℕ => (1 + t) / ((n : ℝ) + 1 + t))
      Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.div_atTop tendsto_const_nhds
    exact Filter.tendsto_atTop_add_const_right _ (1 + t)
      (tendsto_natCast_atTop_atTop) |>.congr (fun n => by ring)
  have hlim : Filter.Tendsto (fun n : ℕ => 1 - (1 + t) / ((n : ℝ) + 1 + t))
      Filter.atTop (nhds (1 - 0)) := Filter.Tendsto.const_sub _ this
  simpa using hlim

lemma summable_stepWeight {t : ℝ} (ht : 0 ≤ t) : Summable (stepWeight t) :=
  (hasSum_stepWeight ht).summable

lemma tsum_stepWeight {t : ℝ} (ht : 0 ≤ t) : ∑' k, stepWeight t k = 1 :=
  (hasSum_stepWeight ht).tsum_eq

/-- Weighted sums of bounded-on-`[0,1]` integrands are summable. -/
lemma summable_stepWeight_mul {t : ℝ} (ht : 0 ≤ t) {φ : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x ∈ Set.Icc (0 : ℝ) 1, |φ x| ≤ M) :
    Summable (fun k => stepWeight t k * φ (stepPt t k)) := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _)
    (fun k => ?_) ((summable_stepWeight ht).mul_right M)
  rw [abs_mul, abs_of_nonneg (stepWeight_nonneg ht k)]
  exact mul_le_mul_of_nonneg_left (hM _ (stepPt_mem_Icc ht k))
    (stepWeight_nonneg ht k)

/-- `stepOp` fixes constants. -/
lemma stepOp_const {t : ℝ} (ht : 0 ≤ t) (c : ℝ) :
    stepOp (fun _ => c) t = c := by
  unfold stepOp
  rw [tsum_mul_right, tsum_stepWeight ht, one_mul]

/-! ## Telescoping majorant

`Σ_{k≥0} 1/((k+a)(k+a+1)(k+a+2)) = (1/2)/(a(a+1))` — the single telescope
serving every tail bound below (used at `a = 2`). -/

lemma hasSum_inv_triple {a : ℝ} (ha : 1 ≤ a) :
    HasSum (fun k : ℕ => 1 / (((k : ℝ) + a) * ((k : ℝ) + a + 1) * ((k : ℝ) + a + 2)))
      ((1 / 2) / (a * (a + 1))) := by
  have hk : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + a := fun k => by
    have := Nat.cast_nonneg (α := ℝ) k; linarith
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by
    have h1 := hk k; positivity)]
  have hps : ∀ n : ℕ,
      ∑ k ∈ Finset.range n,
        1 / (((k : ℝ) + a) * ((k : ℝ) + a + 1) * ((k : ℝ) + a + 2)) =
      (1 / 2) / (a * (a + 1)) -
        (1 / 2) / (((n : ℝ) + a) * ((n : ℝ) + a + 1)) := by
    intro n
    calc ∑ k ∈ Finset.range n,
          1 / (((k : ℝ) + a) * ((k : ℝ) + a + 1) * ((k : ℝ) + a + 2))
        = ∑ k ∈ Finset.range n,
            ((1 / 2) / (((k : ℝ) + a) * ((k : ℝ) + a + 1)) -
              (1 / 2) / ((((k + 1 : ℕ) : ℝ) + a) * (((k + 1 : ℕ) : ℝ) + a + 1))) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have h1 : ((k : ℝ) + a) ≠ 0 := ne_of_gt (hk k)
          have h2 : ((k : ℝ) + a + 1) ≠ 0 := ne_of_gt (by have := hk k; linarith)
          have h3 : ((k : ℝ) + a + 2) ≠ 0 := ne_of_gt (by have := hk k; linarith)
          push_cast
          field_simp
          ring
      _ = (1 / 2) / ((((0 : ℕ) : ℝ) + a) * (((0 : ℕ) : ℝ) + a + 1)) -
            (1 / 2) / (((n : ℝ) + a) * ((n : ℝ) + a + 1)) :=
          Finset.sum_range_sub'
            (fun k : ℕ => (1 / 2) / (((k : ℝ) + a) * ((k : ℝ) + a + 1))) n
      _ = (1 / 2) / (a * (a + 1)) -
            (1 / 2) / (((n : ℝ) + a) * ((n : ℝ) + a + 1)) := by norm_num
  simp only [hps]
  have hlim0 : Filter.Tendsto
      (fun n : ℕ => (1 / 2) / (((n : ℝ) + a) * ((n : ℝ) + a + 1)))
      Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.div_atTop tendsto_const_nhds
    have h := tendsto_natCast_atTop_atTop (R := ℝ)
    exact (Filter.tendsto_atTop_add_const_right _ a h).atTop_mul_atTop₀
      (Filter.tendsto_atTop_add_const_right _ 1
        (Filter.tendsto_atTop_add_const_right _ a h))
  have hlim := Filter.Tendsto.const_sub ((1 / 2) / (a * (a + 1))) hlim0
  simpa using hlim

/-- Comparison against `C/(k+1)²`: the workhorse summability test. -/
private lemma summable_sq_bound {f : ℕ → ℝ} {C : ℝ}
    (h : ∀ k, |f k| ≤ C / ((k : ℝ) + 1) ^ 2) : Summable f := by
  apply Summable.of_abs
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) h
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).mpr hbase
  have : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    apply hshift.congr
    intro k
    push_cast
    ring
  simpa [div_eq_mul_inv, mul_comm] using this.mul_left C

/-! ## Elementary bounds on weights and points -/

lemma stepWeight_le {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (k : ℕ) :
    stepWeight t k ≤ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  obtain ⟨h0, h1⟩ := ht
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [stepWeight, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hk h0, mul_nonneg (mul_nonneg hk hk) h0,
    mul_nonneg (mul_nonneg hk h0) h0]

lemma stepPt_sub {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (k : ℕ) :
    stepPt t k - stepPt t' k =
      (t' - t) / ((((k : ℝ) + 1 + t)) * ((k : ℝ) + 1 + t')) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [stepPt, stepPt,
    div_sub_div _ _ (ne_of_gt (by positivity)) (ne_of_gt (by positivity))]
  congr 1
  ring

lemma abs_stepPt_sub_le {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (k : ℕ) :
    |stepPt t k - stepPt t' k| ≤ |t - t'| / (((k : ℝ) + 1) * ((k : ℝ) + 1)) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hden : (0 : ℝ) < ((k : ℝ) + 1 + t) * ((k : ℝ) + 1 + t') := by positivity
  rw [stepPt_sub ht ht', abs_div, abs_sub_comm, abs_of_pos hden]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
  have h1 : ((k : ℝ) + 1) ≤ (k : ℝ) + 1 + t := by linarith
  have h2 : ((k : ℝ) + 1) ≤ (k : ℝ) + 1 + t' := by linarith
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- Consecutive-point gap: `z_k − z_{k+1} = 1/((k+1+t)(k+2+t))`. -/
lemma stepPt_sub_succ {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    stepPt t k - stepPt t (k + 1) =
      1 / ((((k : ℝ) + 1 + t)) * ((k : ℝ) + 2 + t)) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h2 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 + t := by push_cast; linarith
  rw [stepPt, stepPt, div_sub_div _ _ (ne_of_gt (by positivity)) (ne_of_gt h2)]
  push_cast
  rw [show ((k : ℝ) + 1 + 1 + t) = (k : ℝ) + 2 + t by ring]
  congr 1
  ring

/-! ## The Abel tail function -/

/-- Tail of the weight difference: `gTail t t' k = Σ_{j≥k}(w_t − w_{t'})(j)`
in closed form.  `gTail 0 = 0` and
`w_t(k) − w_{t'}(k) = gTail k − gTail (k+1)` — the discrete integration by
parts powering the contraction bound. -/
private noncomputable def gTail (t t' : ℝ) (k : ℕ) : ℝ :=
  (1 + t) / ((k : ℝ) + 1 + t) - (1 + t') / ((k : ℝ) + 1 + t')

private lemma gTail_zero {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    gTail t t' 0 = 0 := by
  rw [gTail]
  push_cast
  rw [show ((0 : ℝ) + 1 + t) = 1 + t by ring,
    show ((0 : ℝ) + 1 + t') = 1 + t' by ring,
    div_self (by positivity), div_self (by positivity), sub_self]

private lemma stepWeight_sub_eq {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (k : ℕ) :
    stepWeight t k - stepWeight t' k = gTail t t' k - gTail t t' (k + 1) := by
  rw [stepWeight_eq_sub ht, stepWeight_eq_sub ht', gTail, gTail]
  push_cast
  ring_nf

private lemma gTail_eq {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (k : ℕ) :
    gTail t t' k =
      (t - t') * (k : ℝ) / (((k : ℝ) + 1 + t) * ((k : ℝ) + 1 + t')) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [gTail, div_sub_div _ _ (ne_of_gt (by positivity)) (ne_of_gt (by positivity))]
  congr 1
  ring

private lemma abs_gTail_le {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') (k : ℕ) :
    |gTail t t' k| ≤
      |t - t'| * (k : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 1)) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hden : (0 : ℝ) < ((k : ℝ) + 1 + t) * ((k : ℝ) + 1 + t') := by positivity
  rw [gTail_eq ht ht', abs_div, abs_mul, abs_of_nonneg hk, abs_of_pos hden]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have h1 : ((k : ℝ) + 1) ≤ (k : ℝ) + 1 + t := by linarith
  have h2 : ((k : ℝ) + 1) ≤ (k : ℝ) + 1 + t' := by linarith
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-! ## The main contraction -/

set_option maxHeartbeats 1600000 in
/-- **One-step Lipschitz contraction** (the W3 analytic crux).  If `φ` is
`L`-Lipschitz on `[0,1]`, then `stepOp φ` is `(9/10)·L`-Lipschitz on
`[0,1]`.  Hence `Pᵏφ` is `(9/10)ᵏ·L`-Lipschitz: the geometric
Gauss–Kuzmin–Lévy mixing rate.

Proof: with `ψ = φ − φ(0)` (which drops out of `stepOp` differences since
the weights sum to `1`), split
`Σ w_t ψ(z) − Σ w_{t'} ψ(z') = Σ A_k + Σ B_k` with
`A_k = w_t(k)(ψ(z_k) − ψ(z'_k))` and `B_k = (w_t − w_{t'})(k)·ψ(z'_k)`.
The `A`-series is bounded termwise, peeling two leading terms
(`≤ LΔ(1/2 + 1/12 + 1/18)`); the `B`-series is Abel-resummed through
`gTail` into `Σ gTail(k+1)·(ψ(z'_{k+1}) − ψ(z'_k))` and bounded termwise,
peeling one (`≤ LΔ(1/8 + 1/12)`).  Total `61/72 ≤ 9/10`. -/
theorem stepOp_lipschitz {φ : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hφ : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |φ x - φ y| ≤ L * |x - y|)
    {t t' : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (ht' : t' ∈ Set.Icc (0 : ℝ) 1) :
    |stepOp φ t - stepOp φ t'| ≤ 9 / 10 * L * |t - t'| := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨ht0', ht1'⟩ := ht'
  set Δ : ℝ := |t - t'| with hΔ
  have hΔ0 : 0 ≤ Δ := abs_nonneg _
  set ψ : ℝ → ℝ := fun x => φ x - φ 0 with hψdef
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, by norm_num⟩
  -- pointwise bounds for ψ
  have hψ_le : ∀ x ∈ Set.Icc (0 : ℝ) 1, |ψ x| ≤ L * x := by
    intro x hx
    have h := hφ x hx 0 hmem0
    rw [sub_zero, abs_of_nonneg hx.1] at h
    exact h
  have hψ_bd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |ψ x| ≤ L := fun x hx =>
    (hψ_le x hx).trans (by nlinarith [hx.2])
  have hψ_lip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |ψ x - ψ y| ≤ L * |x - y| := by
    intro x hx y hy
    have : ψ x - ψ y = φ x - φ y := by rw [hψdef]; ring
    rw [this]
    exact hφ x hx y hy
  -- reduction to the centered integrand
  have hred : ∀ s : ℝ, 0 ≤ s →
      stepOp φ s = (∑' k, stepWeight s k * ψ (stepPt s k)) + φ 0 := by
    intro s hs0
    have hs1' : Summable (fun k => stepWeight s k * ψ (stepPt s k)) :=
      summable_stepWeight_mul hs0 hψ_bd
    have hs2' : Summable (fun k => stepWeight s k * φ 0) :=
      (summable_stepWeight hs0).mul_right (φ 0)
    have hexp : stepOp φ s = ∑' k, (stepWeight s k * ψ (stepPt s k)
        + stepWeight s k * φ 0) := by
      unfold stepOp
      apply tsum_congr
      intro k
      rw [hψdef]
      ring
    rw [hexp, hs1'.tsum_add hs2', tsum_mul_right, tsum_stepWeight hs0, one_mul]
  -- the two series
  set A : ℕ → ℝ := fun k => stepWeight t k * (ψ (stepPt t k) - ψ (stepPt t' k))
    with hAdef
  set B : ℕ → ℝ := fun k => (stepWeight t k - stepWeight t' k) * ψ (stepPt t' k)
    with hBdef
  have hSF : Summable (fun k => stepWeight t k * ψ (stepPt t k)) :=
    summable_stepWeight_mul ht0 hψ_bd
  have hSF' : Summable (fun k => stepWeight t' k * ψ (stepPt t' k)) :=
    summable_stepWeight_mul ht0' hψ_bd
  have hSmix : Summable (fun k => stepWeight t k * ψ (stepPt t' k)) := by
    apply Summable.of_abs
    apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
      ((summable_stepWeight ht0).mul_right L)
    rw [abs_mul, abs_of_nonneg (stepWeight_nonneg ht0 k)]
    exact mul_le_mul_of_nonneg_left (hψ_bd _ (stepPt_mem_Icc ht0' k))
      (stepWeight_nonneg ht0 k)
  have hSA : Summable A := by
    have hA' : A = fun k => stepWeight t k * ψ (stepPt t k)
        - stepWeight t k * ψ (stepPt t' k) := by
      funext k; rw [hAdef]; ring
    rw [hA']
    exact hSF.sub hSmix
  have hSB : Summable B := by
    have hB' : B = fun k => stepWeight t k * ψ (stepPt t' k)
        - stepWeight t' k * ψ (stepPt t' k) := by
      funext k; rw [hBdef]; ring
    rw [hB']
    exact hSmix.sub hSF'
  -- the difference is ΣA + ΣB
  have hsplit : stepOp φ t - stepOp φ t' = (∑' k, A k) + (∑' k, B k) := by
    rw [hred t ht0, hred t' ht0']
    have h1 : (∑' k, stepWeight t k * ψ (stepPt t k)) + φ 0
        - ((∑' k, stepWeight t' k * ψ (stepPt t' k)) + φ 0)
        = (∑' k, stepWeight t k * ψ (stepPt t k))
          - ∑' k, stepWeight t' k * ψ (stepPt t' k) := by ring
    rw [h1, ← hSF.tsum_sub hSF', ← hSA.tsum_add hSB]
    apply tsum_congr
    intro k
    rw [hAdef, hBdef]
    ring
  -- ### termwise bound for A
  have hA_term : ∀ k : ℕ, |A k| ≤
      stepWeight t k * (L * (Δ / (((k : ℝ) + 1) * ((k : ℝ) + 1)))) := by
    intro k
    rw [hAdef]
    rw [abs_mul, abs_of_nonneg (stepWeight_nonneg ht0 k)]
    apply mul_le_mul_of_nonneg_left ?_ (stepWeight_nonneg ht0 k)
    calc |ψ (stepPt t k) - ψ (stepPt t' k)|
        ≤ L * |stepPt t k - stepPt t' k| :=
          hψ_lip _ (stepPt_mem_Icc ht0 k) _ (stepPt_mem_Icc ht0' k)
      _ ≤ L * (Δ / (((k : ℝ) + 1) * ((k : ℝ) + 1))) := by
          apply mul_le_mul_of_nonneg_left ?_ hL
          rw [hΔ]
          exact abs_stepPt_sub_le ht0 ht0' k
  -- |A 0| ≤ LΔ/2, |A 1| ≤ LΔ/12, |A (k+2)| ≤ (2/3)LΔ/((k+2)(k+3)(k+4))
  have hA0 : |A 0| ≤ L * Δ * (1 / 2) := by
    refine (hA_term 0).trans ?_
    have hw : stepWeight t 0 ≤ 1 / 2 := by
      rw [stepWeight]
      push_cast
      rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
      nlinarith
    calc stepWeight t 0 * (L * (Δ / ((((0 : ℕ) : ℝ) + 1) * (((0 : ℕ) : ℝ) + 1))))
        = stepWeight t 0 * (L * Δ) := by push_cast; ring_nf
      _ ≤ 1 / 2 * (L * Δ) := by
          apply mul_le_mul_of_nonneg_right hw (by positivity)
      _ = L * Δ * (1 / 2) := by ring
  have hA1 : |A 1| ≤ L * Δ * (1 / 12) := by
    refine (hA_term 1).trans ?_
    have hw : stepWeight t 1 ≤ 1 / 3 := by
      rw [stepWeight]
      push_cast
      rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
      nlinarith
    calc stepWeight t 1 * (L * (Δ / ((((1 : ℕ) : ℝ) + 1) * (((1 : ℕ) : ℝ) + 1))))
        = stepWeight t 1 * (L * Δ * (1 / 4)) := by push_cast; ring_nf
      _ ≤ 1 / 3 * (L * Δ * (1 / 4)) := by
          apply mul_le_mul_of_nonneg_right hw (by positivity)
      _ = L * Δ * (1 / 12) := by ring
  have hAtail : ∀ k : ℕ, |A (k + 2)| ≤
      (2 / 3) * (L * Δ) * (1 / (((k : ℝ) + 2) * ((k : ℝ) + 2 + 1) * ((k : ℝ) + 2 + 2))) := by
    intro k
    refine (hA_term (k + 2)).trans ?_
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hw : stepWeight t (k + 2) ≤ 2 / (((k : ℝ) + 3) * ((k : ℝ) + 4)) := by
      have := stepWeight_le ⟨ht0, ht1⟩ (k + 2)
      calc stepWeight t (k + 2)
          ≤ 2 / ((((k + 2 : ℕ) : ℝ) + 1) * (((k + 2 : ℕ) : ℝ) + 2)) := this
        _ = 2 / (((k : ℝ) + 3) * ((k : ℝ) + 4)) := by push_cast; ring_nf
    have hpt : Δ / ((((k + 2 : ℕ) : ℝ) + 1) * (((k + 2 : ℕ) : ℝ) + 1))
        = Δ / (((k : ℝ) + 3) * ((k : ℝ) + 3)) := by push_cast; ring_nf
    calc stepWeight t (k + 2) *
          (L * (Δ / ((((k + 2 : ℕ) : ℝ) + 1) * (((k + 2 : ℕ) : ℝ) + 1))))
        ≤ (2 / (((k : ℝ) + 3) * ((k : ℝ) + 4))) *
            (L * (Δ / (((k : ℝ) + 3) * ((k : ℝ) + 3)))) := by
          rw [hpt]
          apply mul_le_mul_of_nonneg_right hw (by positivity)
      _ = L * Δ * (2 / ((((k : ℝ) + 3) * ((k : ℝ) + 3) * ((k : ℝ) + 3)) * ((k : ℝ) + 4))) := by
          field_simp
      _ ≤ (2 / 3) * (L * Δ) *
            (1 / (((k : ℝ) + 2) * ((k : ℝ) + 2 + 1) * ((k : ℝ) + 2 + 2))) := by
          have hfrac : 2 / ((((k : ℝ) + 3) * ((k : ℝ) + 3) * ((k : ℝ) + 3)) * ((k : ℝ) + 4)) ≤
              (2 / 3) * (1 / (((k : ℝ) + 2) * ((k : ℝ) + 2 + 1) * ((k : ℝ) + 2 + 2))) := by
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [mul_nonneg hk hk, mul_nonneg (mul_nonneg hk hk) hk,
              mul_nonneg (mul_nonneg (mul_nonneg hk hk) hk) hk]
          calc L * Δ * (2 / ((((k : ℝ) + 3) * ((k : ℝ) + 3) * ((k : ℝ) + 3)) * ((k : ℝ) + 4)))
              ≤ L * Δ * ((2 / 3) *
                  (1 / (((k : ℝ) + 2) * ((k : ℝ) + 2 + 1) * ((k : ℝ) + 2 + 2)))) :=
                mul_le_mul_of_nonneg_left hfrac (by positivity)
            _ = (2 / 3) * (L * Δ) *
                  (1 / (((k : ℝ) + 2) * ((k : ℝ) + 2 + 1) * ((k : ℝ) + 2 + 2))) := by ring
  -- assemble ΣA
  have habsA : Summable (fun k => |A k|) := hSA.abs
  have habsA1 : Summable (fun k => |A (k + 1)|) :=
    (summable_nat_add_iff 1).mpr habsA
  have habsA2 : Summable (fun k => |A (k + 2)|) :=
    (summable_nat_add_iff 2).mpr habsA
  have hAmajor : Summable (fun k : ℕ =>
      (2 / 3) * (L * Δ) * (1 / (((k : ℝ) + 2) * ((k : ℝ) + 2 + 1) * ((k : ℝ) + 2 + 2)))) :=
    ((hasSum_inv_triple (by norm_num : (1 : ℝ) ≤ 2)).summable.mul_left _)
  have hAtail_sum : ∑' k, |A (k + 2)| ≤ L * Δ * (1 / 18) := by
    calc ∑' k, |A (k + 2)|
        ≤ ∑' k : ℕ, (2 / 3) * (L * Δ) *
            (1 / (((k : ℝ) + 2) * ((k : ℝ) + 2 + 1) * ((k : ℝ) + 2 + 2))) :=
          habsA2.tsum_le_tsum hAtail hAmajor
      _ = (2 / 3) * (L * Δ) * ((1 / 2) / (2 * (2 + 1))) := by
          rw [((hasSum_inv_triple (by norm_num : (1 : ℝ) ≤ 2)).mul_left
            ((2 / 3) * (L * Δ))).tsum_eq]
      _ = L * Δ * (1 / 18) := by ring
  have hsumA : |∑' k, A k| ≤ L * Δ * (1 / 2 + 1 / 12 + 1 / 18) := by
    have h1 : |∑' k, A k| ≤ ∑' k, |A k| := by
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := A)
        (by simpa [Real.norm_eq_abs] using habsA)
    have h2 : ∑' k, |A k| = |A 0| + (|A 1| + ∑' k, |A (k + 2)|) := by
      rw [habsA.tsum_eq_zero_add]
      congr 1
      have := habsA1.tsum_eq_zero_add
      simpa using this
    calc |∑' k, A k| ≤ ∑' k, |A k| := h1
      _ = |A 0| + (|A 1| + ∑' k, |A (k + 2)|) := h2
      _ ≤ L * Δ * (1 / 2) + (L * Δ * (1 / 12) + L * Δ * (1 / 18)) := by
          gcongr
      _ = L * Δ * (1 / 2 + 1 / 12 + 1 / 18) := by ring
  -- ### Abel resummation for B
  set u : ℕ → ℝ := fun k => gTail t t' k * ψ (stepPt t' k) with hudef
  set v : ℕ → ℝ := fun k => gTail t t' (k + 1) * ψ (stepPt t' k) with hvdef
  have hu_bd : ∀ k, |u k| ≤ (L * Δ) / ((k : ℝ) + 1) ^ 2 := by
    intro k
    rw [hudef]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_mul]
    have hpt : stepPt t' k ≤ 1 / ((k : ℝ) + 1) := by
      rw [stepPt]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      linarith
    calc |gTail t t' k| * |ψ (stepPt t' k)|
        ≤ (Δ * (k : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 1))) * (L * (1 / ((k : ℝ) + 1))) := by
          apply mul_le_mul (abs_gTail_le ht0 ht0' k)
            ((hψ_le _ (stepPt_mem_Icc ht0' k)).trans
              (mul_le_mul_of_nonneg_left hpt hL)) (abs_nonneg _) (by positivity)
      _ ≤ (L * Δ) / ((k : ℝ) + 1) ^ 2 := by
          have hfrac : Δ * (k : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 1)) * (L * (1 / ((k : ℝ) + 1)))
              = (L * Δ) * ((k : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 1) * ((k : ℝ) + 1))) := by
            rw [mul_one_div, div_mul_div_comm, mul_div_assoc']
            congr 1 <;> ring
          rw [hfrac]
          have hxy : (k : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 1) * ((k : ℝ) + 1))
              ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [mul_nonneg hk hk, mul_nonneg (mul_nonneg hk hk) hk]
          calc (L * Δ) * ((k : ℝ) / (((k : ℝ) + 1) * ((k : ℝ) + 1) * ((k : ℝ) + 1)))
              ≤ (L * Δ) * (1 / ((k : ℝ) + 1) ^ 2) :=
                mul_le_mul_of_nonneg_left hxy (by positivity)
            _ = (L * Δ) / ((k : ℝ) + 1) ^ 2 := by rw [mul_one_div]
  have hv_bd : ∀ k, |v k| ≤ (L * Δ) / ((k : ℝ) + 1) ^ 2 := by
    intro k
    rw [hvdef]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_mul]
    have hgt : |gTail t t' (k + 1)| ≤
        Δ * ((k : ℝ) + 1) / (((k : ℝ) + 2) * ((k : ℝ) + 2)) := by
      refine (abs_gTail_le ht0 ht0' (k + 1)).trans_eq ?_
      rw [hΔ]
      push_cast
      ring_nf
    have hpt : stepPt t' k ≤ 1 / ((k : ℝ) + 1) := by
      rw [stepPt]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      linarith
    calc |gTail t t' (k + 1)| * |ψ (stepPt t' k)|
        ≤ (Δ * ((k : ℝ) + 1) / (((k : ℝ) + 2) * ((k : ℝ) + 2))) *
            (L * (1 / ((k : ℝ) + 1))) := by
          apply mul_le_mul hgt ((hψ_le _ (stepPt_mem_Icc ht0' k)).trans
            (mul_le_mul_of_nonneg_left hpt hL)) (abs_nonneg _) (by positivity)
      _ = (L * Δ) * (((k : ℝ) + 1) / (((k : ℝ) + 2) * ((k : ℝ) + 2) * ((k : ℝ) + 1))) := by
          field_simp
      _ ≤ (L * Δ) / ((k : ℝ) + 1) ^ 2 := by
          have hxy : ((k : ℝ) + 1) / (((k : ℝ) + 2) * ((k : ℝ) + 2) * ((k : ℝ) + 1))
              ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [mul_nonneg hk hk, mul_nonneg (mul_nonneg hk hk) hk]
          calc (L * Δ) * (((k : ℝ) + 1) / (((k : ℝ) + 2) * ((k : ℝ) + 2) * ((k : ℝ) + 1)))
              ≤ (L * Δ) * (1 / ((k : ℝ) + 1) ^ 2) :=
                mul_le_mul_of_nonneg_left hxy (by positivity)
            _ = (L * Δ) / ((k : ℝ) + 1) ^ 2 := by rw [mul_one_div]
  have hSu : Summable u := summable_sq_bound hu_bd
  have hSv : Summable v := summable_sq_bound hv_bd
  have hSu1 : Summable (fun k => u (k + 1)) := (summable_nat_add_iff 1).mpr hSu
  -- Σ'B = Σ' gTail(k+1)·(ψ(z'_{k+1}) − ψ(z'_k))
  set T : ℕ → ℝ := fun k =>
    gTail t t' (k + 1) * (ψ (stepPt t' (k + 1)) - ψ (stepPt t' k)) with hTdef
  have hBsum : (∑' k, B k) = ∑' k, T k := by
    have hBk : ∀ k, B k = u k - v k := by
      intro k
      simp only [hBdef, hudef, hvdef]
      rw [stepWeight_sub_eq ht0 ht0' k]
      ring
    have h1 : (∑' k, B k) = (∑' k, u k) - ∑' k, v k := by
      rw [show (fun k => B k) = fun k => u k - v k from funext hBk]
      exact hSu.tsum_sub hSv
    have h2 : (∑' k, u k) = ∑' k, u (k + 1) := by
      rw [hSu.tsum_eq_zero_add]
      have hu0 : u 0 = 0 := by
        simp only [hudef]
        rw [gTail_zero ht0 ht0', zero_mul]
      rw [hu0, zero_add]
    rw [h1, h2, ← hSu1.tsum_sub hSv]
    apply tsum_congr
    intro k
    simp only [hTdef, hudef, hvdef]
    ring
  -- termwise bound for T
  have hT_term : ∀ k : ℕ, |T k| ≤
      L * Δ * (1 / (((k : ℝ) + 2) * ((k : ℝ) + 2) * ((k : ℝ) + 2))) := by
    intro k
    simp only [hTdef]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [abs_mul]
    have hgt : |gTail t t' (k + 1)| ≤
        Δ * ((k : ℝ) + 1) / (((k : ℝ) + 2) * ((k : ℝ) + 2)) := by
      refine (abs_gTail_le ht0 ht0' (k + 1)).trans_eq ?_
      rw [hΔ]
      push_cast
      ring_nf
    have hgap : |ψ (stepPt t' (k + 1)) - ψ (stepPt t' k)| ≤
        L * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
      calc |ψ (stepPt t' (k + 1)) - ψ (stepPt t' k)|
          ≤ L * |stepPt t' (k + 1) - stepPt t' k| :=
            hψ_lip _ (stepPt_mem_Icc ht0' (k + 1)) _ (stepPt_mem_Icc ht0' k)
        _ ≤ L * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
            apply mul_le_mul_of_nonneg_left ?_ hL
            rw [abs_sub_comm, stepPt_sub_succ ht0' k,
              abs_of_pos (by positivity)]
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            have h1 : ((k : ℝ) + 1) ≤ (k : ℝ) + 1 + t' := by linarith
            have h2 : ((k : ℝ) + 2) ≤ (k : ℝ) + 2 + t' := by linarith
            exact mul_le_mul h1 h2 (by positivity) (by positivity)
    calc |gTail t t' (k + 1)| * |ψ (stepPt t' (k + 1)) - ψ (stepPt t' k)|
        ≤ (Δ * ((k : ℝ) + 1) / (((k : ℝ) + 2) * ((k : ℝ) + 2))) *
            (L * (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)))) := by
          apply mul_le_mul hgt hgap (abs_nonneg _) (by positivity)
      _ = L * Δ * (1 / (((k : ℝ) + 2) * ((k : ℝ) + 2) * ((k : ℝ) + 2))) := by
          field_simp
  -- assemble ΣB
  have hST : Summable T := by
    apply summable_sq_bound (C := L * Δ)
    intro k
    refine (hT_term k).trans ?_
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have habsT : Summable (fun k => |T k|) := hST.abs
  have habsT1 : Summable (fun k => |T (k + 1)|) :=
    (summable_nat_add_iff 1).mpr habsT
  have hT0 : |T 0| ≤ L * Δ * (1 / 8) := by
    refine (hT_term 0).trans ?_
    norm_num
  have hTtail : ∀ k : ℕ, |T (k + 1)| ≤
      L * Δ * (1 / (((k : ℝ) + 2) * ((k : ℝ) + 2 + 1) * ((k : ℝ) + 2 + 2))) := by
    intro k
    refine (hT_term (k + 1)).trans ?_
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hcast : (((k + 1 : ℕ) : ℝ) + 2) = (k : ℝ) + 3 := by push_cast; ring
    rw [hcast]
    apply mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have hTmajor : Summable (fun k : ℕ =>
      L * Δ * (1 / (((k : ℝ) + 2) * ((k : ℝ) + 2 + 1) * ((k : ℝ) + 2 + 2)))) :=
    ((hasSum_inv_triple (by norm_num : (1 : ℝ) ≤ 2)).summable.mul_left _)
  have hsumB : |∑' k, B k| ≤ L * Δ * (1 / 8 + 1 / 12) := by
    rw [hBsum]
    have h1 : |∑' k, T k| ≤ ∑' k, |T k| := by
      simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := T)
        (by simpa [Real.norm_eq_abs] using habsT)
    have h2 : ∑' k, |T k| = |T 0| + ∑' k, |T (k + 1)| := habsT.tsum_eq_zero_add
    have h3 : ∑' k, |T (k + 1)| ≤ L * Δ * (1 / 12) := by
      calc ∑' k, |T (k + 1)|
          ≤ ∑' k : ℕ, L * Δ *
              (1 / (((k : ℝ) + 2) * ((k : ℝ) + 2 + 1) * ((k : ℝ) + 2 + 2))) :=
            habsT1.tsum_le_tsum hTtail hTmajor
        _ = L * Δ * ((1 / 2) / (2 * (2 + 1))) := by
            rw [((hasSum_inv_triple (by norm_num : (1 : ℝ) ≤ 2)).mul_left
              (L * Δ)).tsum_eq]
        _ = L * Δ * (1 / 12) := by ring
    calc |∑' k, T k| ≤ ∑' k, |T k| := h1
      _ = |T 0| + ∑' k, |T (k + 1)| := h2
      _ ≤ L * Δ * (1 / 8) + L * Δ * (1 / 12) := by gcongr
      _ = L * Δ * (1 / 8 + 1 / 12) := by ring
  -- ### final assembly: 1/2 + 1/12 + 1/18 + 1/8 + 1/12 = 61/72 ≤ 9/10
  rw [hsplit]
  calc |(∑' k, A k) + ∑' k, B k| ≤ |∑' k, A k| + |∑' k, B k| := abs_add_le _ _
    _ ≤ L * Δ * (1 / 2 + 1 / 12 + 1 / 18) + L * Δ * (1 / 8 + 1 / 12) :=
        add_le_add hsumA hsumB
    _ = 61 / 72 * L * Δ := by ring
    _ ≤ 9 / 10 * L * Δ := by
        nlinarith [mul_nonneg hL hΔ0]

end NormalNumbers
