import NormalNumbers.TwoPointHonestChain

/-!
# The Cauchy–Schwarz step of the Kátai/BSZ inequality, in kernel

Laps 4–6 rest on a hand derivation: in the Kátai/BSZ argument the pair term enters as a SUM
against `L(w)²`, because the **diagonal** `p = q` of the inner square contributes `Σ_{p≤w} N/p`.
This file proves that step outright, abstractly, so the claim is machine-checked rather than
asserted.

`katai_cauchySchwarz`: for unimodular-bounded `u` (the role of `f(p)`), `g` (the role of `f(m)`)
and `C p m` (the role of `a(pm)`, truncated to `pm < N`),

    ‖Σ_{p ∈ A} u p · Σ_{m<N} g m · C p m‖²
      ≤ N · ( Σ_{p ∈ A} Σ_{m<N} ‖C p m‖²  +  Σ_{p ≠ q ∈ A} ‖Σ_{m<N} C p m conj(C q m)‖ ) .

The first bracketed term is the diagonal; with `C p m = a(pm)·1_{pm<N}` it is `Σ_{p≤w} N/p =
N·L(w)`, and the second is the pair sum.  Dividing by `N²L(w)²` gives exactly

    ‖E f·a‖²  ≲  1/L(w)  +  pairSum / L(w)² ,

which is `KataiQuantSharp`'s shape and NOT `KataiQuant`'s.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- The correlation matrix of the truncated family. -/
noncomputable def csGram (C : ℕ → ℕ → ℂ) (N p q : ℕ) : ℂ :=
  ∑ m ∈ Finset.range N, C p m * (starRingEnd ℂ) (C q m)

lemma csGram_self (C : ℕ → ℕ → ℂ) (N p : ℕ) :
    csGram C N p p = ((∑ m ∈ Finset.range N, ‖C p m‖ ^ 2 : ℝ) : ℂ) := by
  rw [csGram, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma norm_csGram_self (C : ℕ → ℕ → ℂ) (N p : ℕ) :
    ‖csGram C N p p‖ = ∑ m ∈ Finset.range N, ‖C p m‖ ^ 2 := by
  rw [csGram_self, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun m _ => by positivity)]

/-- Expanding the inner square: the `ℓ²` mass of the superposition is the Gram sum. -/
lemma sum_sq_superposition (A : Finset ℕ) (N : ℕ) (u : ℕ → ℂ) (C : ℕ → ℕ → ℂ) :
    ((∑ m ∈ Finset.range N, ‖∑ p ∈ A, u p * C p m‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ A, ∑ q ∈ A, (u p * (starRingEnd ℂ) (u q)) * csGram C N p q := by
  have hstep : ∀ m : ℕ, ((‖∑ p ∈ A, u p * C p m‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ A, ∑ q ∈ A, (u p * (starRingEnd ℂ) (u q)) * (C p m * (starRingEnd ℂ) (C q m)) := by
    intro m
    have h1 : ((‖∑ p ∈ A, u p * C p m‖ ^ 2 : ℝ) : ℂ)
        = (∑ p ∈ A, u p * C p m) * (starRingEnd ℂ) (∑ p ∈ A, u p * C p m) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h1, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul]; ring
  rw [Complex.ofReal_sum, Finset.sum_congr rfl fun m _ => hstep m]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [csGram, Finset.mul_sum]

/-- **The Cauchy–Schwarz step, with its true constants.** -/
theorem katai_cauchySchwarz (A : Finset ℕ) (N : ℕ) (u g : ℕ → ℂ) (C : ℕ → ℕ → ℂ)
    (hu : ∀ p, ‖u p‖ ≤ 1) (hg : ∀ m, ‖g m‖ ≤ 1) :
    ‖∑ p ∈ A, u p * ∑ m ∈ Finset.range N, g m * C p m‖ ^ 2
      ≤ (N : ℝ) * ((∑ p ∈ A, ∑ m ∈ Finset.range N, ‖C p m‖ ^ 2)
          + ∑ p ∈ A, ∑ q ∈ A, if p = q then 0 else ‖csGram C N p q‖) := by
  classical
  set h : ℕ → ℂ := fun m => ∑ p ∈ A, u p * C p m with hh
  -- interchange the order of summation
  have hX : ∑ p ∈ A, u p * ∑ m ∈ Finset.range N, g m * C p m
      = ∑ m ∈ Finset.range N, g m * h m := by
    rw [hh]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  -- step 1: bound by the `ℓ¹` mass
  have h1 : ‖∑ m ∈ Finset.range N, g m * h m‖ ≤ ∑ m ∈ Finset.range N, ‖h m‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_mul]
    nlinarith [hg m, norm_nonneg (h m), norm_nonneg (g m)]
  -- step 2: Cauchy–Schwarz `ℓ¹ → ℓ²`
  have h2 : (∑ m ∈ Finset.range N, ‖h m‖) ^ 2
      ≤ (N : ℝ) * ∑ m ∈ Finset.range N, ‖h m‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := fun m => ‖h m‖)
    simpa using this
  -- step 3: the `ℓ²` mass is the Gram sum, bounded by diagonal plus off-diagonal
  have h3 : (∑ m ∈ Finset.range N, ‖h m‖ ^ 2)
      ≤ (∑ p ∈ A, ∑ m ∈ Finset.range N, ‖C p m‖ ^ 2)
        + ∑ p ∈ A, ∑ q ∈ A, if p = q then 0 else ‖csGram C N p q‖ := by
    have hexp := sum_sq_superposition A N u C
    have hnorm : (∑ m ∈ Finset.range N, ‖h m‖ ^ 2)
        = ‖∑ p ∈ A, ∑ q ∈ A, (u p * (starRingEnd ℂ) (u q)) * csGram C N p q‖ := by
      rw [← hexp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun m _ => by positivity)]
    rw [hnorm]
    calc ‖∑ p ∈ A, ∑ q ∈ A, (u p * (starRingEnd ℂ) (u q)) * csGram C N p q‖
        ≤ ∑ p ∈ A, ∑ q ∈ A, ‖(u p * (starRingEnd ℂ) (u q)) * csGram C N p q‖ :=
          le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => norm_sum_le _ _)
      _ ≤ ∑ p ∈ A, ∑ q ∈ A, ‖csGram C N p q‖ := by
          refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
          rw [norm_mul, norm_mul, RCLike.norm_conj]
          calc ‖u p‖ * ‖u q‖ * ‖csGram C N p q‖
              ≤ 1 * 1 * ‖csGram C N p q‖ :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul (hu p) (hu q) (norm_nonneg _) zero_le_one)
                  (norm_nonneg _)
            _ = ‖csGram C N p q‖ := by ring
      _ = (∑ p ∈ A, ‖csGram C N p p‖)
            + ∑ p ∈ A, ∑ q ∈ A, if p = q then 0 else ‖csGram C N p q‖ := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun p hp => ?_
          have hsplit : ∀ q : ℕ, ‖csGram C N p q‖
              = (if p = q then ‖csGram C N p q‖ else 0)
                + (if p = q then 0 else ‖csGram C N p q‖) := by
            intro q; by_cases hpq : p = q <;> simp [hpq]
          rw [Finset.sum_congr rfl (fun q _ => hsplit q), Finset.sum_add_distrib,
            Finset.sum_ite_eq A p (fun q => ‖csGram C N p q‖)]
          simp [hp]
      _ = _ := by
          congr 1
          exact Finset.sum_congr rfl fun p _ => norm_csGram_self C N p
  -- assemble
  rw [hX]
  have hnn : 0 ≤ ∑ m ∈ Finset.range N, ‖h m‖ := Finset.sum_nonneg fun m _ => norm_nonneg _
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
  calc ‖∑ m ∈ Finset.range N, g m * h m‖ ^ 2 ≤ (∑ m ∈ Finset.range N, ‖h m‖) ^ 2 := by
        nlinarith [h1, hnn, norm_nonneg (∑ m ∈ Finset.range N, g m * h m)]
    _ ≤ (N : ℝ) * ∑ m ∈ Finset.range N, ‖h m‖ ^ 2 := h2
    _ ≤ (N : ℝ) * _ := mul_le_mul_of_nonneg_left h3 hNnn

end NormalNumbers.CastingOut
