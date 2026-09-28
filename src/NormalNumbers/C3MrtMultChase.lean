/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtMultRung
import NormalNumbers.C3MrtMultiInner
import NormalNumbers.C3MrtTwist

/-!
# The `ε`-chase on the merely-multiplicative anchor — `progression_log_rung_class_mult`

`rung_class_of_named_inputs_mult` (lap 60b) bounds the initial segment
`∑_{j ≤ A^m} j⁻¹ ∏_i z_i^{ω(M₀ j + r+i+1)}`.  This file converts that into the statement
`ProgressionLogRung` actually asks for: the log-averaged `K`-point correlation of `ζ^ω` over
the residue class of `r` mod `M₀`, in the ORIGINAL variable `n` with the weight `1/(n+1)`.

Three pieces of bookkeeping, all already in the repo:

* `class_sum_reindex` (lap 53) — `n ≡ r (mod M₀)`, `n < N` ↔ `n = M₀ j + r'`, `r' = r % M₀`;
* `filter_linear_lt_eq_range` — the resulting index set is `range (J+1)`, `J = (N−1−r')/M₀`;
* `progression_sum_bound_generic` (lap 46) — peel `j = 0`, transfer the weight
  `(M₀ j + r' + 1)⁻¹ → M₀⁻¹ j⁻¹` at cost `2/M₀` (`weight_transfer`, via `sum_inv_sq_le`),
  and close the window gap `(A^{⌊log_A J⌋}, J]` at cost `1 + log A`.

The `ε`-budget is a single rescale `ε ↦ ε·M₀`: the transferred weight carries the factor `M₀⁻¹`,
so the rung's saving `ε_r log N` arrives as `M₀⁻¹ ε_r log N`.

**What is NOT here.**  `multi_correlation_of_uniform_rung_prog` has to split `ε` in two and spend
half of it on `K^{K²} · truncB z Y K`, the truncation of the divisor-tuple expansion.  On this
anchor `M = 1`: there are no tuples, so that entire half of the chase is absent, and with it the
`Y`-truncation, the tuple mass and the budget.
-/

open Filter Finset

namespace NormalNumbers

namespace CastingOut

/-- **The log-averaged `K`-point correlation of `ζ^ω` over a residue class, on the
merely-multiplicative anchor.**  Same conclusion as `progression_log_rung_class`, but resting on
`KPointLogElliottMult K` — Elliott's own hypothesis class — plus
`TwistedPrimeSumSavingAllLevels`, with no powerful-divisor bridge, no truncation and no `K^{K²}`
budget anywhere beneath it. -/
theorem progression_log_rung_class_mult {K : ℕ} (hK : 0 < K) {Mo : ℕ} (hMo : 0 < Mo) (r : ℕ)
    (helliott : KPointLogElliottMult K) (hsave : TwistedPrimeSumSavingAllLevels)
    (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (hz01 : z 0 ≠ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖∑ n ∈ (range N).filter (fun n => n ≡ r [MOD Mo]),
          harmW n * ∏ i : Fin K, (z i) ^ omegaNat (n + (i : ℕ) + 1)‖
        ≤ C + ε * Real.log N := by
  classical
  set r' : ℕ := r % Mo with hr'def
  have hr' : r' < Mo := Nat.mod_lt _ hMo
  have hMoR : (0 : ℝ) < (Mo : ℝ) := by exact_mod_cast hMo
  set εr : ℝ := ε * Mo with hεrdef
  have hεr : 0 < εr := by rw [hεrdef]; positivity
  obtain ⟨A₀, hA₀2, hA₀⟩ :=
    rung_class_of_named_inputs_mult hK helliott hsave hMo r' z hz hz01 εr hεr
  obtain ⟨i₀, hi₀⟩ := hA₀ A₀ le_rfl
  set A : ℕ := A₀ with hAdef
  have hA2 : 2 ≤ A := hA₀2
  have hA1 : 1 ≤ A := by omega
  have hlogA : 0 ≤ Real.log A := Real.log_natCast_nonneg A
  have hlogAi : 0 ≤ Real.log ((A ^ i₀ : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_pow _ _ (by omega)
  refine ⟨(((r' : ℝ) + 1)⁻¹ + 2 / (Mo : ℝ))
      + (Mo : ℝ)⁻¹ * ((1 + Real.log ((A ^ i₀ : ℕ) : ℝ)) + (1 + Real.log A)),
    Mo * A ^ i₀ + r' + 1, fun N hN => ?_⟩
  have hr'N : r' < N := by
    have : 1 ≤ Mo * A ^ i₀ := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hN1 : 1 ≤ N := by omega
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  -- Step 1: rewrite the congruence filter and reindex.
  have hfil : (range N).filter (fun n => n ≡ r [MOD Mo])
      = (range N).filter (fun n => n % Mo = r') := by
    refine Finset.filter_congr fun n _ => ?_
    simp [Nat.ModEq, hr'def]
  set G : ℕ → ℂ := fun j => ∏ i : Fin K, (z i) ^ omegaNat (Mo * j + (r' + (i : ℕ) + 1)) with hG
  have hGnorm : ∀ j, ‖G j‖ ≤ 1 := by
    intro j
    rw [hG]
    simp only []
    rw [norm_prod]
    refine le_of_eq (Finset.prod_eq_one fun i _ => ?_)
    rw [norm_pow, hz i, one_pow]
  have hreindex : ∑ n ∈ (range N).filter (fun n => n ≡ r [MOD Mo]),
        harmW n * ∏ i : Fin K, (z i) ^ omegaNat (n + (i : ℕ) + 1)
      = ∑ j ∈ range ((N - 1 - r') / Mo + 1),
          ((((Mo * j + r' : ℕ) : ℝ) + 1)⁻¹ : ℝ) • G j := by
    rw [hfil, class_sum_reindex hMo hr' N
      (fun n => harmW n * ∏ i : Fin K, (z i) ^ omegaNat (n + (i : ℕ) + 1)),
      filter_linear_lt_eq_range hMo hr'N]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← harmW_smul]
    congr 1
    rw [hG]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 2
    omega
  rw [hreindex]
  set J : ℕ := (N - 1 - r') / Mo with hJdef
  have hJge : A ^ i₀ ≤ J := by
    rw [hJdef, Nat.le_div_iff_mul_le hMo]
    have : Mo * A ^ i₀ = A ^ i₀ * Mo := by ring
    omega
  have hJ1 : 1 ≤ J := le_trans (Nat.one_le_pow _ _ (by omega)) hJge
  set m : ℕ := Nat.log A J with hmdef
  have hmi : i₀ ≤ m := by
    rw [hmdef]
    calc i₀ = Nat.log A (A ^ i₀) := (Nat.log_pow (by omega) i₀).symm
      _ ≤ Nat.log A J := Nat.log_mono_right hJge
  -- Step 2: the rung, converted to the `•` spelling.
  have hrung' : ‖∑ j ∈ Finset.Ioc 0 (A ^ Nat.log A J), (((j : ℝ))⁻¹ : ℝ) • G j‖
      ≤ (1 + Real.log ((A ^ i₀ : ℕ) : ℝ)) + εr * Real.log N := by
    have hb := hi₀ m hmi
    have hspell : ∑ j ∈ Finset.Ioc 0 (A ^ m), (((j : ℝ))⁻¹ : ℝ) • G j
        = ∑ j ∈ Finset.Ioc 0 (A ^ m), (Erdos67b.harmonicWeight j : ℂ) *
            ∏ i : Fin K, (z (i : ℕ)) ^ omegaNat (Mo * j + (r' + (i : ℕ) + 1)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hG, Complex.real_smul, Erdos67b.harmonicWeight]
    rw [← hmdef, hspell]
    refine le_trans hb ?_
    have hAmJ : A ^ m ≤ J := Nat.pow_log_le_self A (by omega)
    have hJN : J ≤ N := le_trans (Nat.div_le_self _ _) (by omega)
    have hcast : ((A : ℝ)) ^ m ≤ (N : ℝ) := by exact_mod_cast le_trans hAmJ hJN
    have hlogpow : (m : ℝ) * Real.log A ≤ Real.log N := by
      have := Real.log_le_log (by positivity) hcast
      rwa [Real.log_pow] at this
    have hfin : (m : ℝ) * (εr * Real.log A) ≤ εr * Real.log N := by
      calc (m : ℝ) * (εr * Real.log A) = εr * ((m : ℝ) * Real.log A) := by ring
        _ ≤ εr * Real.log N := mul_le_mul_of_nonneg_left hlogpow hεr.le
    linarith
  -- Step 3: weight transfer + window gap.
  have hmain := progression_sum_bound_generic (L := Mo) (a := r') (A := A) (J := J)
    hMo (by omega) hA2 hJ1 G hGnorm hrung'
  refine le_trans hmain ?_
  have hMoinv : (Mo : ℝ)⁻¹ * εr = ε := by
    rw [hεrdef]; field_simp
  have hdist : (Mo : ℝ)⁻¹ * (((1 + Real.log ((A ^ i₀ : ℕ) : ℝ)) + εr * Real.log N)
        + (1 + Real.log A))
      = (Mo : ℝ)⁻¹ * ((1 + Real.log ((A ^ i₀ : ℕ) : ℝ)) + (1 + Real.log A))
        + ((Mo : ℝ)⁻¹ * εr) * Real.log N := by ring
  rw [hdist, hMoinv]
  linarith

#print axioms progression_log_rung_class_mult

end CastingOut

end NormalNumbers
