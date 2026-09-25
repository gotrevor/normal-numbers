import NormalNumbers.ElliottArchBands
import ErdosProblems.Erdos49.PNT.IEANTN.Mertens

/-!
# The damping step: from the sharp cutoff to the Dirichlet series (lap 97)

Lap 96 left `ShiftedMertensSmall` and `ArchCorrModerate` as the two de la Vallée Poussin-strength
inputs of the Elliott consumer.  This file starts discharging them, by the route found in the
lap-97 survey, which is *not* Abel summation (lap 96 showed that cannot work):

> `1/log n = ∫_0^∞ n^{-w} dw`, hence
> `∑_p p^{-s} = ∫_0^∞ (-ζ'/ζ)(s+w) dw + O(1)`,
> and both target bounds follow from a bound on `ζ'/ζ` on `σ > 1` by an elementary integration:
> `∫_0^∞ min(1/(δ+w), R) dw = log(1/(δR)) + O(1)` where `R` is the bound at the relevant height.
> Sub-unit band: `R ≍ 1/|v|` (pole-local, and mathlib already has `ζ(1+it) ≠ 0`).
> Moderate band: `R ≍ log|v|` (de la Vallée Poussin).

The first step of that route is arithmetic, not analytic: replace the sharp cutoff `p ≤ X` in
`archCorr` by the analytic damping `p^{-1/log X}` over **all** primes.  This file proves the
cutoff-to-damping half, whose cost is exactly Mertens' first theorem.

`Mertens.sum_log_prime_div_eq_log` (`ErdosProblems.Erdos49.PNT.IEANTN.Mertens`, sorry-free, explicit
constant `log 4 + 4`) is the input; the tail half `∑_{p > X} p^{-1-1/log X} = O(1)` is the next
lap's target and is already scaffolded in `Erdos67b.PrimeEstimates.expWeightedPrimeTail`.
-/

open Finset

namespace NormalNumbers.ElliottDamped

open Erdos67b NormalNumbers.ElliottZetaOmegaPretentious NormalNumbers.ElliottTwistBootstrap

noncomputable section

/-- Mertens' first theorem in this campaign's index set. -/
theorem sum_log_div_primesUpTo_le {X : ℕ} (hX : 1 ≤ X) :
    ∑ p ∈ primesUpTo X, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log (X : ℝ) + (Real.log 4 + 4) := by
  classical
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hfloor : ⌊(X : ℝ)⌋₊ = X := Nat.floor_natCast X
  have hset : (primesUpTo X) = {p ∈ Ioc 0 ⌊(X : ℝ)⌋₊ | p.Prime} := by
    rw [hfloor]
    ext p
    simp only [primesUpTo, mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro ⟨hp, hpp⟩; exact ⟨⟨hpp.pos, by omega⟩, hpp⟩
    · rintro ⟨⟨_, hle⟩, hpp⟩; exact ⟨by omega, hpp⟩
  have hM := Mertens.sum_log_prime_div_eq_log hXR
  rw [abs_le] at hM
  rw [hset]
  linarith [hM.2]

/-- The analytically damped correlation: the same phases, weighted by `p^{-1-1/log X}` instead of
being cut off sharply at `X`. -/
def dampedArchCorr (v : ℝ) (X : ℕ) : ℂ :=
  ∑ p ∈ primesUpTo X,
    (starRingEnd ℂ) (archimedeanTwist v p) *
      (((p : ℝ) ^ (-(1 : ℝ) - (Real.log (X : ℝ))⁻¹) : ℝ) : ℂ)

/-- **The damping costs an absolute constant.**  Replacing `1/p` by `p^{-1-1/log X}` inside the
sharp cutoff changes the correlation by at most `1 + (log 4 + 4)/log X`.  The mechanism is
`1 - p^{-δ} ≤ δ log p` together with Mertens' first theorem, so the bound is uniform in the
frequency `v`. -/
theorem norm_archCorr_sub_dampedArchCorr_le {X : ℕ} (hX : 2 ≤ X) (v : ℝ) :
    ‖archCorr v X - dampedArchCorr v X‖ ≤ 1 + (Real.log 4 + 4) / Real.log (X : ℝ) := by
  classical
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  set δ : ℝ := (Real.log (X : ℝ))⁻¹ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hsub : archCorr v X - dampedArchCorr v X
      = ∑ p ∈ primesUpTo X, ((starRingEnd ℂ) (archimedeanTwist v p) *
          ((((p : ℝ)⁻¹ - (p : ℝ) ^ (-(1 : ℝ) - δ) : ℝ)) : ℂ)) := by
    rw [archCorr, dampedArchCorr, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hppos : 0 < p := (mem_primesUpTo.mp hp).1.pos
    have hcast : (((p : ℝ)⁻¹ : ℝ) : ℂ) = ((p : ℂ))⁻¹ := by push_cast; ring
    rw [Complex.ofReal_sub, mul_sub, hcast, div_eq_mul_inv]
  rw [hsub]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ primesUpTo X,
      ‖(starRingEnd ℂ) (archimedeanTwist v p) *
        ((((p : ℝ)⁻¹ - (p : ℝ) ^ (-(1 : ℝ) - δ) : ℝ)) : ℂ)‖
        ≤ δ * (Real.log (p : ℝ) / (p : ℝ)) := by
    intro p hp
    have hpp := (mem_primesUpTo.mp hp).1
    have hppos : 0 < p := hpp.pos
    have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.one_le
    have hpR0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hnorm1 : ‖(starRingEnd ℂ) (archimedeanTwist v p)‖ = 1 := by
      rw [RCLike.norm_conj]; exact norm_archimedeanTwist hppos v
    rw [norm_mul, hnorm1, one_mul, Complex.norm_real]
    -- `p^{-1-δ} = p⁻¹ · p^{-δ}` and `1 - p^{-δ} ≤ δ log p`
    have hsplit : (p : ℝ) ^ (-(1 : ℝ) - δ) = (p : ℝ)⁻¹ * (p : ℝ) ^ (-δ) := by
      rw [show -(1 : ℝ) - δ = (-1 : ℝ) + (-δ) by ring, Real.rpow_add hpR0, Real.rpow_neg_one]
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hpR
    have hexp : (1 : ℝ) - δ * Real.log (p : ℝ) ≤ (p : ℝ) ^ (-δ) := by
      have h1 : Real.exp (-(δ * Real.log (p : ℝ))) = (p : ℝ) ^ (-δ) := by
        rw [Real.rpow_def_of_pos hpR0]; ring_nf
      rw [← h1]
      linarith [Real.add_one_le_exp (-(δ * Real.log (p : ℝ)))]
    have hle1 : (p : ℝ) ^ (-δ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hpR (by linarith)
    have hdiff : (p : ℝ)⁻¹ - (p : ℝ) ^ (-(1 : ℝ) - δ)
        ≤ δ * (Real.log (p : ℝ) / (p : ℝ)) := by
      rw [hsplit]
      have : (p : ℝ)⁻¹ * (1 - (p : ℝ) ^ (-δ)) ≤ (p : ℝ)⁻¹ * (δ * Real.log (p : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      calc (p : ℝ)⁻¹ - (p : ℝ)⁻¹ * (p : ℝ) ^ (-δ) = (p : ℝ)⁻¹ * (1 - (p : ℝ) ^ (-δ)) := by ring
        _ ≤ (p : ℝ)⁻¹ * (δ * Real.log (p : ℝ)) := this
        _ = δ * (Real.log (p : ℝ) / (p : ℝ)) := by field_simp
    have hnn : 0 ≤ (p : ℝ)⁻¹ - (p : ℝ) ^ (-(1 : ℝ) - δ) := by
      rw [hsplit]
      have : (p : ℝ)⁻¹ * (p : ℝ) ^ (-δ) ≤ (p : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hle1 (by positivity)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hdiff
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hM := sum_log_div_primesUpTo_le (X := X) (by omega)
  have : δ * (∑ p ∈ primesUpTo X, Real.log (p : ℝ) / (p : ℝ))
      ≤ δ * (Real.log (X : ℝ) + (Real.log 4 + 4)) :=
    mul_le_mul_of_nonneg_left hM hδ0.le
  have hcancel : δ * Real.log (X : ℝ) = 1 := by
    rw [hδ]; field_simp
  have hrw : δ * (Real.log (X : ℝ) + (Real.log 4 + 4))
      = 1 + (Real.log 4 + 4) / Real.log (X : ℝ) := by
    rw [mul_add, hcancel, hδ]; field_simp
  linarith [hrw ▸ this]

end

end NormalNumbers.ElliottDamped
