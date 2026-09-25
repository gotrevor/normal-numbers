import NormalNumbers.ElliottArchBands
import NormalNumbers.ElliottLogIntegral
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

/-! ### The tail half: `∑_{p > X} p^{-1-1/log X} = O(1)` -/

open Erdos67b.PrimeEstimates

/-- A general prime interval splits additively at an interior point. -/
theorem sum_primesInInterval_split {f : ℕ → ℝ} {X M Y : ℕ} (hXM : X ≤ M) (hMY : M ≤ Y) :
    ∑ p ∈ primesInInterval X Y, f p
      = (∑ p ∈ primesInInterval X M, f p) + ∑ p ∈ primesInInterval M Y, f p := by
  classical
  have hunion : primesInInterval X Y = primesInInterval X M ∪ primesInInterval M Y := by
    ext p
    simp only [Finset.mem_union, mem_primesInInterval]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hpM : p ≤ M
      · exact Or.inl ⟨h1, hpM, h3⟩
      · exact Or.inr ⟨by omega, h2, h3⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h1, by omega, h3⟩
      · exact ⟨by omega, h2, h3⟩
  have hdisj : Disjoint (primesInInterval X M) (primesInInterval M Y) := by
    refine Finset.disjoint_left.mpr ?_
    intro p hp hp'
    have h1 := (mem_primesInInterval.mp hp).2.1
    have h2 := (mem_primesInInterval.mp hp').1
    omega
  rw [hunion, Finset.sum_union hdisj]

/-- **One square block of the damped tail.**  On `(M, N]` with `N ≤ M²`, the damped weight is at
most `M^{-δ}` and the reciprocal mass is at most `log 2 + 2·mertensBound`. -/
theorem dampedBlock_le {X M N : ℕ} (hX : 2 ≤ X) (hM : 2 ≤ M) (hMN : M ≤ N) (hN : N ≤ M ^ 2) :
    ∑ p ∈ primesInInterval M N, (p : ℝ) ^ (-(1 : ℝ) - (Real.log (X : ℝ))⁻¹)
      ≤ (M : ℝ) ^ (-(Real.log (X : ℝ))⁻¹) * (Real.log 2 + 2 * PrimeEstimates.mertensBound) := by
  classical
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  set δ : ℝ := (Real.log (X : ℝ))⁻¹ with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  -- termwise
  have hterm : ∀ p ∈ primesInInterval M N,
      (p : ℝ) ^ (-(1 : ℝ) - δ) ≤ (M : ℝ) ^ (-δ) * (p : ℝ)⁻¹ := by
    intro p hp
    have hpM : M < p := (mem_primesInInterval.mp hp).1
    have hpR : (M : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpM.le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hsplit : (p : ℝ) ^ (-(1 : ℝ) - δ) = (p : ℝ) ^ (-δ) * (p : ℝ)⁻¹ := by
      rw [show -(1 : ℝ) - δ = (-δ) + (-1 : ℝ) by ring, Real.rpow_add hppos, Real.rpow_neg_one]
    have hmono : (p : ℝ) ^ (-δ) ≤ (M : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos hMpos hpR (by linarith)
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hmono (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hmass : ∑ p ∈ primesInInterval M N, (p : ℝ)⁻¹
      ≤ Real.log 2 + 2 * PrimeEstimates.mertensBound := by
    have h := PrimeEstimates.reciprocalPrimeInterval_le_log_log_sub_add hM hMN
    have hNR : (0 : ℝ) < (N : ℝ) := by
      have : 2 ≤ N := le_trans hM hMN
      exact_mod_cast (by omega : 0 < N)
    have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by linarith)
    have hlogN : Real.log (N : ℝ) ≤ 2 * Real.log (M : ℝ) := by
      have : (N : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hN
      have := Real.log_le_log hNR this
      rwa [Real.log_pow] at this
      
    have hstep : Real.log (Real.log (N : ℝ)) ≤ Real.log 2 + Real.log (Real.log (M : ℝ)) := by
      have h1 : Real.log (Real.log (N : ℝ)) ≤ Real.log (2 * Real.log (M : ℝ)) := by
        refine Real.log_le_log ?_ hlogN
        have : 2 ≤ N := le_trans hM hMN
        exact Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      rwa [Real.log_mul (by norm_num) (ne_of_gt hlogM)] at h1
    exact le_trans h (by linarith)
  have hpos : (0 : ℝ) ≤ (M : ℝ) ^ (-δ) := by positivity
  exact mul_le_mul_of_nonneg_left hmass hpos

/-- The damped tail over `(X, X^{2^K}]`, by induction on the number of square blocks. -/
theorem dampedTail_blocks {X : ℕ} (hX : 2 ≤ X) :
    ∀ K : ℕ, ∀ Y : ℕ, Y ≤ X ^ (2 ^ K) →
      ∑ p ∈ primesInInterval X Y, (p : ℝ) ^ (-(1 : ℝ) - (Real.log (X : ℝ))⁻¹)
        ≤ (Real.log 2 + 2 * PrimeEstimates.mertensBound)
            * ∑ k ∈ Finset.range K, Real.exp (-(2 ^ k : ℝ)) := by
  classical
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  set δ : ℝ := (Real.log (X : ℝ))⁻¹ with hδ
  have hD0 : (0 : ℝ) ≤ Real.log 2 + 2 * PrimeEstimates.mertensBound := by
    have := PrimeEstimates.mertensBound_nonneg
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith [PrimeEstimates.mertensBound_nonneg]
  intro K
  induction K with
  | zero =>
    intro Y hY
    have hYX : Y ≤ X := by simpa using hY
    have hempty : primesInInterval X Y = ∅ := by
      refine Finset.eq_empty_of_forall_notMem ?_
      intro p hp
      have h1 := (mem_primesInInterval.mp hp).1
      have h2 := (mem_primesInInterval.mp hp).2.1
      omega
    simp [hempty]
  | succ K ih =>
    intro Y hY
    set M : ℕ := X ^ (2 ^ K) with hM
    have hM2 : 2 ≤ M := by
      rw [hM]
      calc 2 ≤ X := hX
        _ = X ^ 1 := (pow_one X).symm
        _ ≤ X ^ (2 ^ K) := Nat.pow_le_pow_right (by omega) (Nat.one_le_two_pow)
    have hXM : X ≤ M := by
      rw [hM]
      calc X = X ^ 1 := (pow_one X).symm
        _ ≤ X ^ (2 ^ K) := Nat.pow_le_pow_right (by omega) (Nat.one_le_two_pow)
    have hsum_nonneg : (0 : ℝ) ≤ Real.exp (-(2 ^ K : ℝ)) := (Real.exp_pos _).le
    have hrange : ∑ k ∈ Finset.range (K + 1), Real.exp (-(2 ^ k : ℝ))
        = (∑ k ∈ Finset.range K, Real.exp (-(2 ^ k : ℝ))) + Real.exp (-(2 ^ K : ℝ)) :=
      Finset.sum_range_succ _ _
    rcases le_or_gt Y M with hYM | hYM
    · refine le_trans (ih Y hYM) ?_
      rw [hrange]
      nlinarith [hD0, hsum_nonneg]
    · -- split at `M`
      have hMY : M ≤ Y := hYM.le
      rw [sum_primesInInterval_split (f := fun p => (p : ℝ) ^ (-(1 : ℝ) - δ)) hXM hMY]
      have hYM2 : Y ≤ M ^ 2 := by
        have : X ^ (2 ^ (K + 1)) = M ^ 2 := by
          rw [hM, ← pow_mul, pow_succ]
        omega
      have hblock := dampedBlock_le (X := X) (M := M) (N := Y) hX hM2 hMY hYM2
      have hMpow : (M : ℝ) ^ (-δ) ≤ Real.exp (-(2 ^ K : ℝ)) := by
        have hMRpos : (0 : ℝ) < (M : ℝ) := by
          have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
          linarith
        have hlogM : Real.log (M : ℝ) = (2 ^ K : ℝ) * Real.log (X : ℝ) := by
          rw [hM]
          push_cast [Real.log_pow]
          ring
        have : (M : ℝ) ^ (-δ) = Real.exp (-δ * Real.log (M : ℝ)) := by
          rw [Real.rpow_def_of_pos hMRpos]; ring_nf
        have hne : Real.log (X : ℝ) ≠ 0 := ne_of_gt hlogX
        rw [this, hlogM, hδ]
        refine Real.exp_le_exp.mpr (le_of_eq ?_)
        field_simp
      have hIH := ih M le_rfl
      have : (M : ℝ) ^ (-δ) * (Real.log 2 + 2 * PrimeEstimates.mertensBound)
          ≤ Real.exp (-(2 ^ K : ℝ)) * (Real.log 2 + 2 * PrimeEstimates.mertensBound) :=
        mul_le_mul_of_nonneg_right hMpow hD0
      rw [hrange]
      nlinarith [hblock, hIH]

/-- `∑_{k<K} e^{-2^k} ≤ 1`, uniformly in `K`; the doubly-exponential decay of the block weights. -/
theorem sum_exp_neg_two_pow_le (K : ℕ) :
    ∑ k ∈ Finset.range K, Real.exp (-(2 ^ k : ℝ)) ≤ 1 - 2 * Real.exp (-(2 ^ K : ℝ)) := by
  induction K with
  | zero =>
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : Real.exp (-(2 ^ 0 : ℝ)) = (Real.exp 1)⁻¹ := by
      norm_num [Real.exp_neg]
    rw [Finset.sum_range_zero, h2]
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    rw [inv_eq_one_div]
    have : 2 * (1 / Real.exp 1) ≤ 1 := by
      rw [mul_one_div, div_le_one hpos]; linarith
    linarith
  | succ K ih =>
    have hstep : 2 * Real.exp (-(2 ^ (K + 1) : ℝ)) ≤ Real.exp (-(2 ^ K : ℝ)) := by
      have h2 : (2 : ℝ) ≤ Real.exp ((2 : ℝ) ^ K) := by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
        have := Real.add_one_le_exp ((2 : ℝ) ^ K)
        linarith
      have hpos : (0 : ℝ) < Real.exp (-(2 ^ (K + 1) : ℝ)) := Real.exp_pos _
      have heq : Real.exp (-(2 ^ K : ℝ))
          = Real.exp ((2 : ℝ) ^ K) * Real.exp (-(2 ^ (K + 1) : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [heq]
      nlinarith
    rw [Finset.sum_range_succ]
    linarith [ih]

/-- **THE DAMPED TAIL IS ABSOLUTELY BOUNDED.**  For every cutoff `Y`, the damped weight of the
primes beyond `X` is at most `log 2 + 2·mertensBound`, uniformly in `X` and `Y`.  This is the
second half of the damping step: with `norm_archCorr_sub_dampedArchCorr_le` it says that the sharp
prefix `archCorr v X` is the full damped Dirichlet series up to an absolute constant. -/
theorem dampedTail_le {X : ℕ} (hX : 2 ≤ X) (Y : ℕ) :
    ∑ p ∈ primesInInterval X Y, (p : ℝ) ^ (-(1 : ℝ) - (Real.log (X : ℝ))⁻¹)
      ≤ Real.log 2 + 2 * PrimeEstimates.mertensBound := by
  have hD0 : (0 : ℝ) ≤ Real.log 2 + 2 * PrimeEstimates.mertensBound := by
    have h1 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith [PrimeEstimates.mertensBound_nonneg]
  have hYlt : Y < X ^ (2 ^ Y) := by
    calc Y < 2 ^ Y := Nat.lt_two_pow_self
      _ ≤ 2 ^ (2 ^ Y) := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt Nat.lt_two_pow_self)
      _ ≤ X ^ (2 ^ Y) := Nat.pow_le_pow_left hX _
  have hYle : Y ≤ X ^ (2 ^ Y) := hYlt.le
  have hmain := dampedTail_blocks hX Y Y hYle
  have hgeom := sum_exp_neg_two_pow_le Y
  have hexp : (0 : ℝ) < Real.exp (-(2 ^ Y : ℝ)) := Real.exp_pos _
  nlinarith [hmain, hgeom]

/-! ### The damping step, assembled -/

theorem sum_primesUpTo_split {M : Type*} [AddCommMonoid M] {f : ℕ → M} {X Y : ℕ} (hXY : X ≤ Y) :
    ∑ p ∈ primesUpTo Y, f p
      = (∑ p ∈ primesUpTo X, f p) + ∑ p ∈ primesInInterval X Y, f p := by
  classical
  have hunion : primesUpTo Y = primesUpTo X ∪ primesInInterval X Y := by
    ext p
    simp only [Finset.mem_union, mem_primesUpTo, mem_primesInInterval]
    constructor
    · rintro ⟨hp, hle⟩
      by_cases hpX : p ≤ X
      · exact Or.inl ⟨hp, hpX⟩
      · exact Or.inr ⟨by omega, hle, hp⟩
    · rintro (⟨hp, hle⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨hp, le_trans hle hXY⟩
      · exact ⟨h3, h2⟩
  have hdisj : Disjoint (primesUpTo X) (primesInInterval X Y) := by
    refine Finset.disjoint_left.mpr ?_
    intro p hp hp'
    have h1 := (mem_primesUpTo.mp hp).2
    have h2 := (mem_primesInInterval.mp hp').1
    omega
  rw [hunion, Finset.sum_union hdisj]

/-- The damped prefix at cutoff `Y`, with the damping exponent still tuned to `X`. -/
def dampedPrefix (v : ℝ) (X Y : ℕ) : ℂ :=
  ∑ p ∈ primesUpTo Y,
    (starRingEnd ℂ) (archimedeanTwist v p) *
      (((p : ℝ) ^ (-(1 : ℝ) - (Real.log (X : ℝ))⁻¹) : ℝ) : ℂ)

/-- **THE DAMPING STEP.**  The sharply cut-off Archimedean correlation at `X` equals the damped
prime sum at *any* cutoff `Y ≥ X`, up to an absolute constant — uniformly in the frequency `v` and
in `Y`.  This is what converts the combinatorial object `archCorr` into the analytic object
`∑_p p^{-1-1/log X-iv}`, to which the `ζ'/ζ` route of the module docstring applies. -/
theorem norm_archCorr_sub_dampedPrefix_le {X : ℕ} (hX : 2 ≤ X) (v : ℝ) (Y : ℕ) (hXY : X ≤ Y) :
    ‖archCorr v X - dampedPrefix v X Y‖
      ≤ (1 + (Real.log 4 + 4) / Real.log (X : ℝ))
        + (Real.log 2 + 2 * PrimeEstimates.mertensBound) := by
  classical
  set δ : ℝ := (Real.log (X : ℝ))⁻¹ with hδ
  have hsplit : dampedPrefix v X Y = dampedArchCorr v X
      + ∑ p ∈ primesInInterval X Y,
          (starRingEnd ℂ) (archimedeanTwist v p) * (((p : ℝ) ^ (-(1 : ℝ) - δ) : ℝ) : ℂ) := by
    rw [dampedPrefix, dampedArchCorr, hδ]
    exact sum_primesUpTo_split hXY
  have hblocknorm : ‖∑ p ∈ primesInInterval X Y,
      (starRingEnd ℂ) (archimedeanTwist v p) * (((p : ℝ) ^ (-(1 : ℝ) - δ) : ℝ) : ℂ)‖
      ≤ Real.log 2 + 2 * PrimeEstimates.mertensBound := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ p ∈ primesInInterval X Y,
        ‖(starRingEnd ℂ) (archimedeanTwist v p) * (((p : ℝ) ^ (-(1 : ℝ) - δ) : ℝ) : ℂ)‖
          = (p : ℝ) ^ (-(1 : ℝ) - δ) := by
      intro p hp
      have hppos : 0 < p := (mem_primesInInterval.mp hp).2.2.pos
      have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
      rw [norm_mul, RCLike.norm_conj, norm_archimedeanTwist hppos v, one_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [Finset.sum_congr rfl hterm]
    exact dampedTail_le hX Y
  have := norm_archCorr_sub_dampedArchCorr_le hX v
  calc ‖archCorr v X - dampedPrefix v X Y‖
      = ‖(archCorr v X - dampedArchCorr v X)
          - ∑ p ∈ primesInInterval X Y,
              (starRingEnd ℂ) (archimedeanTwist v p) * (((p : ℝ) ^ (-(1 : ℝ) - δ) : ℝ) : ℂ)‖ := by
        rw [hsplit]; ring_nf
    _ ≤ ‖archCorr v X - dampedArchCorr v X‖
          + ‖∑ p ∈ primesInInterval X Y,
              (starRingEnd ℂ) (archimedeanTwist v p) * (((p : ℝ) ^ (-(1 : ℝ) - δ) : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
    _ ≤ _ := by linarith

/-- The norm of the damped weight of the primes in `(X, Y]`: an absolute bound, uniform in the
frequency `v` and in the cutoff `Y`.  Extracted from `norm_archCorr_sub_dampedPrefix_le`'s
internals so that the *cutoff* can be moved freely (`norm_dampedPrefix_transfer`). -/
theorem norm_dampedPrefix_sub_le {X : ℕ} (hX : 2 ≤ X) (v : ℝ) (Y : ℕ) (hXY : X ≤ Y) :
    ‖dampedPrefix v X Y - dampedPrefix v X X‖
      ≤ Real.log 2 + 2 * PrimeEstimates.mertensBound := by
  classical
  set δ : ℝ := (Real.log (X : ℝ))⁻¹ with hδ
  have hsplit : dampedPrefix v X Y - dampedPrefix v X X
      = ∑ p ∈ primesInInterval X Y,
          (starRingEnd ℂ) (archimedeanTwist v p) * (((p : ℝ) ^ (-(1 : ℝ) - δ) : ℝ) : ℂ) := by
    have h := sum_primesUpTo_split (f := fun p : ℕ =>
      (starRingEnd ℂ) (archimedeanTwist v p) * (((p : ℝ) ^ (-(1 : ℝ) - δ) : ℝ) : ℂ)) hXY
    simp only [dampedPrefix, hδ] at *
    rw [h]
    ring
  rw [hsplit]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ primesInInterval X Y,
      ‖(starRingEnd ℂ) (archimedeanTwist v p) * (((p : ℝ) ^ (-(1 : ℝ) - δ) : ℝ) : ℂ)‖
        = (p : ℝ) ^ (-(1 : ℝ) - δ) := by
    intro p hp
    have hppos : 0 < p := (mem_primesInInterval.mp hp).2.2.pos
    rw [norm_mul, RCLike.norm_conj, norm_archimedeanTwist hppos v, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [Finset.sum_congr rfl hterm]
  exact dampedTail_le hX Y

/-- **THE CUTOFF IS FREE.**  Because the damping exponent is tuned to `X`, the damped prefix at two
different cutoffs `Y, Y' ≥ X` differ by an absolute constant.  This is what lets the analytic input
below be stated only at a *large* cutoff (`sliceCut X`), where the truncated von Mangoldt series is
genuinely within `O(1)` of `−ζ'/ζ`, while the consumers keep calling it at `Y = X`. -/
theorem norm_dampedPrefix_transfer {X : ℕ} (hX : 2 ≤ X) (v : ℝ) (Y Y' : ℕ)
    (hXY : X ≤ Y) (hXY' : X ≤ Y') :
    ‖dampedPrefix v X Y‖
      ≤ ‖dampedPrefix v X Y'‖ + 2 * (Real.log 2 + 2 * PrimeEstimates.mertensBound) := by
  have h1 := norm_dampedPrefix_sub_le hX v Y hXY
  have h2 := norm_dampedPrefix_sub_le hX v Y' hXY'
  have h3 : ‖dampedPrefix v X Y - dampedPrefix v X Y'‖
      ≤ 2 * (Real.log 2 + 2 * PrimeEstimates.mertensBound) := by
    have : dampedPrefix v X Y - dampedPrefix v X Y'
        = (dampedPrefix v X Y - dampedPrefix v X X)
          - (dampedPrefix v X Y' - dampedPrefix v X X) := by ring
    rw [this]
    calc ‖_‖ ≤ ‖dampedPrefix v X Y - dampedPrefix v X X‖
          + ‖dampedPrefix v X Y' - dampedPrefix v X X‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have := norm_le_norm_add_norm_sub' (dampedPrefix v X Y) (dampedPrefix v X Y')
  linarith

/-- The cutoff at which the analytic (`ζ'/ζ`) inputs are stated: `exp((log X)²)`, so that
`sliceCut X ^ (−1/log X) = 1/X` and the primes beyond the cut contribute `≤ (log X)²/X ≤ 1` to
every slice with `w ≥ 0`.  Nothing about its size is needed for the reductions — only the
*freedom* of the cutoff (`norm_dampedPrefix_transfer`) — so it is kept opaque here. -/
noncomputable def sliceCut (X : ℕ) : ℕ := ⌈Real.exp ((Real.log (X : ℝ)) ^ 2)⌉₊

/-- The absolute cost of moving the cutoff to `sliceCut X`. -/
def cutCost : ℝ := 2 * (Real.log 2 + 2 * PrimeEstimates.mertensBound)

theorem cutCost_nonneg : 0 ≤ cutCost := by
  have h1 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have := PrimeEstimates.mertensBound_nonneg
  rw [cutCost]; linarith

/-! ### The two soft inputs, reduced to the damped Dirichlet series -/

open NormalNumbers.ElliottArchBands

/-- **The analytic input, sub-unit band.**  The damped prime series is bounded by `log(1/|v|)` up
to an absolute constant.  This is the statement the `ζ'/ζ` route produces: the pole bound
`|ζ'/ζ(σ+w+iv)| ≤ min((δ+w)^{-1}, |v|^{-1})` fed into
`ElliottLogIntegral.integral_le_one_add_log` with `T = |v|`. -/
def DampedSeriesBoundSmall (K : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ (X Y : ℕ) (v : ℝ), X₀ ≤ X → X ≤ Y → 0 < |v| → |v| ≤ 1 →
    ‖dampedPrefix v X Y‖ ≤ Real.log (1 / |v|) + K

/-- **The analytic input, moderate band.**  Same route with `T = 1/(C log|v|)`, i.e. the de la
Vallée Poussin bound `|ζ'/ζ(σ+iv)| ≤ C log|v|` on `σ > 1`. -/
def DampedSeriesBoundModerate (K : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ (X Y : ℕ) (v : ℝ), X₀ ≤ X → X ≤ Y → 1 < |v| →
    ‖dampedPrefix v X Y‖ ≤ Real.log (Real.log (|v| + 16)) + K

/-- The absolute cost of the damping step, once and for all. -/
def dampingCost : ℝ :=
  (1 + (Real.log 4 + 4) / Real.log 2) + (Real.log 2 + 2 * PrimeEstimates.mertensBound)

theorem norm_archCorr_sub_dampedPrefix_le' {X : ℕ} (hX : 2 ≤ X) (v : ℝ) (Y : ℕ) (hXY : X ≤ Y) :
    ‖archCorr v X - dampedPrefix v X Y‖ ≤ dampingCost := by
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : Real.log 2 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) hXR
  have hmono : (Real.log 4 + 4) / Real.log (X : ℝ) ≤ (Real.log 4 + 4) / Real.log 2 := by
    refine div_le_div_of_nonneg_left ?_ hlog2 hlogX
    have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  have := norm_archCorr_sub_dampedPrefix_le hX v Y hXY
  rw [dampingCost]
  linarith

/-- **(c′-I) FROM THE ANALYTIC INPUT.**  The damping step discharges the arithmetic half of
`ShiftedMertensSmall`; what is left is exactly the bound on the damped Dirichlet series. -/
theorem shiftedMertensSmall_of_dampedSeriesBound {K : ℝ} (h : DampedSeriesBoundSmall K) :
    ShiftedMertensSmall (K + dampingCost) := by
  obtain ⟨X₀, hX₀, h⟩ := h
  refine ⟨X₀, hX₀, ?_⟩
  intro X hXX₀ v hv0 hv1
  have hX : 2 ≤ X := le_trans hX₀ hXX₀
  have hd := h X X v hXX₀ le_rfl hv0 hv1
  have hs := norm_archCorr_sub_dampedPrefix_le' hX v X le_rfl
  calc ‖archCorr v X‖ ≤ ‖archCorr v X - dampedPrefix v X X‖ + ‖dampedPrefix v X X‖ := by
        simpa [add_comm] using norm_le_norm_add_norm_sub' (archCorr v X) (dampedPrefix v X X)
    _ ≤ dampingCost + (Real.log (1 / |v|) + K) := by linarith
    _ = Real.log (1 / |v|) + (K + dampingCost) := by ring

/-- **(c′-II-a) FROM THE ANALYTIC INPUT.**  Same reduction on the moderate band. -/
theorem archCorrModerate_of_dampedSeriesBound {K : ℝ} (h : DampedSeriesBoundModerate K) :
    ArchCorrModerate (K + dampingCost) := by
  obtain ⟨X₀, hX₀, h⟩ := h
  refine ⟨X₀, hX₀, ?_⟩
  intro X hXX₀ v hv1
  have hX : 2 ≤ X := le_trans hX₀ hXX₀
  have hd := h X X v hXX₀ le_rfl hv1
  have hs := norm_archCorr_sub_dampedPrefix_le' hX v X le_rfl
  calc ‖archCorr v X‖ ≤ ‖archCorr v X - dampedPrefix v X X‖ + ‖dampedPrefix v X X‖ := by
        simpa [add_comm] using norm_le_norm_add_norm_sub' (archCorr v X) (dampedPrefix v X X)
    _ ≤ dampingCost + (Real.log (Real.log (|v| + 16)) + K) := by linarith
    _ = Real.log (Real.log (|v| + 16)) + (K + dampingCost) := by ring

/-! ### The interchange: the damped prefix as an integral of a von Mangoldt-type series -/

open NormalNumbers.ElliottLogIntegral

/-- The `w`-slice: the log-weighted damped prime sum at abscissa shifted by `w`.  Summed over
*all* primes and all prime powers this would be `−ζ'/ζ(1+δ+w+iv)`; the point of the lemma below is
that the `w`-integral of this truncated version is exactly the damped prefix. -/
def logWeightedSlice (v : ℝ) (X Y : ℕ) (w : ℝ) : ℂ :=
  ∑ p ∈ primesUpTo Y,
    (starRingEnd ℂ) (archimedeanTwist v p) *
      (((Real.log (p : ℝ)) * (p : ℝ) ^ (-(1 : ℝ) - (Real.log (X : ℝ))⁻¹ - w) : ℝ) : ℂ)

/-- **THE INTERCHANGE.**  `dampedPrefix v X Y = ∫_0^∞ logWeightedSlice v X Y w dw`.

This is the structural step of the `ζ'/ζ` route, and because `dampedPrefix` is a *finite* sum the
interchange is `integral_finset_sum`, with no Fubini and no dominated convergence: the only
analytic input is `∫_0^∞ p^{-w} dw = 1/log p`.  Extending `logWeightedSlice` to all primes and
prime powers — an `O(1)` change after integration, by `dampedTail_le` — turns the right-hand side
into `∫_0^∞ (−ζ'/ζ)(1+δ+w+iv) dw`, which
`ElliottLogIntegral.integral_le_one_add_log` then bounds. -/
theorem dampedPrefix_eq_integral {X : ℕ} (hX : 2 ≤ X) (v : ℝ) (Y : ℕ) :
    dampedPrefix v X Y = ∫ w in Set.Ioi (0 : ℝ), logWeightedSlice v X Y w := by
  classical
  set δ : ℝ := (Real.log (X : ℝ))⁻¹ with hδ
  have hterm : ∀ p ∈ primesUpTo Y,
      (∫ w in Set.Ioi (0 : ℝ),
        (starRingEnd ℂ) (archimedeanTwist v p) *
          (((Real.log (p : ℝ)) * (p : ℝ) ^ (-(1 : ℝ) - δ - w) : ℝ) : ℂ))
        = (starRingEnd ℂ) (archimedeanTwist v p) * (((p : ℝ) ^ (-(1 : ℝ) - δ) : ℝ) : ℂ) := by
    intro p hp
    have hpp := (mem_primesUpTo.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    have hcongr : ∀ w ∈ Set.Ioi (0 : ℝ),
        (starRingEnd ℂ) (archimedeanTwist v p) *
            (((Real.log (p : ℝ)) * (p : ℝ) ^ (-(1 : ℝ) - δ - w) : ℝ) : ℂ)
          = ((starRingEnd ℂ) (archimedeanTwist v p) *
              (((Real.log (p : ℝ)) * (p : ℝ) ^ (-(1 : ℝ) - δ) : ℝ) : ℂ))
            * (((p : ℝ) ^ (-w) : ℝ) : ℂ) := by
      intro w _
      have : (p : ℝ) ^ (-(1 : ℝ) - δ - w) = (p : ℝ) ^ (-(1 : ℝ) - δ) * (p : ℝ) ^ (-w) := by
        rw [← Real.rpow_add hp0]
        congr 1
      rw [this]
      push_cast
      ring
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
      MeasureTheory.integral_const_mul]
    have hofReal : (∫ w in Set.Ioi (0 : ℝ), (((p : ℝ) ^ (-w) : ℝ) : ℂ))
        = (((∫ w in Set.Ioi (0 : ℝ), (p : ℝ) ^ (-w)) : ℝ) : ℂ) :=
      _root_.integral_ofReal
    rw [hofReal, integral_rpow_neg_Ioi hp1, mul_assoc, ← Complex.ofReal_mul]
    congr 1
    field_simp
  have hint : ∀ p ∈ primesUpTo Y,
      MeasureTheory.IntegrableOn (fun w : ℝ =>
        (starRingEnd ℂ) (archimedeanTwist v p) *
          (((Real.log (p : ℝ)) * (p : ℝ) ^ (-(1 : ℝ) - δ - w) : ℝ) : ℂ)) (Set.Ioi 0) := by
    intro p hp
    have hpp := (mem_primesUpTo.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
    have hbase : MeasureTheory.IntegrableOn
        (fun w : ℝ => ((((p : ℝ) ^ (-w)) : ℝ) : ℂ)) (Set.Ioi 0) :=
      (integrableOn_rpow_neg_Ioi hp1).ofReal
    have := (hbase.const_mul ((starRingEnd ℂ) (archimedeanTwist v p) *
      (((Real.log (p : ℝ)) * (p : ℝ) ^ (-(1 : ℝ) - δ) : ℝ) : ℂ)))
    refine MeasureTheory.IntegrableOn.congr_fun this ?_ measurableSet_Ioi
    intro w _
    have hsplit : (p : ℝ) ^ (-(1 : ℝ) - δ - w) = (p : ℝ) ^ (-(1 : ℝ) - δ) * (p : ℝ) ^ (-w) := by
      rw [← Real.rpow_add hp0]
      congr 1
    simp only [hsplit]
    push_cast
    ring
  rw [dampedPrefix, ← hδ]
  rw [show (fun w : ℝ => logWeightedSlice v X Y w) = fun w : ℝ => ∑ p ∈ primesUpTo Y,
      (starRingEnd ℂ) (archimedeanTwist v p) *
        (((Real.log (p : ℝ)) * (p : ℝ) ^ (-(1 : ℝ) - δ - w) : ℝ) : ℂ) from rfl,
    MeasureTheory.integral_finsetSum _ hint]
  exact (Finset.sum_congr rfl hterm).symm

/-! ### Decay of the slice at large `w` -/

/-- The absolute constant `∑_n n^{-3/2}`, used only as a finite bound. -/
def pSeriesThreeHalves : ℝ := ∑' n : ℕ, ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹

theorem summable_pSeriesThreeHalves :
    Summable (fun n : ℕ => ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
  Real.summable_nat_rpow_inv.mpr (by norm_num)

theorem pSeriesThreeHalves_nonneg : 0 ≤ pSeriesThreeHalves :=
  tsum_nonneg fun n => by positivity

/-- `log x ≤ 2√x` for `x ≥ 1`, in `rpow` form. -/
theorem log_le_two_mul_rpow_half {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 2 * x ^ (1 / 2 : ℝ) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hroot : (0 : ℝ) < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hlog : Real.log (x ^ (1 / 2 : ℝ)) ≤ x ^ (1 / 2 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hroot
  have hhalf : Real.log (x ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * Real.log x :=
    Real.log_rpow hx0 _
  rw [hhalf] at hlog
  linarith

/-- **The slice decays geometrically past `w = 1`.**  Beyond the first unit of the `w`-integration
the abscissa exceeds `2`, and the log-weighted prime sum is dominated by an absolutely convergent
`p`-series times `2^{-w}`.  This is what makes the improper integral over `(0,∞)` converge, and it
is completely elementary — no ζ input. -/
theorem norm_logWeightedSlice_le_decay {X : ℕ} (hX : 2 ≤ X) (v : ℝ) (Y : ℕ) {w : ℝ} (hw : 1 ≤ w) :
    ‖logWeightedSlice v X Y w‖ ≤ (4 * pSeriesThreeHalves) * (2 : ℝ) ^ (-w) := by
  classical
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  set δ : ℝ := (Real.log (X : ℝ))⁻¹ with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ primesUpTo Y,
      ‖(starRingEnd ℂ) (archimedeanTwist v p) *
        (((Real.log (p : ℝ)) * (p : ℝ) ^ (-(1 : ℝ) - δ - w) : ℝ) : ℂ)‖
        ≤ (2 * (2 : ℝ) ^ (-w)) * (((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ * 2) := by
    intro p hp
    have hpp := (mem_primesUpTo.mp hp).1
    have hppos : 0 < p := hpp.pos
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by linarith
    rw [norm_mul, RCLike.norm_conj, norm_archimedeanTwist hppos v, one_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.log (p : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - δ - w))]
    -- `log p ≤ 2 p^{1/2}`
    have hlog := log_le_two_mul_rpow_half hp1
    have hstep1 : Real.log (p : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - δ - w)
        ≤ (2 * (p : ℝ) ^ (1 / 2 : ℝ)) * (p : ℝ) ^ (-(1 : ℝ) - δ - w) :=
      mul_le_mul_of_nonneg_right hlog (by positivity)
    have hcomb : (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - δ - w)
        = (p : ℝ) ^ (-(1 / 2 : ℝ) - δ - w) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    have hdrop : (p : ℝ) ^ (-(1 / 2 : ℝ) - δ - w) ≤ (p : ℝ) ^ (-(1 / 2 : ℝ) - w) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    -- `p^{-1/2-w} = p^{-3/2} · p^{1-w} ≤ p^{-3/2} · 2^{1-w}`
    have hsplit : (p : ℝ) ^ (-(1 / 2 : ℝ) - w) = (p : ℝ) ^ (-(3 / 2 : ℝ)) * (p : ℝ) ^ (1 - w) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    have hgeo : (p : ℝ) ^ (1 - w) ≤ (2 : ℝ) ^ (1 - w) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    have hinv : (p : ℝ) ^ (-(3 / 2 : ℝ)) = ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
      Real.rpow_neg hp0.le _
    have h2 : (2 : ℝ) ^ (1 - w) = 2 * (2 : ℝ) ^ (-w) := by
      rw [show (1 : ℝ) - w = 1 + (-w) by ring, Real.rpow_add (by norm_num), Real.rpow_one]
    have hpow_nonneg : (0 : ℝ) ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) := by positivity
    calc Real.log (p : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - δ - w)
        ≤ 2 * ((p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - δ - w)) := by linarith [hstep1]
      _ = 2 * (p : ℝ) ^ (-(1 / 2 : ℝ) - δ - w) := by rw [hcomb]
      _ ≤ 2 * (p : ℝ) ^ (-(1 / 2 : ℝ) - w) := by linarith [hdrop]
      _ = 2 * ((p : ℝ) ^ (-(3 / 2 : ℝ)) * (p : ℝ) ^ (1 - w)) := by rw [hsplit]
      _ ≤ 2 * ((p : ℝ) ^ (-(3 / 2 : ℝ)) * (2 : ℝ) ^ (1 - w)) := by
          have := mul_le_mul_of_nonneg_left hgeo hpow_nonneg
          linarith
      _ = (2 * (2 : ℝ) ^ (-w)) * (((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ * 2) := by
          rw [h2, hinv]; ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hbound : ∑ p ∈ primesUpTo Y, (((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ * 2)
      ≤ 2 * pSeriesThreeHalves := by
    rw [← Finset.sum_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact summable_pSeriesThreeHalves.sum_le_tsum _ (fun n _ => by positivity)
  have hfac : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ (-w) := by positivity
  calc (2 * (2 : ℝ) ^ (-w)) * ∑ p ∈ primesUpTo Y, (((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ * 2)
      ≤ (2 * (2 : ℝ) ^ (-w)) * (2 * pSeriesThreeHalves) :=
        mul_le_mul_of_nonneg_left hbound hfac
    _ = (4 * pSeriesThreeHalves) * (2 : ℝ) ^ (-w) := by ring

/-! ### Assembling the integral bound -/

theorem continuous_logWeightedSlice (v : ℝ) (X Y : ℕ) :
    Continuous (fun w : ℝ => logWeightedSlice v X Y w) := by
  classical
  refine continuous_finset_sum _ (fun p hp => ?_)
  have hpp := (mem_primesUpTo.mp hp).1
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  refine continuous_const.mul ?_
  refine Complex.continuous_ofReal.comp ?_
  refine continuous_const.mul ?_
  have hfun : (fun w : ℝ => (p : ℝ) ^ (-(1 : ℝ) - (Real.log (X : ℝ))⁻¹ - w))
      = fun w : ℝ => Real.exp ((-(1 : ℝ) - (Real.log (X : ℝ))⁻¹ - w) * Real.log (p : ℝ)) := by
    funext w
    rw [Real.rpow_def_of_pos hp0]
    ring_nf
  rw [hfun]
  fun_prop

theorem integrableOn_norm_slice_Ioc (v : ℝ) (X Y : ℕ) :
    MeasureTheory.IntegrableOn
      (fun w : ℝ => ‖logWeightedSlice v X Y w‖) (Set.Ioc (0 : ℝ) 1) :=
  ((continuous_logWeightedSlice v X Y).norm).integrableOn_Ioc

theorem integrableOn_norm_slice_Ioi {X : ℕ} (hX : 2 ≤ X) (v : ℝ) (Y : ℕ) :
    MeasureTheory.IntegrableOn
      (fun w : ℝ => ‖logWeightedSlice v X Y w‖) (Set.Ioi (1 : ℝ)) := by
  have hdom : MeasureTheory.IntegrableOn
      (fun w : ℝ => (4 * pSeriesThreeHalves) * (2 : ℝ) ^ (-w)) (Set.Ioi (1 : ℝ)) := by
    refine ((integrableOn_rpow_neg_Ioi (a := 2) (by norm_num)).mono_set ?_).const_mul _
    exact Set.Ioi_subset_Ioi (by norm_num)
  refine MeasureTheory.Integrable.mono' hdom
    (((continuous_logWeightedSlice v X Y).norm).aestronglyMeasurable.restrict) ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
  intro w hw
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_logWeightedSlice_le_decay hX v Y (le_of_lt hw)

/-- The absolute cost of the `w ≥ 1` range of the integral. -/
def tailCost : ℝ := (4 * pSeriesThreeHalves) / Real.log 2

theorem integral_norm_slice_Ioi_le {X : ℕ} (hX : 2 ≤ X) (v : ℝ) (Y : ℕ) :
    (∫ w in Set.Ioi (1 : ℝ), ‖logWeightedSlice v X Y w‖) ≤ tailCost := by
  have hS : 0 ≤ pSeriesThreeHalves := pSeriesThreeHalves_nonneg
  have hdom : MeasureTheory.IntegrableOn
      (fun w : ℝ => (4 * pSeriesThreeHalves) * (2 : ℝ) ^ (-w)) (Set.Ioi (1 : ℝ)) := by
    refine ((integrableOn_rpow_neg_Ioi (a := 2) (by norm_num)).mono_set ?_).const_mul _
    exact Set.Ioi_subset_Ioi (by norm_num)
  have hstep1 : (∫ w in Set.Ioi (1 : ℝ), ‖logWeightedSlice v X Y w‖)
      ≤ ∫ w in Set.Ioi (1 : ℝ), (4 * pSeriesThreeHalves) * (2 : ℝ) ^ (-w) := by
    refine MeasureTheory.setIntegral_mono_on (integrableOn_norm_slice_Ioi hX v Y) hdom
      measurableSet_Ioi ?_
    intro w hw
    exact norm_logWeightedSlice_le_decay hX v Y (le_of_lt hw)
  have hdom0 : MeasureTheory.IntegrableOn
      (fun w : ℝ => (4 * pSeriesThreeHalves) * (2 : ℝ) ^ (-w)) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_rpow_neg_Ioi (a := 2) (by norm_num)).const_mul _
  have hstep2 : (∫ w in Set.Ioi (1 : ℝ), (4 * pSeriesThreeHalves) * (2 : ℝ) ^ (-w))
      ≤ ∫ w in Set.Ioi (0 : ℝ), (4 * pSeriesThreeHalves) * (2 : ℝ) ^ (-w) := by
    refine MeasureTheory.setIntegral_mono_set hdom0 ?_ ?_
    · filter_upwards with w
      positivity
    · exact Filter.Eventually.of_forall (Set.Ioi_subset_Ioi (by norm_num))
  have hval : (∫ w in Set.Ioi (0 : ℝ), (4 * pSeriesThreeHalves) * (2 : ℝ) ^ (-w)) = tailCost := by
    rw [MeasureTheory.integral_const_mul, integral_rpow_neg_Ioi (a := 2) (by norm_num), tailCost]
    ring
  linarith [hstep1, hstep2, hval ▸ hstep2]

/-- **THE ASSEMBLY.**  A bound on the `w`-slice on `[0,1]` of the shape the `ζ'/ζ` estimates
supply — capped by `T⁻¹` up to `T`, harmonic beyond it — bounds the damped prefix by
`1 + log(1/T) + tailCost`, uniformly in `Y` and in the frequency.

Instantiating `T = |v|` gives `DampedSeriesBoundSmall`; `T = 1/(C log|v|)` gives
`DampedSeriesBoundModerate`.  Everything except the slice bound itself is now proved. -/
theorem norm_dampedPrefix_le_of_slice_le {X : ℕ} (hX : 2 ≤ X) (v : ℝ) (Y : ℕ) {T : ℝ}
    (hδT : (Real.log (X : ℝ))⁻¹ ≤ T) (hT1 : T ≤ 1)
    (hcap : ∀ w ∈ Set.Icc (0 : ℝ) T, ‖logWeightedSlice v X Y w‖ ≤ T⁻¹)
    (hharm : ∀ w ∈ Set.Icc T 1, ‖logWeightedSlice v X Y w‖ ≤ w⁻¹) :
    ‖dampedPrefix v X Y‖ ≤ 1 + Real.log (1 / T) + tailCost := by
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hδ0 : 0 < (Real.log (X : ℝ))⁻¹ := by positivity
  -- pass to the integral
  rw [dampedPrefix_eq_integral hX v Y]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  -- split at `w = 1`
  have hunion : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    ext w
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hw
      rcases le_or_gt w 1 with h | h
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h1)
      · exact h1
      · linarith
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    have h1 : w ≤ 1 := hw.2
    have h2 : (1 : ℝ) < w := hw'
    linarith
  have hsplit : (∫ w in Set.Ioi (0 : ℝ), ‖logWeightedSlice v X Y w‖)
      = (∫ w in Set.Ioc (0 : ℝ) 1, ‖logWeightedSlice v X Y w‖)
        + ∫ w in Set.Ioi (1 : ℝ), ‖logWeightedSlice v X Y w‖ := by
    rw [hunion]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
      (integrableOn_norm_slice_Ioc v X Y) (integrableOn_norm_slice_Ioi hX v Y)
  rw [hsplit]
  have hfirst : (∫ w in Set.Ioc (0 : ℝ) 1, ‖logWeightedSlice v X Y w‖)
      ≤ 1 + Real.log (1 / T) := by
    have hI : (∫ w in Set.Ioc (0 : ℝ) 1, ‖logWeightedSlice v X Y w‖)
        = ∫ w in (0 : ℝ)..1, ‖logWeightedSlice v X Y w‖ :=
      (intervalIntegral.integral_of_le (by norm_num)).symm
    rw [hI]
    refine NormalNumbers.ElliottLogIntegral.integral_le_one_add_log
      (δ := (Real.log (X : ℝ))⁻¹) hδ0 hδT hT1 ?_ (fun w _ => norm_nonneg _) hcap hharm
    exact ((continuous_logWeightedSlice v X Y).norm).intervalIntegrable 0 1
  linarith [integral_norm_slice_Ioi_le hX v Y]

/-- The constant-carrying form of the assembly. -/
theorem norm_dampedPrefix_le_of_slice_le' {X : ℕ} (hX : 2 ≤ X) (v : ℝ) (Y : ℕ) {T K : ℝ}
    (hδT : (Real.log (X : ℝ))⁻¹ ≤ T) (hT1 : T ≤ 1) (hK : 0 ≤ K)
    (hcap : ∀ w ∈ Set.Icc (0 : ℝ) T, ‖logWeightedSlice v X Y w‖ ≤ T⁻¹ + K)
    (hharm : ∀ w ∈ Set.Icc T 1, ‖logWeightedSlice v X Y w‖ ≤ w⁻¹ + K) :
    ‖dampedPrefix v X Y‖ ≤ 1 + Real.log (1 / T) + K + tailCost := by
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hδ0 : 0 < (Real.log (X : ℝ))⁻¹ := by positivity
  rw [dampedPrefix_eq_integral hX v Y]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  have hunion : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    ext w
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hw
      rcases le_or_gt w 1 with h | h
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h1)
      · exact h1
      · linarith
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    have h1 : w ≤ 1 := hw.2
    have h2 : (1 : ℝ) < w := hw'
    linarith
  have hsplit : (∫ w in Set.Ioi (0 : ℝ), ‖logWeightedSlice v X Y w‖)
      = (∫ w in Set.Ioc (0 : ℝ) 1, ‖logWeightedSlice v X Y w‖)
        + ∫ w in Set.Ioi (1 : ℝ), ‖logWeightedSlice v X Y w‖ := by
    rw [hunion]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
      (integrableOn_norm_slice_Ioc v X Y) (integrableOn_norm_slice_Ioi hX v Y)
  rw [hsplit]
  have hfirst : (∫ w in Set.Ioc (0 : ℝ) 1, ‖logWeightedSlice v X Y w‖)
      ≤ 1 + Real.log (1 / T) + K := by
    have hI : (∫ w in Set.Ioc (0 : ℝ) 1, ‖logWeightedSlice v X Y w‖)
        = ∫ w in (0 : ℝ)..1, ‖logWeightedSlice v X Y w‖ :=
      (intervalIntegral.integral_of_le (by norm_num)).symm
    rw [hI]
    refine NormalNumbers.ElliottLogIntegral.integral_le_one_add_log_add_const
      (δ := (Real.log (X : ℝ))⁻¹) hδ0 hδT hT1 hK ?_ (fun w _ => norm_nonneg _) hcap hharm
    exact ((continuous_logWeightedSlice v X Y).norm).intervalIntegrable 0 1
  linarith [integral_norm_slice_Ioi_le hX v Y]

/-- **The assembly with a multiplicative constant on the cap band** (lap 116).

Same as `norm_dampedPrefix_le_of_slice_le'` but the cap clause reads `C·T⁻¹ + K`.  The cap band has
length `T`, so the price is the additive `C` in the conclusion and nothing else — in particular the
`log(1/T)` main term keeps the sharp coefficient `1` from the harmonic band (lap 106).  This is the
form the *moderate* band needs, where the de la Vallée Poussin input carries an unknown constant. -/
theorem norm_dampedPrefix_le_of_slice_le_const {X : ℕ} (hX : 2 ≤ X) (v : ℝ) (Y : ℕ) {T C K : ℝ}
    (hδT : (Real.log (X : ℝ))⁻¹ ≤ T) (hT1 : T ≤ 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hcap : ∀ w ∈ Set.Icc (0 : ℝ) T, ‖logWeightedSlice v X Y w‖ ≤ C * T⁻¹ + K)
    (hharm : ∀ w ∈ Set.Icc T 1, ‖logWeightedSlice v X Y w‖ ≤ w⁻¹ + K) :
    ‖dampedPrefix v X Y‖ ≤ C + Real.log (1 / T) + K + tailCost := by
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hδ0 : 0 < (Real.log (X : ℝ))⁻¹ := by positivity
  rw [dampedPrefix_eq_integral hX v Y]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  have hunion : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    ext w
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro hw
      rcases le_or_gt w 1 with h | h
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr h
    · rintro (⟨h1, _⟩ | h1)
      · exact h1
      · linarith
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    have h1 : w ≤ 1 := hw.2
    have h2 : (1 : ℝ) < w := hw'
    linarith
  have hsplit : (∫ w in Set.Ioi (0 : ℝ), ‖logWeightedSlice v X Y w‖)
      = (∫ w in Set.Ioc (0 : ℝ) 1, ‖logWeightedSlice v X Y w‖)
        + ∫ w in Set.Ioi (1 : ℝ), ‖logWeightedSlice v X Y w‖ := by
    rw [hunion]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
      (integrableOn_norm_slice_Ioc v X Y) (integrableOn_norm_slice_Ioi hX v Y)
  rw [hsplit]
  have hfirst : (∫ w in Set.Ioc (0 : ℝ) 1, ‖logWeightedSlice v X Y w‖)
      ≤ C + Real.log (1 / T) + K := by
    have hI : (∫ w in Set.Ioc (0 : ℝ) 1, ‖logWeightedSlice v X Y w‖)
        = ∫ w in (0 : ℝ)..1, ‖logWeightedSlice v X Y w‖ :=
      (intervalIntegral.integral_of_le (by norm_num)).symm
    rw [hI]
    refine NormalNumbers.ElliottLogIntegral.integral_le_const_add_log_add_const
      (δ := (Real.log (X : ℝ))⁻¹) hδ0 hδT hT1 hK hC ?_ (fun w _ => norm_nonneg _) hcap hharm
    exact ((continuous_logWeightedSlice v X Y).norm).intervalIntegrable 0 1
  linarith [integral_norm_slice_Ioi_le hX v Y]

/-! ### The final shape of the two soft inputs: a bound on the slice -/

/-- **The `ζ'/ζ` input, sub-unit band, in slice form.**  The slice is the truncated von Mangoldt
series at `1+δ+w+iv`; the classical pole-local bound `|ζ'/ζ(s)| ≪ 1/|s-1|` (which needs only
`ζ(1+it) ≠ 0`, already in mathlib, plus compactness) gives exactly these two clauses with
`T = max(|v|, δ)`. -/
def SliceBoundSmall (K : ℝ) : Prop :=
  ∀ (X Y : ℕ) (v : ℝ), 1048576 ≤ X → sliceCut X ≤ Y → 0 < |v| → |v| ≤ 1 →
    (∀ w ∈ Set.Icc (0 : ℝ) (max |v| (Real.log (X : ℝ))⁻¹),
        ‖logWeightedSlice v X Y w‖ ≤ (max |v| (Real.log (X : ℝ))⁻¹)⁻¹ + K) ∧
    (∀ w ∈ Set.Icc (max |v| (Real.log (X : ℝ))⁻¹) 1,
        ‖logWeightedSlice v X Y w‖ ≤ w⁻¹ + K)

/-- **(c′-I) REDUCED TO THE SLICE BOUND.**  Everything between `archCorr` and `ζ'/ζ` is now
proved: the damping (laps 97–98), the interchange (lap 100), the decay (lap 101) and the
integration (lap 102). -/
theorem dampedSeriesBoundSmall_of_sliceBound {K : ℝ} (hK : 0 ≤ K) (h : SliceBoundSmall K) :
    DampedSeriesBoundSmall (1 + K + tailCost + cutCost) := by
  refine ⟨1048576, by norm_num, ?_⟩
  intro X Y v hX3 hXY hv0 hv1
  have hX : 2 ≤ X := by omega
  have hXR : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 3 ≤ X)
  have hlogX : 1 < Real.log (X : ℝ) := by
    have h3 : Real.log 3 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) hXR
    have : (1 : ℝ) < Real.log 3 := by
      have hexp : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      have := Real.log_lt_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    linarith
  have hδ0 : 0 < (Real.log (X : ℝ))⁻¹ := by positivity
  have hδ1 : (Real.log (X : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; exact Or.inr hlogX.le
  set T : ℝ := max |v| (Real.log (X : ℝ))⁻¹ with hT
  have hδT : (Real.log (X : ℝ))⁻¹ ≤ T := le_max_right _ _
  have hvT : |v| ≤ T := le_max_left _ _
  have hT0 : 0 < T := lt_of_lt_of_le hv0 hvT
  have hT1 : T ≤ 1 := max_le hv1 hδ1
  set Y' : ℕ := max Y (sliceCut X) with hY'
  have hXY' : X ≤ Y' := le_trans hXY (le_max_left _ _)
  obtain ⟨hcap, hharm⟩ := h X Y' v hX3 (le_max_right _ _) hv0 hv1
  have hmain0 := norm_dampedPrefix_le_of_slice_le' hX v Y' hδT hT1 hK hcap hharm
  have htr := norm_dampedPrefix_transfer hX v Y Y' hXY hXY'
  have hmain : ‖dampedPrefix v X Y‖ ≤ 1 + Real.log (1 / T) + K + tailCost + cutCost := by
    rw [cutCost] at *; linarith
  have hlogmono : Real.log (1 / T) ≤ Real.log (1 / |v|) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le hv0 hvT)
  have hlogv : 0 ≤ Real.log (1 / |v|) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hv0]
    linarith
  linarith [hmain, hlogmono]

/-- **The `ζ'/ζ` input, moderate band, in slice form.**  The de la Vallée Poussin bound
`|ζ'/ζ(σ+iv)| ≤ C log|v|` on `σ > 1` gives these two clauses with `T = max(1/log(|v|+16), δ)`. -/
def SliceBoundModerate (K : ℝ) : Prop :=
  ∀ (X Y : ℕ) (v : ℝ), 1048576 ≤ X → sliceCut X ≤ Y → 1 < |v| →
    (∀ w ∈ Set.Icc (0 : ℝ) (max (Real.log (|v| + 16))⁻¹ (Real.log (X : ℝ))⁻¹),
        ‖logWeightedSlice v X Y w‖
          ≤ (max (Real.log (|v| + 16))⁻¹ (Real.log (X : ℝ))⁻¹)⁻¹ + K) ∧
    (∀ w ∈ Set.Icc (max (Real.log (|v| + 16))⁻¹ (Real.log (X : ℝ))⁻¹) 1,
        ‖logWeightedSlice v X Y w‖ ≤ w⁻¹ + K)

/-- **(c′-II-a) REDUCED TO THE SLICE BOUND.** -/
theorem dampedSeriesBoundModerate_of_sliceBound {K : ℝ} (hK : 0 ≤ K) (h : SliceBoundModerate K) :
    DampedSeriesBoundModerate (1 + K + tailCost + cutCost) := by
  refine ⟨1048576, by norm_num, ?_⟩
  intro X Y v hX3 hXY hv1
  have hX : 2 ≤ X := by omega
  have hXR : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 3 ≤ X)
  have hlogX : 1 < Real.log (X : ℝ) := by
    have h3 : Real.log 3 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) hXR
    have : (1 : ℝ) < Real.log 3 := by
      have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have := Real.log_lt_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    linarith
  have hδ0 : 0 < (Real.log (X : ℝ))⁻¹ := by positivity
  have hδ1 : (Real.log (X : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; exact Or.inr hlogX.le
  have hv0 : (0 : ℝ) < |v| := lt_trans one_pos hv1
  have hL : (1 : ℝ) < Real.log (|v| + 16) := by
    have h17 : (17 : ℝ) ≤ |v| + 16 := by linarith
    have hlog17 : Real.log 17 ≤ Real.log (|v| + 16) := Real.log_le_log (by norm_num) h17
    have : (1 : ℝ) < Real.log 17 := by
      have hexp : Real.exp 1 < 17 := by linarith [Real.exp_one_lt_d9]
      have := Real.log_lt_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    linarith
  have hL0 : 0 < Real.log (|v| + 16) := by linarith
  set T : ℝ := max (Real.log (|v| + 16))⁻¹ (Real.log (X : ℝ))⁻¹ with hT
  have hδT : (Real.log (X : ℝ))⁻¹ ≤ T := le_max_right _ _
  have hLT : (Real.log (|v| + 16))⁻¹ ≤ T := le_max_left _ _
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hLT
  have hLinv1 : (Real.log (|v| + 16))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; exact Or.inr hL.le
  have hT1 : T ≤ 1 := max_le hLinv1 hδ1
  set Y' : ℕ := max Y (sliceCut X) with hY'
  have hXY' : X ≤ Y' := le_trans hXY (le_max_left _ _)
  obtain ⟨hcap, hharm⟩ := h X Y' v hX3 (le_max_right _ _) hv1
  have hmain0 := norm_dampedPrefix_le_of_slice_le' hX v Y' hδT hT1 hK hcap hharm
  have htr := norm_dampedPrefix_transfer hX v Y Y' hXY hXY'
  have hmain : ‖dampedPrefix v X Y‖ ≤ 1 + Real.log (1 / T) + K + tailCost + cutCost := by
    rw [cutCost] at *; linarith
  have hlogmono : Real.log (1 / T) ≤ Real.log (Real.log (|v| + 16)) := by
    refine Real.log_le_log (by positivity) ?_
    rw [div_le_iff₀ hT0]
    have : (Real.log (|v| + 16))⁻¹ * Real.log (|v| + 16) = 1 := by field_simp
    nlinarith [hLT, hL0]
  linarith [hmain, hlogmono]

/-! ### The log-weighted tail (lap 104)

The slice `logWeightedSlice v X Y w` is the prime part of `−ζ'/ζ(1+δ+w+iv)` *truncated* at `Y`.
To hand the analytic input the untruncated series one needs the tail
`∑_{p>Y} log p · p^{-1-δ-w}` to be `O(1)`, which is false at `Y = X` (it is `≍ 1/(δ+w)`) but true
at `Y = sliceCut X = exp((log X)²)`, because there the damping has already decayed by `Y^{-δ} = 1/X`
while the log-weight has only grown to `log Y = (log X)²`.  These are the square-block bricks for
that tail: the same iteration as `dampedTail_blocks`, but with Mertens' *first* theorem (two-sided,
constant `log 4 + 4`) supplying the block mass in place of Mertens' second. -/

/-- Mertens' first theorem, lower half, in this campaign's index set. -/
theorem sum_log_div_primesUpTo_ge {X : ℕ} (hX : 1 ≤ X) :
    Real.log (X : ℝ) - (Real.log 4 + 4) ≤ ∑ p ∈ primesUpTo X, Real.log (p : ℝ) / (p : ℝ) := by
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
  linarith [hM.1]

/-- The log-weighted reciprocal mass of a prime interval: `∑_{M<p≤N} log p/p ≤ log(N/M) + 2C`. -/
theorem sum_log_div_primesInInterval_le {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    ∑ p ∈ primesInInterval M N, Real.log (p : ℝ) / (p : ℝ)
      ≤ (Real.log (N : ℝ) - Real.log (M : ℝ)) + 2 * (Real.log 4 + 4) := by
  classical
  have hreal := sum_primesUpTo_split (f := fun p : ℕ => Real.log (p : ℝ) / (p : ℝ)) hMN
  have h1 := sum_log_div_primesUpTo_le (X := N) (le_trans hM hMN)
  have h2 := sum_log_div_primesUpTo_ge (X := M) hM
  linarith

/-- **One square block of the log-weighted tail.**  On `(M, N]` with `N ≤ M²`. -/
theorem logBlock_le {M N : ℕ} {a : ℝ} (hM : 2 ≤ M) (hMN : M ≤ N) (hN : N ≤ M ^ 2)
    (ha : 0 ≤ a) :
    ∑ p ∈ primesInInterval M N, Real.log (p : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - a)
      ≤ (M : ℝ) ^ (-a) * (Real.log (M : ℝ) + 2 * (Real.log 4 + 4)) := by
  classical
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by linarith)
  have hterm : ∀ p ∈ primesInInterval M N,
      Real.log (p : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - a)
        ≤ (M : ℝ) ^ (-a) * (Real.log (p : ℝ) / (p : ℝ)) := by
    intro p hp
    have hpM : M < p := (mem_primesInInterval.mp hp).1
    have hpR : (M : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpM.le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    have hsplit : (p : ℝ) ^ (-(1 : ℝ) - a) = (p : ℝ) ^ (-a) * (p : ℝ)⁻¹ := by
      rw [show -(1 : ℝ) - a = (-a) + (-1 : ℝ) by ring, Real.rpow_add hppos, Real.rpow_neg_one]
    have hmono : (p : ℝ) ^ (-a) ≤ (M : ℝ) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hMpos hpR (by linarith)
    rw [hsplit]
    have : Real.log (p : ℝ) * ((p : ℝ) ^ (-a) * (p : ℝ)⁻¹)
        = (p : ℝ) ^ (-a) * (Real.log (p : ℝ) / (p : ℝ)) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hmono (by positivity)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hmass : ∑ p ∈ primesInInterval M N, Real.log (p : ℝ) / (p : ℝ)
      ≤ Real.log (M : ℝ) + 2 * (Real.log 4 + 4) := by
    have h := sum_log_div_primesInInterval_le (M := M) (N := N) (by omega) hMN
    have hNR : (0 : ℝ) < (N : ℝ) := by
      have : 2 ≤ N := le_trans hM hMN
      exact_mod_cast (by omega : 0 < N)
    have hlogN : Real.log (N : ℝ) ≤ 2 * Real.log (M : ℝ) := by
      have hNM : (N : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hN
      have := Real.log_le_log hNR hNM
      rwa [Real.log_pow] at this
    linarith
  exact mul_le_mul_of_nonneg_left hmass (by positivity)

/-- **The log-weighted tail over `(Y, Z]`, by square blocks.**  Exact geometric shape: the `k`-th
block contributes `Y^{-a·2^k} · (2^k log Y + 2C)`. -/
theorem logTail_blocks {Y : ℕ} {a : ℝ} (hY : 2 ≤ Y) (ha : 0 ≤ a) :
    ∀ K : ℕ, ∀ Z : ℕ, Z ≤ Y ^ (2 ^ K) →
      ∑ p ∈ primesInInterval Y Z, Real.log (p : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - a)
        ≤ ∑ k ∈ Finset.range K,
            (Y : ℝ) ^ (-(a * 2 ^ k)) * (2 ^ k * Real.log (Y : ℝ) + 2 * (Real.log 4 + 4)) := by
  classical
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hYpos : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlogY : 0 < Real.log (Y : ℝ) := Real.log_pos (by linarith)
  intro K
  induction K with
  | zero =>
    intro Z hZ
    have hZY : Z ≤ Y := by simpa using hZ
    have hempty : primesInInterval Y Z = ∅ := by
      refine Finset.eq_empty_of_forall_notMem ?_
      intro p hp
      have h1 := (mem_primesInInterval.mp hp).1
      have h2 := (mem_primesInInterval.mp hp).2.1
      omega
    simp [hempty]
  | succ K ih =>
    intro Z hZ
    set M : ℕ := Y ^ (2 ^ K) with hM
    have hM2 : 2 ≤ M := by
      rw [hM]
      calc 2 ≤ Y := hY
        _ = Y ^ 1 := (pow_one Y).symm
        _ ≤ Y ^ (2 ^ K) := Nat.pow_le_pow_right (by omega) (Nat.one_le_two_pow)
    have hYM : Y ≤ M := by
      rw [hM]
      calc Y = Y ^ 1 := (pow_one Y).symm
        _ ≤ Y ^ (2 ^ K) := Nat.pow_le_pow_right (by omega) (Nat.one_le_two_pow)
    have hnew : (0 : ℝ) ≤ (Y : ℝ) ^ (-(a * 2 ^ K))
        * (2 ^ K * Real.log (Y : ℝ) + 2 * (Real.log 4 + 4)) := by
      have h1 : (0 : ℝ) < (Y : ℝ) ^ (-(a * 2 ^ K)) := Real.rpow_pos_of_pos hYpos _
      have h2 : (0 : ℝ) ≤ 2 ^ K * Real.log (Y : ℝ) + 2 * (Real.log 4 + 4) := by
        have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
        positivity
      positivity
    have hrange : ∑ k ∈ Finset.range (K + 1),
        (Y : ℝ) ^ (-(a * 2 ^ k)) * (2 ^ k * Real.log (Y : ℝ) + 2 * (Real.log 4 + 4))
        = (∑ k ∈ Finset.range K,
            (Y : ℝ) ^ (-(a * 2 ^ k)) * (2 ^ k * Real.log (Y : ℝ) + 2 * (Real.log 4 + 4)))
          + (Y : ℝ) ^ (-(a * 2 ^ K)) * (2 ^ K * Real.log (Y : ℝ) + 2 * (Real.log 4 + 4)) :=
      Finset.sum_range_succ _ _
    rcases le_or_gt Z M with hZM | hZM
    · refine le_trans (ih Z hZM) ?_
      rw [hrange]; linarith
    · have hMZ : M ≤ Z := hZM.le
      rw [sum_primesInInterval_split
        (f := fun p : ℕ => Real.log (p : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - a)) hYM hMZ]
      have hZM2 : Z ≤ M ^ 2 := by
        have : Y ^ (2 ^ (K + 1)) = M ^ 2 := by rw [hM, ← pow_mul, pow_succ]
        omega
      have hblock := logBlock_le (M := M) (N := Z) (a := a) hM2 hMZ hZM2 ha
      have hlogM : Real.log (M : ℝ) = (2 ^ K : ℝ) * Real.log (Y : ℝ) := by
        rw [hM]; push_cast [Real.log_pow]; ring
      have hMpow : (M : ℝ) ^ (-a) = (Y : ℝ) ^ (-(a * 2 ^ K)) := by
        have hMRpos : (0 : ℝ) < (M : ℝ) := by
          have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
          linarith
        rw [Real.rpow_def_of_pos hMRpos, Real.rpow_def_of_pos hYpos, hlogM]
        congr 1; ring
      rw [hMpow, hlogM] at hblock
      have hIH := ih M le_rfl
      rw [hrange]
      linarith

/-- A shifted geometric sum, with room to spare: `∑_{k<K} q^{k+1} ≤ 2q` for `q ≤ 1/2`. -/
theorem sum_geom_shift_le {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (K : ℕ) :
    ∑ k ∈ Finset.range K, q ^ (k + 1) ≤ 2 * q - 2 * q ^ (K + 1) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hpow : (0 : ℝ) ≤ q ^ (K + 1) := by positivity
    have hstep : 2 * q ^ (K + 2) ≤ q ^ (K + 1) := by
      have : q ^ (K + 2) = q ^ (K + 1) * q := by ring
      rw [this]
      nlinarith
    linarith

/-- The block weights sum geometrically: `∑_{k<K} X^{-2^k/2} ≤ 2 X^{-1/2}`. -/
theorem sum_rpow_neg_two_pow_half_le {X : ℝ} (hX : 4 ≤ X) (K : ℕ) :
    ∑ k ∈ Finset.range K, X ^ (-((2 : ℝ) ^ k / 2)) ≤ 2 * X ^ (-(1 / 2 : ℝ)) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  set q : ℝ := X ^ (-(1 / 2 : ℝ)) with hqdef
  have hq0 : (0 : ℝ) < q := Real.rpow_pos_of_pos hX0 _
  have hq : q ≤ 1 / 2 := by
    have h4 : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
      rw [show (-(1 / 2 : ℝ)) = -(1 / 2 : ℝ) from rfl, Real.rpow_neg (by norm_num)]
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num]
      rw [← Real.rpow_natCast (2 : ℝ) 2, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc q ≤ (4 : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hX (by norm_num)
      _ = 1 / 2 := h4
  have hterm : ∀ k ∈ Finset.range K, X ^ (-((2 : ℝ) ^ k / 2)) ≤ q ^ (k + 1) := by
    intro k _
    have hqk : q ^ (k + 1) = X ^ (-((k : ℝ) + 1) / 2) := by
      rw [hqdef, ← Real.rpow_natCast (X ^ (-(1 / 2 : ℝ))) (k + 1), ← Real.rpow_mul hX0.le]
      congr 1
      push_cast
      ring
    rw [hqk]
    refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
    have h2k : ((k : ℝ) + 1) ≤ (2 : ℝ) ^ k := by
      have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      exact_mod_cast hk
    have : -((2 : ℝ) ^ k / 2) ≤ -(((k : ℝ) + 1) / 2) := by linarith
    calc -((2 : ℝ) ^ k / 2) ≤ -(((k : ℝ) + 1) / 2) := this
      _ = -((k : ℝ) + 1) / 2 := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have := sum_geom_shift_le hq0.le hq K
  have hpos : (0 : ℝ) ≤ q ^ (K + 1) := by positivity
  linarith

/-- **The `k`-th block weight, collapsed.**  With `a ≥ 1/log X` and `log Y ≥ (log X)²` the
log-weight is beaten by the damping: put `t = a·2^k·log Y ≥ 2^k log X`; then `2^k log Y = t/a ≤
t log X` and `t e^{-t} ≤ 2 e^{-t/2}`, so the block contributes `≤ (2 log X + 2C)·X^{-2^k/2}`. -/
theorem logTail_term_le {X Y : ℕ} {a : ℝ} (hX : 2 ≤ X) (hY : 2 ≤ Y)
    (hlogY : (Real.log (X : ℝ)) ^ 2 ≤ Real.log (Y : ℝ)) (ha : (Real.log (X : ℝ))⁻¹ ≤ a) (k : ℕ) :
    (Y : ℝ) ^ (-(a * 2 ^ k)) * (2 ^ k * Real.log (Y : ℝ) + 2 * (Real.log 4 + 4))
      ≤ (2 * Real.log (X : ℝ) + 2 * (Real.log 4 + 4)) * (X : ℝ) ^ (-((2 : ℝ) ^ k / 2)) := by
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hlogY0 : 0 < Real.log (Y : ℝ) := Real.log_pos (by linarith)
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  set t : ℝ := a * 2 ^ k * Real.log (Y : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  -- `t ≥ 2^k log X`
  have haY : Real.log (X : ℝ) ≤ a * Real.log (Y : ℝ) := by
    have h1 : (Real.log (X : ℝ))⁻¹ * Real.log (Y : ℝ) ≤ a * Real.log (Y : ℝ) :=
      mul_le_mul_of_nonneg_right ha hlogY0.le
    have h2 : Real.log (X : ℝ) ≤ (Real.log (X : ℝ))⁻¹ * Real.log (Y : ℝ) := by
      rw [inv_mul_eq_div, le_div_iff₀ hlogX]
      nlinarith [hlogY]
    linarith
  have htlow : (2 : ℝ) ^ k * Real.log (X : ℝ) ≤ t := by
    rw [ht]
    calc (2 : ℝ) ^ k * Real.log (X : ℝ) ≤ (2 : ℝ) ^ k * (a * Real.log (Y : ℝ)) :=
          mul_le_mul_of_nonneg_left haY hpow.le
      _ = a * 2 ^ k * Real.log (Y : ℝ) := by ring
  -- the damping factor is `e^{-t}`
  have hYrpow : (Y : ℝ) ^ (-(a * 2 ^ k)) = Real.exp (-t) := by
    rw [Real.rpow_def_of_pos (by linarith), ht]; ring_nf
  -- `2^k log Y ≤ t · log X`
  have hmass : (2 : ℝ) ^ k * Real.log (Y : ℝ) ≤ t * Real.log (X : ℝ) := by
    have hinv : a⁻¹ ≤ Real.log (X : ℝ) := by
      rw [inv_le_comm₀ ha0 hlogX]; exact ha
    have hta : t * a⁻¹ = 2 ^ k * Real.log (Y : ℝ) := by
      rw [ht]; field_simp
    have : t * a⁻¹ ≤ t * Real.log (X : ℝ) := mul_le_mul_of_nonneg_left hinv ht0.le
    linarith [hta ▸ this]
  -- `t e^{-t} ≤ 2 e^{-t/2}` and `e^{-t} ≤ e^{-t/2} ≤ X^{-2^k/2}`
  have hhalf : Real.exp (-t) ≤ Real.exp (-(t / 2)) := Real.exp_le_exp.mpr (by linarith)
  have hcap : Real.exp (-(t / 2)) ≤ (X : ℝ) ^ (-((2 : ℝ) ^ k / 2)) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    exact Real.exp_le_exp.mpr (by nlinarith [htlow])
  have hte : t * Real.exp (-t) ≤ 2 * Real.exp (-(t / 2)) := by
    have h1 : t / 2 + 1 ≤ Real.exp (t / 2) := Real.add_one_le_exp _
    have h2 : Real.exp (-t) = Real.exp (-(t / 2)) * Real.exp (-(t / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-(t / 2)) * Real.exp (t / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have hpos : 0 < Real.exp (-(t / 2)) := Real.exp_pos _
    rw [h2]
    nlinarith [hpos, h1, h3]
  have hCnn : (0 : ℝ) ≤ 2 * (Real.log 4 + 4) := by
    have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  calc (Y : ℝ) ^ (-(a * 2 ^ k)) * (2 ^ k * Real.log (Y : ℝ) + 2 * (Real.log 4 + 4))
      = Real.exp (-t) * (2 ^ k * Real.log (Y : ℝ)) + Real.exp (-t) * (2 * (Real.log 4 + 4)) := by
        rw [hYrpow]; ring
    _ ≤ Real.exp (-t) * (t * Real.log (X : ℝ)) + Real.exp (-t) * (2 * (Real.log 4 + 4)) := by
        have := mul_le_mul_of_nonneg_left hmass (Real.exp_pos (-t)).le
        linarith
    _ = Real.log (X : ℝ) * (t * Real.exp (-t)) + (2 * (Real.log 4 + 4)) * Real.exp (-t) := by ring
    _ ≤ Real.log (X : ℝ) * (2 * Real.exp (-(t / 2)))
          + (2 * (Real.log 4 + 4)) * Real.exp (-(t / 2)) := by
        have h1 := mul_le_mul_of_nonneg_left hte hlogX.le
        have h2 := mul_le_mul_of_nonneg_left hhalf hCnn
        linarith
    _ = (2 * Real.log (X : ℝ) + 2 * (Real.log 4 + 4)) * Real.exp (-(t / 2)) := by ring
    _ ≤ (2 * Real.log (X : ℝ) + 2 * (Real.log 4 + 4)) * (X : ℝ) ^ (-((2 : ℝ) ^ k / 2)) := by
        refine mul_le_mul_of_nonneg_left hcap ?_
        linarith

/-- `log 4 ≤ 1.4`. -/
theorem log_four_le : Real.log 4 ≤ 1.4 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_lt_d9
  rw [h]; linarith

/-- **The numeric collapse.**  `(2 log X + 2C)·2·X^{-1/2} ≤ 1` for `X ≥ 2²⁰`.  Proved through
`s = X^{1/4} ≥ 32` and `log X = 4 log s ≤ 4(s−1)`, which turns the claim into `16s + 4C − 16 ≤ s²`. -/
theorem tailNumeric_le {X : ℝ} (hX : (1048576 : ℝ) ≤ X) :
    (2 * Real.log X + 2 * (Real.log 4 + 4)) * (2 * X ^ (-(1 / 2 : ℝ))) ≤ 1 := by
  have hX0 : (0 : ℝ) < X := by linarith
  set s : ℝ := X ^ (1 / 4 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hX0 _
  have hs32 : (32 : ℝ) ≤ s := by
    have hbase : ((1048576 : ℝ)) ^ (1 / 4 : ℝ) = 32 := by
      have h1 : (1048576 : ℝ) = (32 : ℝ) ^ (4 : ℕ) := by norm_num
      rw [h1, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
    calc (32 : ℝ) = ((1048576 : ℝ)) ^ (1 / 4 : ℝ) := hbase.symm
      _ ≤ s := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
  have hsq : s ^ 2 = X ^ (1 / 2 : ℝ) := by
    rw [hs, ← Real.rpow_natCast (X ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hX0.le]
    norm_num
  have hneg : X ^ (-(1 / 2 : ℝ)) = (s ^ 2)⁻¹ := by
    rw [hsq, Real.rpow_neg hX0.le]
  have hlogs : Real.log s = 1 / 4 * Real.log X := by rw [hs, Real.log_rpow hX0]
  have hlog : Real.log X ≤ 4 * (s - 1) := by
    have h1 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
    rw [hlogs] at h1
    linarith
  have hC : 2 * (Real.log 4 + 4) ≤ 10.8 := by linarith [log_four_le]
  have hsq0 : (0 : ℝ) < s ^ 2 := by positivity
  rw [hneg]
  have key : (2 * Real.log X + 2 * (Real.log 4 + 4)) * 2 ≤ s ^ 2 := by nlinarith [hs32, hlog, hC]
  have hrw : (2 * Real.log X + 2 * (Real.log 4 + 4)) * (2 * (s ^ 2)⁻¹)
      = ((2 * Real.log X + 2 * (Real.log 4 + 4)) * 2) / s ^ 2 := by field_simp
  rw [hrw, div_le_one hsq0]
  exact key

/-- **THE LOG-WEIGHTED TAIL IS AT MOST `1`.**  Beyond the cut `sliceCut X = exp((log X)²)`, and for
every shift `a ≥ δ = 1/log X` (i.e. every `w ≥ 0` in the slice), the log-weighted damped mass of the
primes past the cut is at most `1`, uniformly in the far endpoint `Z`.

This is what makes the slice inputs honest: the truncated von Mangoldt series at `sliceCut X` is
within `O(1)` of the full one, hence of `−ζ'/ζ(1+δ+w+iv)` (after the prime-power correction), while
at the consumers' own cutoff `Y = X` it is not (the tail there is `≍ 1/(δ+w)`).  `2²⁰` is where the
numeric collapse `(4 log X + 4C)/√X ≤ 1` first holds. -/
theorem logTail_le {X Y Z : ℕ} (hX : 1048576 ≤ X) (hY : sliceCut X ≤ Y) {a : ℝ}
    (ha : (Real.log (X : ℝ))⁻¹ ≤ a) :
    ∑ p ∈ primesInInterval Y Z, Real.log (p : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - a) ≤ 1 := by
  classical
  have hXR : (1048576 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX2 : 2 ≤ X := by omega
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hlogX1 : 1 ≤ Real.log (X : ℝ) := by
    have h : Real.log (Real.exp 1) ≤ Real.log (X : ℝ) :=
      Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    rwa [Real.log_exp] at h
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  -- the cut delivers `log Y ≥ (log X)²`
  have hcut : Real.exp ((Real.log (X : ℝ)) ^ 2) ≤ (Y : ℝ) := by
    have h1 : Real.exp ((Real.log (X : ℝ)) ^ 2) ≤ (sliceCut X : ℝ) := by
      rw [sliceCut]; exact Nat.le_ceil _
    have h2 : ((sliceCut X : ℕ) : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    linarith
  have hYpos : (0 : ℝ) < (Y : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hcut
  have hlogY : (Real.log (X : ℝ)) ^ 2 ≤ Real.log (Y : ℝ) := by
    have := Real.log_le_log (Real.exp_pos _) hcut
    rwa [Real.log_exp] at this
  have hY2 : 2 ≤ Y := by
    have h1 : (1 : ℝ) ≤ (Real.log (X : ℝ)) ^ 2 := by nlinarith
    have h2 := Real.add_one_le_exp ((Real.log (X : ℝ)) ^ 2)
    have : (2 : ℝ) ≤ (Y : ℝ) := by linarith
    exact_mod_cast this
  -- block decomposition
  have hZlt : Z ≤ Y ^ (2 ^ Z) := le_of_lt <| by
    calc Z < 2 ^ Z := Nat.lt_two_pow_self
      _ ≤ 2 ^ (2 ^ Z) := Nat.pow_le_pow_right (by omega) (Nat.le_of_lt Nat.lt_two_pow_self)
      _ ≤ Y ^ (2 ^ Z) := Nat.pow_le_pow_left hY2 _
  have hblocks := logTail_blocks (Y := Y) (a := a) hY2 ha0.le Z Z hZlt
  have hterms : ∑ k ∈ Finset.range Z,
      (Y : ℝ) ^ (-(a * 2 ^ k)) * (2 ^ k * Real.log (Y : ℝ) + 2 * (Real.log 4 + 4))
      ≤ ∑ k ∈ Finset.range Z,
          (2 * Real.log (X : ℝ) + 2 * (Real.log 4 + 4)) * (X : ℝ) ^ (-((2 : ℝ) ^ k / 2)) :=
    Finset.sum_le_sum (fun k _ => logTail_term_le hX2 hY2 hlogY ha k)
  have hgeom : ∑ k ∈ Finset.range Z, (X : ℝ) ^ (-((2 : ℝ) ^ k / 2))
      ≤ 2 * (X : ℝ) ^ (-(1 / 2 : ℝ)) :=
    sum_rpow_neg_two_pow_half_le (by linarith) Z
  have hCnn : (0 : ℝ) ≤ 2 * Real.log (X : ℝ) + 2 * (Real.log 4 + 4) := by
    have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  have hfinal : ∑ k ∈ Finset.range Z,
      (2 * Real.log (X : ℝ) + 2 * (Real.log 4 + 4)) * (X : ℝ) ^ (-((2 : ℝ) ^ k / 2))
      ≤ (2 * Real.log (X : ℝ) + 2 * (Real.log 4 + 4)) * (2 * (X : ℝ) ^ (-(1 / 2 : ℝ))) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hgeom hCnn
  have hnum := tailNumeric_le (X := (X : ℝ)) hXR
  linarith

/-! ### Mertens I gives the harmonic clause with the SHARP constant `1` (lap 106)

The `w ≥ T` clause of both slice inputs asks for `‖slice‖ ≤ w⁻¹ + K`, with the coefficient of `w⁻¹`
exactly `1` — anything larger multiplies the eventual `log(1/|v|)` and destroys the consumer.  The
observation of this lap is that **no cancellation is needed for it**: the trivial absolute bound is

  `∑_{p≤Y} log p · p^{-1-a} ≤ 1/a + (log 4 + 4)`,

with sharp constant `1`, and it follows from Mertens' *first* theorem by Abel summation in the form
`p^{-a} = a∫_{log p}^∞ e^{-as} ds`: the interchange is a finite sum, and
`∑_{p<e^s} log p/p ≤ s + (log 4 + 4)` is Mertens I.  Since `a = δ + w ≥ w`, this gives the harmonic
clause outright.  Only the *cap* clause `w ≤ T` needs `ζ'/ζ` (there the trivial bound is `1/δ`,
while the clause asks for `1/|v|`), and that is the whole remaining analytic input. -/

/-- `∫_{s>c} e^{-as} ds = e^{-ac}/a`. -/
theorem integral_exp_neg_mul_Ioi' {a c : ℝ} (ha : 0 < a) :
    ∫ s in Set.Ioi c, Real.exp (-a * s) = Real.exp (-a * c) / a := by
  have h := integral_exp_mul_Ioi (a := -a) (by linarith) c
  rw [h]
  field_simp

/-- `∫_{s>0} s e^{-as} ds = 1/a²`. -/
theorem integral_id_mul_exp_neg_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ s in Set.Ioi (0 : ℝ), s * Real.exp (-a * s) = 1 / a ^ 2 := by
  have hcongr : ∀ s ∈ Set.Ioi (0 : ℝ),
      s * Real.exp (-a * s) = s ^ (1 : ℝ) * Real.exp (-a * s ^ (1 : ℝ)) := by
    intro s _; rw [Real.rpow_one]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num : (-1 : ℝ) < 1) ha]
  rw [show ((1 : ℝ) + 1) / 1 = 2 by norm_num, show -((1 : ℝ) + 1) / 1 = -2 by norm_num,
    Real.Gamma_two]
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha.le, Real.rpow_natCast]
  simp [one_div]

/-- `∫_{s>0} e^{-as}(s+C) ds = 1/a² + C/a`. -/
theorem integral_exp_neg_mul_linear_Ioi {a C : ℝ} (ha : 0 < a) :
    ∫ s in Set.Ioi (0 : ℝ), Real.exp (-a * s) * (s + C) = 1 / a ^ 2 + C / a := by
  have hcongr : ∀ s ∈ Set.Ioi (0 : ℝ),
      Real.exp (-a * s) * (s + C) = s * Real.exp (-a * s) + C * Real.exp (-a * s) := by
    intro s _; ring
  have hint1 : MeasureTheory.IntegrableOn (fun s : ℝ => s * Real.exp (-a * s))
      (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Integrable.of_integral_ne_zero ?_
    rw [integral_id_mul_exp_neg_Ioi ha]
    positivity
  have hint2 : MeasureTheory.IntegrableOn (fun s : ℝ => C * Real.exp (-a * s))
      (Set.Ioi (0 : ℝ)) := (exp_neg_integrableOn_Ioi 0 ha).const_mul C
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
    MeasureTheory.integral_add hint1 hint2, integral_id_mul_exp_neg_Ioi ha,
    MeasureTheory.integral_const_mul, integral_exp_neg_mul_Ioi' ha]
  simp
  ring

/-- Integrability of the majorant. -/
theorem integrableOn_exp_neg_mul_linear {a C : ℝ} (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp (-a * s) * (s + C))
      (Set.Ioi (0 : ℝ)) := by
  have hcongr : ∀ s ∈ Set.Ioi (0 : ℝ),
      Real.exp (-a * s) * (s + C) = s * Real.exp (-a * s) + C * Real.exp (-a * s) := by
    intro s _; ring
  have hint1 : MeasureTheory.IntegrableOn (fun s : ℝ => s * Real.exp (-a * s))
      (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.Integrable.of_integral_ne_zero ?_
    rw [integral_id_mul_exp_neg_Ioi ha]
    positivity
  have hint2 : MeasureTheory.IntegrableOn (fun s : ℝ => C * Real.exp (-a * s))
      (Set.Ioi (0 : ℝ)) := (exp_neg_integrableOn_Ioi 0 ha).const_mul C
  exact (MeasureTheory.integrableOn_congr_fun (hcongr) measurableSet_Ioi).mpr (hint1.add hint2)

/-- **THE SHARP TRIVIAL BOUND.**  `∑_{p≤Y} log p·p^{-1-a} ≤ 1/a + (log 4 + 4)`, with the
coefficient of `1/a` exactly `1`: Mertens I through `p^{-a} = a∫_{log p}^∞ e^{-as} ds`. -/
theorem sum_log_rpow_le {Y : ℕ} {a : ℝ} (ha : 0 < a) :
    ∑ p ∈ primesUpTo Y, Real.log (p : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - a)
      ≤ 1 / a + (Real.log 4 + 4) := by
  classical
  set C : ℝ := Real.log 4 + 4 with hC
  have hC0 : (0 : ℝ) ≤ C := by
    have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    rw [hC]; linarith
  set g : ℕ → ℝ → ℝ := fun p s =>
    (Set.Ioi (Real.log (p : ℝ))).indicator (fun s => Real.exp (-a * s)) s * (Real.log (p : ℝ) / p)
    with hg
  have hterm : ∀ p ∈ primesUpTo Y,
      (∫ s in Set.Ioi (0 : ℝ), g p s) = Real.log (p : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - a) / a := by
    intro p hp
    have hpp : p.Prime := (mem_primesUpTo.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    have hinter : Set.Ioi (0 : ℝ) ∩ Set.Ioi (Real.log (p : ℝ)) = Set.Ioi (Real.log (p : ℝ)) := by
      rw [Set.inter_eq_right]
      exact Set.Ioi_subset_Ioi hlogp
    rw [hg]
    simp only
    rw [MeasureTheory.integral_mul_const, MeasureTheory.setIntegral_indicator measurableSet_Ioi,
      hinter, integral_exp_neg_mul_Ioi' ha]
    have hexp : Real.exp (-a * Real.log (p : ℝ)) = (p : ℝ) ^ (-a) := by
      rw [Real.rpow_def_of_pos hppos]; ring_nf
    have hsplit : (p : ℝ) ^ (-(1 : ℝ) - a) = (p : ℝ) ^ (-a) * (p : ℝ)⁻¹ := by
      rw [show -(1 : ℝ) - a = (-a) + (-1 : ℝ) by ring, Real.rpow_add hppos, Real.rpow_neg_one]
    rw [hexp, hsplit]
    field_simp
  have hint : ∀ p ∈ primesUpTo Y, MeasureTheory.IntegrableOn (g p) (Set.Ioi (0 : ℝ)) := by
    intro p _
    refine MeasureTheory.Integrable.mul_const ?_ _
    exact (exp_neg_integrableOn_Ioi 0 ha).indicator measurableSet_Ioi
  have hswap : (∫ s in Set.Ioi (0 : ℝ), ∑ p ∈ primesUpTo Y, g p s)
      = ∑ p ∈ primesUpTo Y, ∫ s in Set.Ioi (0 : ℝ), g p s :=
    MeasureTheory.integral_finsetSum _ hint
  -- Mertens I bounds the integrand
  have hbound : ∀ s ∈ Set.Ioi (0 : ℝ),
      ∑ p ∈ primesUpTo Y, g p s ≤ Real.exp (-a * s) * (s + C) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hexp0 : (0 : ℝ) < Real.exp (-a * s) := Real.exp_pos _
    set N : ℕ := ⌊Real.exp s⌋₊ with hN
    have hexps : (1 : ℝ) ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
    have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hexps)
    -- drop the primes above `N`, they carry indicator `0`
    have hstep : ∀ p ∈ primesUpTo Y,
        g p s ≤ (if p ≤ N then Real.exp (-a * s) * (Real.log (p : ℝ) / p) else 0) := by
      intro p hp
      have hpp : p.Prime := (mem_primesUpTo.mp hp).1
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hmass : 0 ≤ Real.log (p : ℝ) / (p : ℝ) := by
        have : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
        positivity
      by_cases hle : p ≤ N
      · simp only [hle, if_true, hg]
        rcases le_or_gt s (Real.log (p : ℝ)) with hsl | hsl
        · have : (Set.Ioi (Real.log (p : ℝ))).indicator (fun s => Real.exp (-a * s)) s = 0 := by
            refine Set.indicator_of_notMem ?_ _
            simp only [Set.mem_Ioi]
            linarith
          rw [this, zero_mul]
          positivity
        · have : (Set.Ioi (Real.log (p : ℝ))).indicator (fun s => Real.exp (-a * s)) s
              = Real.exp (-a * s) := Set.indicator_of_mem hsl _
          rw [this]
      · -- `p > N = ⌊e^s⌋₊` forces `s ≤ log p`, so the indicator vanishes
        have hpgt : Real.exp s < (p : ℝ) := by
          have h1 : Real.exp s < (N : ℝ) + 1 := Nat.lt_floor_add_one _
          have h2 : (N : ℝ) + 1 ≤ (p : ℝ) := by
            have : N + 1 ≤ p := by omega
            exact_mod_cast this
          linarith
        have hsl : s ≤ Real.log (p : ℝ) := by
          have := Real.log_le_log (Real.exp_pos s) hpgt.le
          rwa [Real.log_exp] at this
        simp only [hle, if_false, hg]
        have : (Set.Ioi (Real.log (p : ℝ))).indicator (fun s => Real.exp (-a * s)) s = 0 := by
          refine Set.indicator_of_notMem ?_ _
          simp only [Set.mem_Ioi]
          linarith
        rw [this, zero_mul]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    have hfilter : ∑ p ∈ primesUpTo Y,
        (if p ≤ N then Real.exp (-a * s) * (Real.log (p : ℝ) / p) else 0)
        = ∑ p ∈ (primesUpTo Y).filter (fun p => p ≤ N),
            Real.exp (-a * s) * (Real.log (p : ℝ) / p) := by
      rw [Finset.sum_filter]
    rw [hfilter]
    have hsubset : (primesUpTo Y).filter (fun p => p ≤ N) ⊆ primesUpTo N := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hp.1).1, hp.2⟩
    have hmono : ∑ p ∈ (primesUpTo Y).filter (fun p => p ≤ N),
          Real.exp (-a * s) * (Real.log (p : ℝ) / p)
        ≤ ∑ p ∈ primesUpTo N, Real.exp (-a * s) * (Real.log (p : ℝ) / p) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
      intro p hp _
      have hpp : p.Prime := (mem_primesUpTo.mp hp).1
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
      positivity
    refine le_trans hmono ?_
    rw [← Finset.mul_sum]
    have hmert : ∑ p ∈ primesUpTo N, Real.log (p : ℝ) / (p : ℝ) ≤ s + C := by
      have h := sum_log_div_primesUpTo_le (X := N) hN1
      have hlogN : Real.log (N : ℝ) ≤ s := by
        have h1 : (N : ℝ) ≤ Real.exp s := Nat.floor_le (by positivity)
        have := Real.log_le_log (by exact_mod_cast hN1) h1
        rwa [Real.log_exp] at this
      rw [hC]; linarith
    exact mul_le_mul_of_nonneg_left hmert hexp0.le
  -- assemble
  have hintsum : MeasureTheory.IntegrableOn (fun s => ∑ p ∈ primesUpTo Y, g p s)
      (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.integrable_finset_sum _ hint
  have hle : (∫ s in Set.Ioi (0 : ℝ), ∑ p ∈ primesUpTo Y, g p s)
      ≤ ∫ s in Set.Ioi (0 : ℝ), Real.exp (-a * s) * (s + C) := by
    refine MeasureTheory.setIntegral_mono_on hintsum (integrableOn_exp_neg_mul_linear ha)
      measurableSet_Ioi hbound
  rw [hswap] at hle
  rw [integral_exp_neg_mul_linear_Ioi (a := a) (C := C) ha] at hle
  have hsumeq : ∑ p ∈ primesUpTo Y, (∫ s in Set.Ioi (0 : ℝ), g p s)
      = (∑ p ∈ primesUpTo Y, Real.log (p : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - a)) / a := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl hterm
  rw [hsumeq, div_le_iff₀ ha] at hle
  have : (1 / a ^ 2 + C / a) * a = 1 / a + C := by field_simp
  linarith [this ▸ hle]

/-- **THE TRIVIAL SLICE BOUND, SHARP.**  `‖slice‖ ≤ (δ+w)^{-1} + (log 4 + 4)`, with coefficient `1`:
absolute values everywhere, `sum_log_rpow_le` for the resulting real series. -/
theorem norm_logWeightedSlice_le_trivial {X : ℕ} (hX : 2 ≤ X) (v : ℝ) (Y : ℕ) {w : ℝ}
    (hw : 0 ≤ w) :
    ‖logWeightedSlice v X Y w‖ ≤ ((Real.log (X : ℝ))⁻¹ + w)⁻¹ + (Real.log 4 + 4) := by
  classical
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  set a : ℝ := (Real.log (X : ℝ))⁻¹ + w with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have hnorm : ‖logWeightedSlice v X Y w‖
      ≤ ∑ p ∈ primesUpTo Y, Real.log (p : ℝ) * (p : ℝ) ^ (-(1 : ℝ) - a) := by
    rw [logWeightedSlice]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum ?_
    intro p hp
    have hpp : p.Prime := (mem_primesUpTo.mp hp).1
    have hppos : 0 < p := hpp.pos
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    have hexp : (-(1 : ℝ) - (Real.log (X : ℝ))⁻¹ - w) = -(1 : ℝ) - a := by rw [ha]; ring
    rw [norm_mul, RCLike.norm_conj, norm_archimedeanTwist hppos v, one_mul, Complex.norm_real,
      Real.norm_eq_abs, hexp, abs_of_nonneg (by positivity)]
  simpa [one_div] using le_trans hnorm (sum_log_rpow_le (Y := Y) ha0)

/-- **The cap clause alone is the remaining `ζ'/ζ` input, sub-unit band.**  The `w ≥ T` half of
`SliceBoundSmall` is a *theorem* (`sum_log_rpow_le`); only `w ≤ T` needs cancellation, because there
the trivial bound gives `1/δ = log X` while the clause asks for `1/|v|`. -/
def SliceCapSmall (K : ℝ) : Prop :=
  ∀ (X Y : ℕ) (v : ℝ), 1048576 ≤ X → sliceCut X ≤ Y → 0 < |v| → |v| ≤ 1 →
    ∀ w ∈ Set.Icc (0 : ℝ) (max |v| (Real.log (X : ℝ))⁻¹),
      ‖logWeightedSlice v X Y w‖ ≤ (max |v| (Real.log (X : ℝ))⁻¹)⁻¹ + K

/-- The cap-band cutoff for the **moderate** band, at exponent `9`.

`(sliceT9 X v)⁻¹ = min ((log(|v|+16))^9) (log X)` — the `log X` side is what the *trivial* bound
`norm_logWeightedSlice_le_trivial` delivers, the `(log(|v|+16))^9` side is what the de la Vallée
Poussin bound `ElliottZetaModerate.exists_moderate_logDeriv_bound` delivers.  Taking the `max` of
the two reciprocals means each branch is covered by exactly one of them; see
`ElliottSliceCapModerate.exists_sliceCapModerate9`.

The exponent is `9` rather than `1` because the in-repo zero-free region
(`PNTPort.ZetaZeroFree9`) is `σ ≥ 1 − A/(log|t|)^9`.  It costs an absolute factor `9` in the
`log(1/T)` main term and nothing else. -/
def sliceT9 (X : ℕ) (v : ℝ) : ℝ :=
  max ((Real.log (|v| + 16)) ^ (9 : ℕ))⁻¹ (Real.log (X : ℝ))⁻¹

/-- **The cap clause alone, moderate band, at exponent 9 and with a multiplicative constant.**

The constant `C` is *forced*: in the branch `(log(|v|+16))^9 ≤ log X` the trivial bound (which
gives `log X`) is too weak, and the dVP bound comes with a constant `C₀ > 1` that cannot be
removed.  It is *free* at the consumer, because the cap band has length `sliceT9 X v`, so
`∫₀^T (C·T⁻¹ + K) = C + K·T`: a multiplicative constant in the cap band is an additive constant
in the integral. -/
def SliceCapModerate9 (C K : ℝ) : Prop :=
  ∀ (X Y : ℕ) (v : ℝ), 1048576 ≤ X → sliceCut X ≤ Y → 1 < |v| →
    ∀ w ∈ Set.Icc (0 : ℝ) (sliceT9 X v),
      ‖logWeightedSlice v X Y w‖ ≤ C * (sliceT9 X v)⁻¹ + K

/-- `sliceT9 X v ≤ 1` for `X ≥ 2²⁰`: both branches of the `max` are reciprocals of reals `≥ 1`
(`(log(|v|+16))^9 ≥ (log 16)^9 ≥ 1` and `log X ≥ 1`). -/
theorem sliceT9_le_one {X : ℕ} (hX : 1048576 ≤ X) (v : ℝ) : sliceT9 X v ≤ 1 := by
  have hXR : (1048576 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX1 : 1 ≤ Real.log (X : ℝ) := by
    have h3 : Real.log 3 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) (by linarith)
    have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (Real.exp_pos 1) hexp
    rw [Real.log_exp] at this
    linarith
  have hL : (1 : ℝ) ≤ Real.log (|v| + 16) := by
    have h16 : (16 : ℝ) ≤ |v| + 16 := by linarith [abs_nonneg v]
    have hmono := Real.log_le_log (by norm_num : (0:ℝ) < 16) h16
    have he : (1 : ℝ) ≤ Real.log 16 := by
      have hexp : Real.exp 1 < 16 := by linarith [Real.exp_one_lt_d9]
      have := Real.log_lt_log (Real.exp_pos 1) hexp
      rw [Real.log_exp] at this; linarith
    linarith
  have hpow : (1 : ℝ) ≤ (Real.log (|v| + 16)) ^ (9 : ℕ) := one_le_pow₀ hL
  rw [sliceT9]
  refine max_le ?_ ?_
  · rw [inv_le_one_iff₀]; exact Or.inr hpow
  · rw [inv_le_one_iff₀]; exact Or.inr hlogX1

/-- **The cap clause alone, moderate band.** -/
def SliceCapModerate (K : ℝ) : Prop :=
  ∀ (X Y : ℕ) (v : ℝ), 1048576 ≤ X → sliceCut X ≤ Y → 1 < |v| →
    ∀ w ∈ Set.Icc (0 : ℝ) (max (Real.log (|v| + 16))⁻¹ (Real.log (X : ℝ))⁻¹),
      ‖logWeightedSlice v X Y w‖ ≤ (max (Real.log (|v| + 16))⁻¹ (Real.log (X : ℝ))⁻¹)⁻¹ + K

/-- **HALF OF THE SUB-UNIT INPUT IS DISCHARGED.**  `SliceBoundSmall` follows from the cap clause
alone. -/
theorem sliceBoundSmall_of_cap {K : ℝ} (hK : 0 ≤ K) (h : SliceCapSmall K) :
    SliceBoundSmall (K + (Real.log 4 + 4)) := by
  intro X Y v hX hY hv0 hv1
  have hX2 : 2 ≤ X := by omega
  have hC0 : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have := h X Y v hX hY hv0 hv1 w hw
    linarith
  · have hδT : (Real.log (X : ℝ))⁻¹ ≤ max |v| (Real.log (X : ℝ))⁻¹ := le_max_right _ _
    have hXR2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
    have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
    have hδpos : (0 : ℝ) < (Real.log (X : ℝ))⁻¹ := by positivity
    have hw0 : 0 < w := lt_of_lt_of_le hδpos (le_trans hδT hw.1)
    have htriv := norm_logWeightedSlice_le_trivial hX2 v Y hw0.le
    have hmono : ((Real.log (X : ℝ))⁻¹ + w)⁻¹ ≤ w⁻¹ := inv_anti₀ hw0 (by linarith)
    linarith

/-- **HALF OF THE MODERATE INPUT IS DISCHARGED.** -/
theorem sliceBoundModerate_of_cap {K : ℝ} (hK : 0 ≤ K) (h : SliceCapModerate K) :
    SliceBoundModerate (K + (Real.log 4 + 4)) := by
  intro X Y v hX hY hv1
  have hX2 : 2 ≤ X := by omega
  have hC0 : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have := h X Y v hX hY hv1 w hw
    linarith
  · have hδT : (Real.log (X : ℝ))⁻¹
        ≤ max (Real.log (|v| + 16))⁻¹ (Real.log (X : ℝ))⁻¹ := le_max_right _ _
    have hXR2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
    have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
    have hδpos : (0 : ℝ) < (Real.log (X : ℝ))⁻¹ := by positivity
    have hw0 : 0 < w := lt_of_lt_of_le hδpos (le_trans hδT hw.1)
    have htriv := norm_logWeightedSlice_le_trivial hX2 v Y hw0.le
    have hmono : ((Real.log (X : ℝ))⁻¹ + w)⁻¹ ≤ w⁻¹ := inv_anti₀ hw0 (by linarith)
    linarith

/-! ### The moderate band at exponent 9 (lap 116) -/

/-- **The `ζ'/ζ` input, moderate band, at exponent 9 with a multiplicative cap constant.** -/
def SliceBoundModerate9 (C K : ℝ) : Prop :=
  ∀ (X Y : ℕ) (v : ℝ), 1048576 ≤ X → sliceCut X ≤ Y → 1 < |v| →
    (∀ w ∈ Set.Icc (0 : ℝ) (sliceT9 X v),
        ‖logWeightedSlice v X Y w‖ ≤ C * (sliceT9 X v)⁻¹ + K) ∧
    (∀ w ∈ Set.Icc (sliceT9 X v) 1, ‖logWeightedSlice v X Y w‖ ≤ w⁻¹ + K)

/-- The harmonic clause of the moderate-9 input is `sum_log_rpow_le` (lap 106, coefficient
exactly `1`), so the whole input follows from the cap clause. -/
theorem sliceBoundModerate9_of_cap {C K : ℝ} (hK : 0 ≤ K) (h : SliceCapModerate9 C K) :
    SliceBoundModerate9 C (K + (Real.log 4 + 4)) := by
  intro X Y v hX hY hv1
  have hX2 : 2 ≤ X := by omega
  have hC0 : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have := h X Y v hX hY hv1 w hw
    linarith
  · have hδT : (Real.log (X : ℝ))⁻¹ ≤ sliceT9 X v := le_max_right _ _
    have hXR2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX2
    have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
    have hδpos : (0 : ℝ) < (Real.log (X : ℝ))⁻¹ := by positivity
    have hw0 : 0 < w := lt_of_lt_of_le hδpos (le_trans hδT hw.1)
    have htriv := norm_logWeightedSlice_le_trivial hX2 v Y hw0.le
    have hmono : ((Real.log (X : ℝ))⁻¹ + w)⁻¹ ≤ w⁻¹ := inv_anti₀ hw0 (by linarith)
    linarith

/-- **The analytic input, moderate band, at exponent 9.**  The coefficient `9` is exactly
`log(1/sliceT9) ≤ log ((log(|v|+16))^9) = 9·log log(|v|+16)`; it comes from the exponent in the
in-repo zero-free region `PNTPort.ZetaZeroFree9`, and nothing else in the chain contributes to it
(the harmonic band has coefficient exactly `1`, lap 106). -/
def DampedSeriesBoundModerate9 (K : ℝ) : Prop :=
  ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ (X Y : ℕ) (v : ℝ), X₀ ≤ X → X ≤ Y → 1 < |v| →
    ‖dampedPrefix v X Y‖ ≤ 9 * Real.log (Real.log (|v| + 16)) + K

/-- **(c′-II-a) REDUCED TO THE MODERATE-9 SLICE BOUND.** -/
theorem dampedSeriesBoundModerate9_of_sliceBound {C K : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (h : SliceBoundModerate9 C K) :
    DampedSeriesBoundModerate9 (C + K + tailCost + cutCost) := by
  refine ⟨1048576, by norm_num, ?_⟩
  intro X Y v hX3 hXY hv1
  have hX : 2 ≤ X := by omega
  have hXR : (3 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 3 ≤ X)
  have hlogX : 1 < Real.log (X : ℝ) := by
    have h3 : Real.log 3 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) hXR
    have : (1 : ℝ) < Real.log 3 := by
      have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      have := Real.log_lt_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    linarith
  have hδ0 : 0 < (Real.log (X : ℝ))⁻¹ := by positivity
  have hL : (1 : ℝ) < Real.log (|v| + 16) := by
    have h17 : (17 : ℝ) ≤ |v| + 16 := by linarith
    have hlog17 : Real.log 17 ≤ Real.log (|v| + 16) := Real.log_le_log (by norm_num) h17
    have : (1 : ℝ) < Real.log 17 := by
      have hexp : Real.exp 1 < 17 := by linarith [Real.exp_one_lt_d9]
      have := Real.log_lt_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    linarith
  have hL0 : 0 < Real.log (|v| + 16) := by linarith
  set a : ℝ := (Real.log (|v| + 16)) ^ (9 : ℕ) with ha
  have ha1 : (1 : ℝ) < a := one_lt_pow₀ hL (by norm_num)
  have ha0 : 0 < a := by linarith
  set T : ℝ := sliceT9 X v with hT
  have hδT : (Real.log (X : ℝ))⁻¹ ≤ T := le_max_right _ _
  have hLT : a⁻¹ ≤ T := le_max_left _ _
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hLT
  have hT1 : T ≤ 1 := sliceT9_le_one hX3 v
  set Y' : ℕ := max Y (sliceCut X) with hY'
  have hXY' : X ≤ Y' := le_trans hXY (le_max_left _ _)
  obtain ⟨hcap, hharm⟩ := h X Y' v hX3 (le_max_right _ _) hv1
  have hmain0 := norm_dampedPrefix_le_of_slice_le_const hX v Y' hδT hT1 hK hC hcap hharm
  have htr := norm_dampedPrefix_transfer hX v Y Y' hXY hXY'
  have hmain : ‖dampedPrefix v X Y‖ ≤ C + Real.log (1 / T) + K + tailCost + cutCost := by
    rw [cutCost] at *; linarith
  have hlogmono : Real.log (1 / T) ≤ 9 * Real.log (Real.log (|v| + 16)) := by
    have hstep : Real.log (1 / T) ≤ Real.log a := by
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ hT0]
      have hid : a⁻¹ * a = 1 := by field_simp
      nlinarith [hLT, ha0]
    have hpow : Real.log a = 9 * Real.log (Real.log (|v| + 16)) := by
      rw [ha, Real.log_pow]; norm_num
    linarith [hpow ▸ hstep]
  linarith [hmain, hlogmono]

end

end NormalNumbers.ElliottDamped