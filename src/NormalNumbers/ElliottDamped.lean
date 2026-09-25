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

theorem sum_primesUpTo_split {f : ℕ → ℂ} {X Y : ℕ} (hXY : X ≤ Y) :
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

/-! ### The two soft inputs, reduced to the damped Dirichlet series -/

open NormalNumbers.ElliottArchBands

/-- **The analytic input, sub-unit band.**  The damped prime series is bounded by `log(1/|v|)` up
to an absolute constant.  This is the statement the `ζ'/ζ` route produces: the pole bound
`|ζ'/ζ(σ+w+iv)| ≤ min((δ+w)^{-1}, |v|^{-1})` fed into
`ElliottLogIntegral.integral_le_one_add_log` with `T = |v|`. -/
def DampedSeriesBoundSmall (K : ℝ) : Prop :=
  ∀ (X Y : ℕ) (v : ℝ), 2 ≤ X → X ≤ Y → 0 < |v| → |v| ≤ 1 →
    ‖dampedPrefix v X Y‖ ≤ Real.log (1 / |v|) + K

/-- **The analytic input, moderate band.**  Same route with `T = 1/(C log|v|)`, i.e. the de la
Vallée Poussin bound `|ζ'/ζ(σ+iv)| ≤ C log|v|` on `σ > 1`. -/
def DampedSeriesBoundModerate (K : ℝ) : Prop :=
  ∀ (X Y : ℕ) (v : ℝ), 2 ≤ X → X ≤ Y → 1 < |v| →
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
  refine ⟨2, le_rfl, ?_⟩
  intro X hX v hv0 hv1
  have hd := h X X v hX le_rfl hv0 hv1
  have hs := norm_archCorr_sub_dampedPrefix_le' hX v X le_rfl
  calc ‖archCorr v X‖ ≤ ‖archCorr v X - dampedPrefix v X X‖ + ‖dampedPrefix v X X‖ := by
        simpa [add_comm] using norm_le_norm_add_norm_sub' (archCorr v X) (dampedPrefix v X X)
    _ ≤ dampingCost + (Real.log (1 / |v|) + K) := by linarith
    _ = Real.log (1 / |v|) + (K + dampingCost) := by ring

/-- **(c′-II-a) FROM THE ANALYTIC INPUT.**  Same reduction on the moderate band. -/
theorem archCorrModerate_of_dampedSeriesBound {K : ℝ} (h : DampedSeriesBoundModerate K) :
    ArchCorrModerate (K + dampingCost) := by
  refine ⟨2, le_rfl, ?_⟩
  intro X hX v hv1
  have hd := h X X v hX le_rfl hv1
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

end

end NormalNumbers.ElliottDamped
