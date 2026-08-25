import NormalNumbers.CFAeNormal
import NormalNumbers.CFLogTail

/-!
# a.e. Khinchin-typicality (toward the image-Khinchin B6 stretch)

Goal: `∀ᵐ x ∂gaussMeasure, KhinchinTypical x` — the geometric mean of the CF
digits tends to Khinchin's constant `K₀` for a.e. `x`.  This is the missing
co-null set that, intersected with the affine-family co-null sets
(`CFAffineFamily.lean`), upgrades the B6 witness to be Khinchin-typical too.

## The reduction (why this is tractable without a general ergodic theorem)

By `khinchinTypical_iff_log_tendsto`, `KhinchinTypical x` is equivalent to the
log-average `(1/n) Σ_{i<n} log(a_i(x)) → log K₀`.  Split each digit-log at a
FIXED cutoff `K`:

  `Σ_{i<n} log a_i  =  Σ_{a=1}^{K} log a · #{i<n : a_i = a}  +  logBirkhoffSum K n x`,

where the tail `logBirkhoffSum K n x = Σ_{i<n} log(a_i)·1[a_i > K]` is exactly
the log-tail Birkhoff sum of `CFLogTail`.  Dividing by `n`:

* **bounded part** `Σ_{a≤K} log a · (blockCount (cfCylinder [a]) n x / n)` →
  `Σ_{a≤K} log a · γ([a]) = Σ_{k<K} logTailG k` a.e., a FINITE sum of the
  singleton-digit frequency limits `ae_orbit_freq [a]` (already proved).
* **tail part** `logBirkhoffSum K n x / n → ∫ logTailFn K dγ` a.e. — the one new
  analytic input (`ae_tail_average_tendsto`).

Their limits ADD to `(Σ_{k<K} logTailG k) + ∫ logTailFn K dγ = log K₀` EXACTLY
(`integral_logTailFn_eq_of_hasSum` with `HasSum logTailG (log K₀)`), for ANY
fixed `K` — no `K → ∞` limiting needed.  So the whole crux collapses onto the
single tail-average lemma.

## Status
`ae_digitCount_tendsto` (bounded-part leaf) is PROVED here.  The tail-average
lemma `ae_tail_average_tendsto` is the disclosed crux: it is the L²→a.e.
Borel–Cantelli argument (mirroring `ae_orbit_freq`) applied to `logBirkhoffSum`,
using a variance bound for the log-tail Birkhoff sum (to be built from the Gauss
mixing engine — `logTailFn K = Σ_{a>K} log a · 1_{cfCylinder [a]}` decomposes it
into the same two-point correlations behind `variance_blockCount_le`), plus the
MONOTONE gap-squeeze available because `logTailFn K ≥ 0`.  See `PENDING_WORK.md`.
-/

namespace NormalNumbers

open MeasureTheory Filter Set

/-- **Bounded-part leaf.**  For each digit value `a ≥ 1`, the frequency of digit
`a` among the first `n` CF digits converges a.e. to `γ([a])`.  Direct
specialization of `ae_orbit_freq` to the singleton word `v = [a]`. -/
theorem ae_digitCount_tendsto (a : ℕ) (ha : 1 ≤ a) :
    ∀ᵐ x ∂gaussMeasure,
      Tendsto (fun n => blockCount (cfCylinder [a]) n x / (n : ℝ)) atTop
        (nhds (gaussMeasure (cfCylinder [a])).toReal) := by
  refine ae_orbit_freq [a] (by simp) ?_
  intro b hb
  rw [List.mem_singleton] at hb
  subst hb
  exact ha

/-! ## Foundation bricks for the tail variance bound

`logTailFn K = Σ_{a>K} log a · 1_{cfCylinder [a]}`, so the second moment of
`logBirkhoffSum K n` expands into TWO-different-cylinder correlations
`γ(T^{-j}[a] ∩ T^{-j'}[b])`.  These two bricks generalize the single-cylinder
`gaussMeasureReal_pair_shift` / `abs_cov_pair_le` (`CFBlockFreq.lean`) to two
distinct cylinders, which is exactly what the log-tail variance sum needs. -/

/-- **Two-set pair invariance**: `γ(T^{-j}A ∩ T^{-(j+m)}B) = γ(A ∩ T^{-m}B)`.
Generalizes `gaussMeasureReal_pair_shift` to two distinct measurable sets. -/
theorem gaussMeasureReal_pair_shift₂ (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (j m : ℕ) :
    gaussMeasure.real ((gaussMap^[j]) ⁻¹' A ∩ (gaussMap^[j + m]) ⁻¹' B) =
      gaussMeasure.real (A ∩ (gaussMap^[m]) ⁻¹' B) := by
  have hmp := measurePreserving_gaussMap
  have hmm : MeasurableSet ((gaussMap^[m]) ⁻¹' B) := (measurable_gaussMap.iterate m) hB
  rw [preimage_iterate_add B j m, ← Set.preimage_inter]
  exact (hmp.iterate j).measureReal_preimage (hA.inter hmm).nullMeasurableSet

/-- **Aligned two-cylinder mixing** at gap `m ≥ 1`: for singleton digit words
`[a]`, `[b]`, the correlation `γ([a] ∩ T^{-m}[b])` deviates from `γ([a])·γ([b])`
by at most `(9/10)^{m-1}·4·|[b]|·γ([a])`.  Direct application of
`gaussMeasure_cylinder_mixing` with `v = [a]` and the arbitrary-set slot
`A = cfCylinder [b]`. -/
theorem abs_cov_two_cyl_le (a b : ℕ) (ha : 1 ≤ a) (m : ℕ) (hm : 1 ≤ m) :
    |(gaussMeasure (cfCylinder [a] ∩ (gaussMap^[m]) ⁻¹' cfCylinder [b])).toReal -
        (gaussMeasure (cfCylinder [a])).toReal * (gaussMeasure (cfCylinder [b])).toReal| ≤
      ((9 : ℝ) / 10) ^ (m - 1) * (4 * (volume (cfCylinder [b])).toReal) *
        (gaussMeasure (cfCylinder [a])).toReal := by
  have hposa : ∀ x ∈ [a], 1 ≤ x := by
    intro x hx; rw [List.mem_singleton] at hx; subst hx; exact ha
  obtain ⟨g, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hlen : ([a] : List ℕ).length + g = 1 + g := by simp
  have hmix := gaussMeasure_cylinder_mixing [a] hposa g
    (measurableSet_cfCylinder [b]) (cfCylinder_subset_Ioo [b])
  rw [hlen] at hmix
  simpa using hmix

/-- **The tail-average crux (disclosed).**  For a fixed cutoff `K`, the
normalized log-tail Birkhoff sum converges a.e. to the tail integral.  Route:
L²→a.e. Borel–Cantelli (as in `ae_orbit_freq`) via a variance bound for
`logBirkhoffSum K` from Gauss mixing, plus the monotone gap-squeeze
(`logBirkhoffSum K n x` is nondecreasing in `n`, since `logTailFn K ≥ 0`). -/
theorem ae_tail_average_tendsto (K : ℕ) :
    ∀ᵐ x ∂gaussMeasure,
      Tendsto (fun n => logBirkhoffSum K n x / (n : ℝ)) atTop
        (nhds (∫ y, logTailFn K y ∂gaussMeasure)) := by
  sorry

end NormalNumbers
