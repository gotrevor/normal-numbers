import NormalNumbers.ElliottPrimePower
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The arithmetic bridge: the slice is `−ζ'/ζ` up to `O(1)` (lap 110)

`logWeightedSlice v X Y w` is the log-weighted prime sum at abscissa `s = (1+δ+w) + iv`; mathlib's
`L ↗Λ s = −ζ'/ζ(s)` is the same sum over all prime powers, untruncated.  This file identifies the
slice with a partial sum of `L ↗Λ`, term by term — the point being that the campaign's
`archimedeanTwist v p = p^{iv}` conjugated is exactly the `p^{-iv}` hidden in `p^{-s}`.

The two error terms (primes past `Y`, prime powers with `j ≥ 2`) are `ElliottDamped.logTail_le`
(lap 105) and `ElliottPrimePower.sum_pairs_le` (lap 109); assembling them is the next lap.
-/

open Finset ArithmeticFunction

namespace NormalNumbers.ElliottBridge

open NormalNumbers.ElliottDamped NormalNumbers.ElliottPrimePower Erdos67b.PrimeEstimates
open Erdos67b NormalNumbers.ElliottZetaOmegaPretentious

noncomputable section

/-- The abscissa of the `w`-slice: `s = (1 + δ + w) + iv` with `δ = 1/log X`. -/
noncomputable def sliceAbscissa (X : ℕ) (w v : ℝ) : ℂ :=
  ((1 + (Real.log (X : ℝ))⁻¹ + w : ℝ) : ℂ) + Complex.I * (v : ℂ)

theorem sliceAbscissa_re {X : ℕ} (w v : ℝ) :
    (sliceAbscissa X w v).re = 1 + (Real.log (X : ℝ))⁻¹ + w := by
  simp only [sliceAbscissa, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im]
  ring

theorem sliceAbscissa_im {X : ℕ} (w v : ℝ) : (sliceAbscissa X w v).im = v := by
  simp only [sliceAbscissa, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re]
  ring

/-- The conjugated Archimedean twist is `p^{-iv}` in exponential form. -/
theorem conj_archimedeanTwist {p : ℕ} (hp : 0 < p) (v : ℝ) :
    (starRingEnd ℂ) (archimedeanTwist v p)
      = Complex.exp (-(Complex.I * (v : ℂ) * ((Real.log (p : ℝ) : ℝ) : ℂ))) := by
  rw [archimedeanTwist_eq_exp hp v, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- **THE TERM IDENTITY.**  At `s = σ + iv` with `σ` real, the `p`-th term of `L ↗Λ` is exactly the
`p`-th summand of the slice. -/
theorem term_eq_slice_summand {p : ℕ} (hp : p.Prime) (σ v : ℝ) :
    LSeries.term (fun n => ((vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + Complex.I * (v : ℂ)) p
      = (starRingEnd ℂ) (archimedeanTwist v p)
          * (((Real.log (p : ℝ)) * (p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hpC : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp0.ne'
  rw [LSeries.term_of_ne_zero (by omega : p ≠ 0)]
  rw [vonMangoldt_apply_prime hp]
  -- split `p^{-s}` into its real and Archimedean parts
  have hsplit : ((p : ℕ) : ℂ) ^ ((σ : ℂ) + Complex.I * (v : ℂ))
      = (((p : ℝ) ^ σ : ℝ) : ℂ) * Complex.exp (Complex.I * (v : ℂ) * ((Real.log (p : ℝ) : ℝ) : ℂ))
      := by
    rw [Complex.cpow_add _ _ hpC]
    congr 1
    · rw [Complex.ofReal_cpow hpR.le]
      norm_cast
    · rw [Complex.cpow_def_of_ne_zero hpC]
      congr 1
      rw [← Complex.natCast_log]
      ring
  rw [hsplit, conj_archimedeanTwist hp0 v]
  have hne : Complex.exp (Complex.I * (v : ℂ) * ((Real.log (p : ℝ) : ℝ) : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  have hpow : (((p : ℝ) ^ σ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hpR.le]
  rw [Complex.exp_neg]
  field_simp
  rw [Complex.ofReal_cpow hpR.le (-σ)]
  push_cast
  rw [Complex.cpow_neg]
  field_simp

/-- **THE SLICE IS A PARTIAL SUM OF `L ↗Λ`.**  Exactly, with no error: the truncation and the
prime powers are the *missing* terms, bounded in the next lap. -/
theorem slice_eq_sum_term (v : ℝ) (X Y : ℕ) (w : ℝ) :
    logWeightedSlice v X Y w
      = ∑ p ∈ primesUpTo Y,
          LSeries.term (fun n => ((vonMangoldt n : ℝ) : ℂ)) (sliceAbscissa X w v) p := by
  classical
  rw [logWeightedSlice]
  refine (Finset.sum_congr rfl ?_).symm
  intro p hp
  have hpp : p.Prime := (mem_primesUpTo.mp hp).1
  have hterm := term_eq_slice_summand hpp (1 + (Real.log (X : ℝ))⁻¹ + w) v
  rw [show sliceAbscissa X w v
      = ((1 + (Real.log (X : ℝ))⁻¹ + w : ℝ) : ℂ) + Complex.I * (v : ℂ) from rfl]
  rw [hterm]
  congr 2
  rw [show -(1 : ℝ) - (Real.log (X : ℝ))⁻¹ - w = -(1 + (Real.log (X : ℝ))⁻¹ + w) by ring]

/-! ### The missing terms: primes past `Y`, and prime powers -/

/-- A prime power is recovered from its least prime factor and that factor's multiplicity, and the
multiplicity is `≥ 2` unless the number is itself prime. -/
theorem primePow_decomp {n : ℕ} (h : IsPrimePow n) (hnp : ¬ n.Prime) :
    (n.minFac).Prime ∧ (n.minFac) ^ (n.factorization n.minFac) = n
      ∧ 2 ≤ n.factorization n.minFac := by
  obtain ⟨q, k, hq, hk, rfl⟩ := h
  have hqp : q.Prime := Nat.prime_iff.mpr hq
  have hk0 : k ≠ 0 := by omega
  have hmin : (q ^ k).minFac = q := by
    rw [Nat.pow_minFac hk0, hqp.minFac_eq]
  have hfac : (q ^ k).factorization q = k := by
    rw [Nat.factorization_pow, hqp.factorization]
    simp
  refine ⟨by rwa [hmin], by rw [hmin, hfac], ?_⟩
  rw [hmin, hfac]
  by_contra hcon
  have hk1 : k = 1 := by omega
  rw [hk1, pow_one] at hnp
  exact hnp hqp
/-- The `p^j`-th term of `∑ Λ n·n^{-σ}`, in the pair shape `sum_pairs_le` consumes. -/
theorem term_primePow {p j : ℕ} (hp : p.Prime) (hj : j ≠ 0) (σ : ℝ) :
    (vonMangoldt (p ^ j) : ℝ) * ((p ^ j : ℕ) : ℝ) ^ (-σ)
      = Real.log (p : ℝ) * (p : ℝ) ^ (-(σ * j)) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hΛ : (vonMangoldt (p ^ j) : ℝ) = Real.log (p : ℝ) := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hj,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [hΛ]
  congr 1
  rw [show (((p ^ j : ℕ) : ℝ)) = ((p : ℝ)) ^ (j : ℕ) by push_cast; ring,
    ← Real.rpow_natCast (p : ℝ) j, ← Real.rpow_mul hp0.le]
  congr 1
  ring

/-- **THE MISSING TERMS ARE `O(1)`.**  Every finite set of indices *outside* `primesUpTo Y`
contributes at most `1 + ppCost` to `∑ Λ n·n^{-σ}`, uniformly: the primes past `Y` by
`logTail_le` (lap 105) and the higher prime powers by `sum_pairs_le` (lap 109). -/
theorem sum_complement_le {X Y : ℕ} (hX : 1048576 ≤ X) (hY : sliceCut X ≤ Y) {σ : ℝ}
    (hσ : 1 + (Real.log (X : ℝ))⁻¹ ≤ σ) (G : Finset ℕ) (hG : ∀ n ∈ G, n ∉ primesUpTo Y) :
    ∑ n ∈ G, (vonMangoldt n) * (n : ℝ) ^ (-σ) ≤ 1 + ppCost := by
  classical
  set a : ℝ := σ - 1 with ha
  have haδ : (Real.log (X : ℝ))⁻¹ ≤ a := by rw [ha]; linarith
  have hσ1 : (1 : ℝ) ≤ σ := by
    have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 2 ≤ X)
    have : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
    have : 0 < (Real.log (X : ℝ))⁻¹ := by positivity
    linarith
  have hexp : -σ = -(1 : ℝ) - a := by rw [ha]; ring
  -- split into primes and the rest
  rw [← Finset.sum_filter_add_sum_filter_not G Nat.Prime]
  have hprime : ∑ n ∈ G.filter Nat.Prime, (vonMangoldt n) * (n : ℝ) ^ (-σ) ≤ 1 := by
    have hrw : ∑ n ∈ G.filter Nat.Prime, (vonMangoldt n) * (n : ℝ) ^ (-σ)
        = ∑ n ∈ G.filter Nat.Prime, Real.log (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) - a) := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      have hnp : n.Prime := (Finset.mem_filter.mp hn).2
      rw [vonMangoldt_apply_prime hnp, hexp]
    rw [hrw]
    set Z : ℕ := G.sup id with hZ
    have hsub : G.filter Nat.Prime ⊆ primesInInterval Y Z := by
      intro n hn
      rw [Finset.mem_filter] at hn
      have hnp : n.Prime := hn.2
      have hnotmem := hG n hn.1
      have hgt : Y < n := by
        by_contra hcon
        exact hnotmem (mem_primesUpTo.mpr ⟨hnp, by omega⟩)
      have hle : n ≤ Z := Finset.le_sup (f := id) hn.1
      exact mem_primesInInterval.mpr ⟨hgt, hle, hnp⟩
    have hnn : ∀ n ∈ primesInInterval Y Z, n ∉ G.filter Nat.Prime →
        0 ≤ Real.log (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) - a) := by
      intro n hn _
      have hnp : n.Prime := (mem_primesInInterval.mp hn).2.2
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnp.one_le
      have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg this
      positivity
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn) ?_
    exact logTail_le hX hY haδ
  have hrest : ∑ n ∈ G.filter (fun n => ¬ n.Prime), (vonMangoldt n) * (n : ℝ) ^ (-σ)
      ≤ ppCost := by
    set H : Finset ℕ := G.filter (fun n => ¬ n.Prime) with hH
    set H' : Finset ℕ := H.filter IsPrimePow with hH'
    have hzero : ∑ n ∈ H', (vonMangoldt n) * (n : ℝ) ^ (-σ)
        = ∑ n ∈ H, (vonMangoldt n) * (n : ℝ) ^ (-σ) := by
      refine Finset.sum_filter_of_ne (fun n _ hne => ?_)
      by_contra hcon
      rw [vonMangoldt_eq_zero_iff.mpr hcon, zero_mul] at hne
      exact hne rfl
    rw [← hzero]
    set φ : ℕ → ℕ × ℕ := fun n => (n.minFac, n.factorization n.minFac) with hφ
    have hdecomp : ∀ n ∈ H', (n.minFac).Prime ∧ (n.minFac) ^ (n.factorization n.minFac) = n
        ∧ 2 ≤ n.factorization n.minFac := by
      intro n hn
      rw [hH', Finset.mem_filter, hH, Finset.mem_filter] at hn
      exact primePow_decomp hn.2 hn.1.2
    have hinj : ∀ x ∈ H', ∀ y ∈ H', φ x = φ y → x = y := by
      intro x hx y hy hxy
      obtain ⟨-, hx2, -⟩ := hdecomp x hx
      obtain ⟨-, hy2, -⟩ := hdecomp y hy
      have hx3 : x = (φ x).1 ^ (φ x).2 := hx2.symm
      have hy3 : y = (φ y).1 ^ (φ y).2 := hy2.symm
      rw [hx3, hy3, hxy]
    have hterm : ∀ n ∈ H', (vonMangoldt n) * (n : ℝ) ^ (-σ)
        = Real.log (((φ n).1 : ℕ) : ℝ) * (((φ n).1 : ℕ) : ℝ) ^ (-(σ * (φ n).2)) := by
      intro n hn
      obtain ⟨hp, hpow, hj⟩ := hdecomp n hn
      have key := term_primePow (p := n.minFac) (j := n.factorization n.minFac) hp
        (by omega) σ
      rw [hpow] at key
      exact key
    rw [Finset.sum_congr rfl hterm]
    have himg := Finset.sum_image (g := φ) (s := H')
      (f := fun q : ℕ × ℕ => Real.log ((q.1 : ℕ) : ℝ) * ((q.1 : ℕ) : ℝ) ^ (-(σ * q.2)))
      (fun x hx y hy h => hinj x hx y hy h)
    rw [← himg]
    refine sum_pairs_le ?_ hσ1
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨n, hn, rfl⟩ := hq
    obtain ⟨hp, -, hj⟩ := hdecomp n hn
    exact ⟨hp.two_le, hj⟩
  linarith

end

end NormalNumbers.ElliottBridge
