import NormalNumbers.PrimeModelPhaseAlgebra

/-!
# Theorem A, leg E5: the graded model phase contraction

Lap 6b of `KICKOFF-2026-09-22-multicutoff-lean.md`; spec `papers/ROUND2-multicutoff-fable.md` §2
("E5").  In the ungraded model every prime `p ∈ P` is seen by **all** `k` sites, so the model
expectation is `∏_p (1 + A/p)` with the fixed `A = ∑_{j<k} (z_j − 1)`.  In the graded model a
prime is seen only by the sites whose cutoff exceeds it: site `j` contributes to `p` iff
`p ≤ y_j`, and for a monotone schedule that is a **prefix** `{j : j < d_p}`.  So the model
expectation is `∏_p (1 + A_{d_p}/p)` with `A_m = ∑_{j < m} (z_j − 1)`.

Two features of the graded bound:

* `A_0 = 0`: a prime seen by no site contributes the factor `1` exactly.  More generally
  `A_m = 0` whenever every `z_j` with `j < m` is `1` — tiers above the least nontrivial site
  `j₀` neither help nor hurt, which is what makes the schedule free.
* The contraction `e^{−1/p}` is collected only from the primes that *do* see `j₀`.  Those are
  the primes of the good set `G` below, and they are the ones the headline's
  `S_P(2k, y_{j₀})` counts.

`Re A_m ≤ 0` always (each `z_j` is on the unit circle), so the primes outside `G` cost nothing
beyond the universal `p^{−2}` term.
-/

open Finset
open scoped BigOperators

namespace NormalNumbers.PrimeModel.PhaseAlgebra

/-- `A_m = ∑_{j < m} (z_j − 1)`, the phase defect seen by a prime that `m` sites reach. -/
noncomputable def prefixA {k : ℕ} (z : Fin k → ℂ) (m : ℕ) : ℂ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val < m), (z j - 1)

@[simp] theorem prefixA_zero {k : ℕ} (z : Fin k → ℂ) : prefixA z 0 = 0 := by
  simp [prefixA]

/-- A prime reached by no nontrivial site sees `A = 0`: the factor is exactly `1`. -/
theorem prefixA_eq_zero_of {k : ℕ} (z : Fin k → ℂ) {m : ℕ}
    (h : ∀ j : Fin k, j.val < m → z j = 1) : prefixA z m = 0 := by
  rw [prefixA]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [h j (Finset.mem_filter.1 hj).2, sub_self]

theorem prefixA_re_nonpos {k : ℕ} (z : Fin k → ℂ) (hz : ∀ j, ‖z j‖ = 1) (m : ℕ) :
    (prefixA z m).re ≤ 0 := by
  rw [prefixA, Complex.re_sum]
  refine Finset.sum_nonpos fun j _ => ?_
  have h1 : (z j).re ≤ ‖z j‖ := Complex.re_le_norm (z j)
  rw [hz j] at h1
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem prefixA_re_le_neg_one {k : ℕ} (z : Fin k → ℂ) (hz : ∀ j, ‖z j‖ = 1)
    {j₀ : Fin k} (hre : (z j₀).re ≤ 0) {m : ℕ} (hm : j₀.val < m) :
    (prefixA z m).re ≤ -1 := by
  classical
  rw [prefixA, Complex.re_sum]
  have hj₀ : j₀ ∈ Finset.univ.filter (fun j : Fin k => j.val < m) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hm⟩
  rw [← Finset.add_sum_erase _ _ hj₀]
  have h1 : (z j₀ - 1).re ≤ -1 := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have h2 : ∑ j ∈ (Finset.univ.filter (fun j : Fin k => j.val < m)).erase j₀, (z j - 1).re ≤ 0 := by
    refine Finset.sum_nonpos fun j _ => ?_
    have h3 : (z j).re ≤ ‖z j‖ := Complex.re_le_norm (z j)
    rw [hz j] at h3
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  linarith

theorem norm_prefixA_le {k : ℕ} (z : Fin k → ℂ) (hz : ∀ j, ‖z j‖ = 1) (m : ℕ) :
    ‖prefixA z m‖ ≤ 2 * (k : ℝ) := by
  classical
  calc ‖prefixA z m‖ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val < m), ‖z j - 1‖ := by
        rw [prefixA]; exact norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.univ.filter (fun j : Fin k => j.val < m), (2 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc ‖z j - 1‖ ≤ ‖z j‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [hz j]; norm_num
    _ ≤ 2 * (k : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have : ((Finset.univ.filter (fun j : Fin k => j.val < m)).card : ℝ) ≤ (k : ℝ) := by
          have := Finset.card_filter_le (Finset.univ : Finset (Fin k))
            (fun j : Fin k => j.val < m)
          rw [Finset.card_univ, Fintype.card_fin] at this
          exact_mod_cast this
        nlinarith

/-- **E5, graded.**  With per-prime prefix defects `A_{d_p}` and `G` the set of primes that
reach the least nontrivial site `j₀`, the model expectation contracts by `e^{−1/p}` at exactly
the primes of `G`. -/
theorem model_phase_norm_le_graded {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hinj : Function.Injective p)
    {k : ℕ} (hk : 1 ≤ k) (hkp : ∀ i, k < p i) (z : Fin k → ℂ) (hz : ∀ j, ‖z j‖ = 1)
    (dsee : ι → ℕ) {j₀ : Fin k} (hre : (z j₀).re ≤ 0)
    (G : Finset ι) (hG : ∀ i ∈ G, j₀.val < dsee i) :
    ‖∏ i, (1 + prefixA z (dsee i) / (p i : ℂ))‖
      ≤ Real.exp (2 * k) * Real.exp (- ∑ i ∈ G, (1 : ℝ) / (p i : ℝ)) := by
  classical
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hp : ∀ i, (0 : ℝ) < (p i : ℝ) := by
    intro i
    have : 0 < p i := lt_of_le_of_lt (Nat.zero_le k) (hkp i)
    exact_mod_cast this
  have hstep : ∀ i : ι, (prefixA z (dsee i) / (p i : ℂ)).re
        + ‖prefixA z (dsee i) / (p i : ℂ)‖ ^ 2 / 2
      ≤ (if i ∈ G then -(1 / (p i : ℝ)) else 0) + 2 * (k : ℝ) ^ 2 * (1 / (p i : ℝ) ^ 2) := by
    intro i
    set A : ℂ := prefixA z (dsee i) with hA
    have hpi := hp i
    have hu : (0 : ℝ) < 1 / (p i : ℝ) := by positivity
    have hAn : ‖A‖ ≤ 2 * (k : ℝ) := norm_prefixA_le z hz _
    have hA2 : ‖A‖ ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith [norm_nonneg A]
    rw [Complex.div_natCast_re, norm_div, Complex.norm_natCast]
    have hrw1 : A.re / (p i : ℝ) = A.re * (1 / (p i : ℝ)) := by ring
    have hrw2 : (‖A‖ / (p i : ℝ)) ^ 2 / 2 = ‖A‖ ^ 2 * (1 / (p i : ℝ)) ^ 2 / 2 := by
      rw [div_pow]; ring
    rw [hrw1, hrw2]
    have e3 : (1 / (p i : ℝ)) ^ 2 = 1 / (p i : ℝ) ^ 2 := by rw [div_pow]; norm_num
    have e2 : (0 : ℝ) ≤ (4 * (k : ℝ) ^ 2 - ‖A‖ ^ 2) * (1 / (p i : ℝ) ^ 2) :=
      mul_nonneg (by linarith) (by positivity)
    rw [e3]
    by_cases hiG : i ∈ G
    · rw [if_pos hiG]
      have hAre : A.re ≤ -1 := prefixA_re_le_neg_one z hz hre (hG i hiG)
      have e1 : (0 : ℝ) ≤ (-(A.re + 1)) * (1 / (p i : ℝ)) := mul_nonneg (by linarith) hu.le
      nlinarith [e1, e2]
    · rw [if_neg hiG]
      have hAre : A.re ≤ 0 := prefixA_re_nonpos z hz _
      have e1 : (0 : ℝ) ≤ (-A.re) * (1 / (p i : ℝ)) := mul_nonneg (by linarith) hu.le
      nlinarith [e1, e2]
  calc ‖∏ i, (1 + prefixA z (dsee i) / (p i : ℂ))‖
      = ∏ i, ‖1 + prefixA z (dsee i) / (p i : ℂ)‖ := Complex.norm_prod _ _
    _ ≤ ∏ i, Real.exp ((prefixA z (dsee i) / (p i : ℂ)).re
          + ‖prefixA z (dsee i) / (p i : ℂ)‖ ^ 2 / 2) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => norm_one_add_le_exp _)
    _ = Real.exp (∑ i, ((prefixA z (dsee i) / (p i : ℂ)).re
          + ‖prefixA z (dsee i) / (p i : ℂ)‖ ^ 2 / 2)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (2 * (k : ℝ) + -∑ i ∈ G, (1 : ℝ) / (p i : ℝ)) := by
        refine Real.exp_le_exp.mpr ?_
        have hsum : ∑ i, ((if i ∈ G then -(1 / (p i : ℝ)) else 0)
              + 2 * (k : ℝ) ^ 2 * (1 / (p i : ℝ) ^ 2))
            = -(∑ i ∈ G, (1 : ℝ) / (p i : ℝ))
              + 2 * (k : ℝ) ^ 2 * ∑ i, (1 : ℝ) / (p i : ℝ) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_neg_distrib]
        calc ∑ i, ((prefixA z (dsee i) / (p i : ℂ)).re
                + ‖prefixA z (dsee i) / (p i : ℂ)‖ ^ 2 / 2)
            ≤ ∑ i, ((if i ∈ G then -(1 / (p i : ℝ)) else 0)
                + 2 * (k : ℝ) ^ 2 * (1 / (p i : ℝ) ^ 2)) :=
              Finset.sum_le_sum (fun i _ => hstep i)
          _ = -(∑ i ∈ G, (1 : ℝ) / (p i : ℝ))
                + 2 * (k : ℝ) ^ 2 * ∑ i, (1 : ℝ) / (p i : ℝ) ^ 2 := hsum
          _ ≤ -(∑ i ∈ G, (1 : ℝ) / (p i : ℝ)) + 2 * (k : ℝ) ^ 2 * (1 / (k : ℝ)) := by
              have := sum_inv_sq_le p hinj hk hkp
              nlinarith [sq_nonneg (k : ℝ)]
          _ = 2 * (k : ℝ) + -∑ i ∈ G, (1 : ℝ) / (p i : ℝ) := by
              field_simp
              ring
    _ = Real.exp (2 * (k : ℝ)) * Real.exp (-∑ i ∈ G, (1 : ℝ) / (p i : ℝ)) := Real.exp_add _ _

end NormalNumbers.PrimeModel.PhaseAlgebra
