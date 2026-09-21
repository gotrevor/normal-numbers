import NormalNumbers.PrimeModelRadicalTail
import Mathlib.NumberTheory.Primorial

/-!
# The arithmetic moment budget for the radical model

`NormalNumbers.PrimeModelRadicalTail.radical_box_tail` carries the moment budget

  `∑ i, ((p i) ^ α - 1) / (p i) ≤ A`

as a hypothesis.  This file *discharges* it for the relevant choice of
parameters: `p` an injective family of primes bounded by `y`, and
`α = 1 / (2 log y)` with `log y ≥ 2`.  The budget then holds with `A = 20`
(the true value of the sum is at most `4`; no constant is optimized).

The arithmetic input is a crude Mertens bound, proved here from scratch out of
mathlib's `primorial_le_four_pow`:

* `theta_le` : Chebyshev's `θ(N) = ∑_{p ≤ N} log p ≤ N log 4`;
* `mertens_crude` : `∑_{p ≤ N} (log p) / p ≤ 4 log N` for `N ≥ 2`, by a dyadic
  strong induction (`N ↦ ⌊N/2⌋`) whose inductive step uses `theta_le` on the
  top half-block, where `1/p ≤ 2/N`.

No appeal to the Prime Number Theorem, and no external dependency.
-/

set_option linter.unusedSectionVars false

open scoped BigOperators
open Finset

namespace NormalNumbers.PrimeModel.Radical

/-! ## Chebyshev's `θ` from the primorial bound -/

/-- `θ(N) = ∑_{p ≤ N, p prime} log p`. -/
noncomputable def theta (N : ℕ) : ℝ := ∑ p ∈ Iic N with p.Prime, Real.log p

lemma theta_nonneg (N : ℕ) : 0 ≤ theta N := by
  refine Finset.sum_nonneg fun p hp => ?_
  simp only [Finset.mem_filter] at hp
  exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)

/-- **Chebyshev's upper bound**, `θ(N) ≤ N log 4`, read off from
`primorial_le_four_pow`. -/
lemma theta_le (N : ℕ) : theta N ≤ N * Real.log 4 := by
  have hprod : ((primorial N : ℕ) : ℝ) = ∏ p ∈ Iic N with p.Prime, (p : ℝ) := by
    rw [primorial, Nat.range_succ_eq_Iic]
    push_cast
    rfl
  have hlog : Real.log ((primorial N : ℕ) : ℝ) = theta N := by
    rw [hprod, theta, Real.log_prod]
    intro p hp
    simp only [Finset.mem_filter] at hp
    exact_mod_cast hp.2.ne_zero
  have h4 : ((primorial N : ℕ) : ℝ) ≤ (4 : ℝ) ^ N := by
    exact_mod_cast primorial_le_four_pow N
  have := Real.log_le_log (by exact_mod_cast primorial_pos N) h4
  rw [hlog, Real.log_pow] at this
  simpa using this

/-! ## A crude Mertens bound -/

/-- `∑_{p ≤ N} (log p)/p`. -/
noncomputable def mertensSum (N : ℕ) : ℝ := ∑ p ∈ Iic N with p.Prime, Real.log p / p

lemma mertensSum_nonneg (N : ℕ) : 0 ≤ mertensSum N := by
  refine Finset.sum_nonneg fun p hp => ?_
  simp only [Finset.mem_filter] at hp
  have : (0:ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
  positivity

/-- The top dyadic block: for `M = N / 2`, the primes in `(M, N]` contribute at
most `2 log 4`, since each satisfies `1/p ≤ 2/N`. -/
lemma mertens_block (N : ℕ) (hN : 2 ≤ N) :
    ∑ p ∈ Ioc (N / 2) N with p.Prime, Real.log p / (p : ℝ) ≤ 2 * Real.log 4 := by
  have hN0 : (0:ℝ) < N := by
    have : 0 < N := lt_of_lt_of_le (by norm_num) hN
    exact_mod_cast this
  have hlog4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have step : ∀ p ∈ (Ioc (N / 2) N).filter Nat.Prime,
      Real.log p / (p : ℝ) ≤ (2 / N) * Real.log p := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hp1, hp2⟩, hpp⟩ := hp
    have hplog : (0:ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
    have hNp : (N : ℝ) ≤ 2 * p := by
      have : N ≤ 2 * p := by lia
      exact_mod_cast this
    rw [div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hplog
    rw [inv_le_iff_one_le_mul₀ hp0] at *
    rw [div_mul_eq_mul_div, le_div_iff₀ hN0]
    linarith
  refine (Finset.sum_le_sum step).trans ?_
  rw [← Finset.mul_sum]
  have hsub : (∑ p ∈ Ioc (N / 2) N with Nat.Prime p, Real.log p) ≤ theta N := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · exact Finset.filter_subset_filter _ (fun x hx => Finset.mem_Iic.2 (Finset.mem_Ioc.1 hx).2)
    · intro p hp _
      simp only [Finset.mem_filter] at hp
      exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
  have h2N : (0:ℝ) ≤ 2 / N := by positivity
  calc (2 / N) * (∑ p ∈ Ioc (N / 2) N with Nat.Prime p, Real.log p)
      ≤ (2 / N) * ((N:ℝ) * Real.log 4) :=
        mul_le_mul_of_nonneg_left (hsub.trans (theta_le N)) h2N
    _ = 2 * Real.log 4 := by field_simp

private lemma log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast; ring

/-- **Crude Mertens.**  `∑_{p ≤ N} (log p)/p ≤ 4 log N` for `N ≥ 2`. -/
lemma mertens_crude : ∀ N : ℕ, 2 ≤ N → mertensSum N ≤ 4 * Real.log N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hsmall : N ≤ 3
  · interval_cases N
    · have hf : (Finset.Iic 2).filter Nat.Prime = {2} := by decide
      rw [mertensSum, hf, Finset.sum_singleton]
      push_cast
      nlinarith
    · have hf : (Finset.Iic 3).filter Nat.Prime = {2, 3} := by decide
      have hle : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
      rw [mertensSum, hf, Finset.sum_pair (by norm_num)]
      push_cast
      nlinarith
  · rw [Nat.not_le] at hsmall
    set M := N / 2 with hM
    have hM2 : 2 ≤ M := by lia
    have hMN : M < N := by lia
    have h2M : 2 * M ≤ N := by lia
    have hsplit : (Finset.Iic N).filter Nat.Prime
        = ((Finset.Iic M).filter Nat.Prime) ∪ ((Finset.Ioc M N).filter Nat.Prime) := by
      rw [← Finset.filter_union, Finset.Iic_union_Ioc_eq_Iic hMN.le]
    have hdisj : Disjoint ((Finset.Iic M).filter Nat.Prime)
        ((Finset.Ioc M N).filter Nat.Prime) := by
      refine Finset.disjoint_filter_filter ?_
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_Iic] at ha
      simp only [Finset.mem_Ioc] at hb
      lia
    have hsum : mertensSum N
        = mertensSum M + ∑ p ∈ Ioc M N with Nat.Prime p, Real.log p / (p:ℝ) := by
      rw [mertensSum, hsplit, Finset.sum_union hdisj, mertensSum]
    have hIH := ih M hMN hM2
    have hblk := mertens_block N (by lia)
    rw [← hM] at hblk
    have hMpos : (0:ℝ) < M := by
      have : 0 < M := lt_of_lt_of_le (by norm_num) hM2
      exact_mod_cast this
    have hkey : Real.log (2 * M) ≤ Real.log N := by
      refine Real.log_le_log (by positivity) ?_
      exact_mod_cast h2M
    rw [Real.log_mul (by norm_num) (ne_of_gt hMpos)] at hkey
    rw [log_four_eq] at hblk
    rw [hsum]
    linarith

/-! ## The moment budget -/

/-- `exp t - 1 ≤ 2 t` on `[0, 1/2]`. -/
lemma exp_sub_one_le_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    Real.exp t - 1 ≤ 2 * t := by
  have h1 : (0:ℝ) < 1 - t := by linarith
  have h := Real.add_one_le_exp (-t)
  rw [Real.exp_neg] at h
  have hexp : (0:ℝ) < Real.exp t := Real.exp_pos t
  have h2 : Real.exp t ≤ (1 - t)⁻¹ := by
    rw [le_inv_comm₀ hexp h1]
    linarith
  have h3 : (1 - t)⁻¹ - 1 ≤ 2 * t := by
    rw [inv_eq_one_div, div_sub_one (ne_of_gt h1), div_le_iff₀ h1]
    nlinarith
  linarith

/-- **The arithmetic moment budget.**  For an injective family `p` of primes all
at most `y`, with `log y ≥ 2`, and for `α = 1 / (2 log y)`,

  `∑ i, ((p i)^α - 1) / (p i) ≤ 20`.

(The proof gives `≤ 4`; the constant `20` is the deliberately loose value
consumed by `radical_box_tail`.)  The arithmetic input is `mertens_crude`. -/
theorem radical_moment_budget {ι : Type*} [Fintype ι] {p : ι → ℕ}
    (hinj : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    {y : ℝ} (hy0 : 0 < y) (hy : 2 ≤ Real.log y) (hle : ∀ i, (p i : ℝ) ≤ y) :
    ∑ i, (((p i : ℝ) ^ (1 / (2 * Real.log y)) - 1) / (p i : ℝ)) ≤ 20 := by
  set L := Real.log y with hL
  have hL2 : 0 < L := by linarith
  set α : ℝ := 1 / (2 * L) with hα
  have hαpos : 0 < α := by positivity
  have hαL : α * L = 1 / 2 := by
    rw [hα, one_div, inv_mul_eq_div, div_eq_div_iff (by positivity) (by norm_num)]
    ring
  have hterm : ∀ i, (((p i : ℝ) ^ α - 1) / (p i : ℝ))
      ≤ 2 * α * (Real.log (p i) / (p i : ℝ)) := by
    intro i
    have hp0 : (0:ℝ) < (p i : ℝ) := by exact_mod_cast (hprime i).pos
    have hlogp : 0 ≤ Real.log (p i) := Real.log_nonneg (by exact_mod_cast (hprime i).one_lt.le)
    have hlogpy : Real.log (p i) ≤ L := Real.log_le_log hp0 (hle i)
    have ht : α * Real.log (p i) ≤ 1 / 2 := by
      rw [← hαL]
      exact mul_le_mul_of_nonneg_left hlogpy hαpos.le
    have hrpow : ((p i : ℝ)) ^ α = Real.exp (α * Real.log (p i)) := by
      rw [Real.rpow_def_of_pos hp0, mul_comm]
    rw [hrpow, show 2 * α * (Real.log (p i) / (p i : ℝ))
        = (2 * α * Real.log (p i)) / (p i : ℝ) by ring,
      div_le_div_iff_of_pos_right hp0]
    calc Real.exp (α * Real.log (p i)) - 1
        ≤ 2 * (α * Real.log (p i)) :=
          exp_sub_one_le_two_mul (by positivity) ht
      _ = 2 * α * Real.log (p i) := by ring
  refine (Finset.sum_le_sum (fun i _ => hterm i)).trans ?_
  rw [← Finset.mul_sum]
  have hy2 : (2:ℝ) ≤ y := by
    have h1 : Real.exp 2 ≤ y := by
      rw [← Real.exp_log hy0]
      exact Real.exp_le_exp.2 hy
    nlinarith [Real.add_one_le_exp (2:ℝ)]
  have hfloor2 : 2 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy2)
  have himg : (Finset.univ.image p) ⊆ (Finset.Iic ⌊y⌋₊).filter Nat.Prime := by
    intro n hn
    simp only [Finset.mem_image] at hn
    obtain ⟨i, -, rfl⟩ := hn
    refine Finset.mem_filter.2 ⟨Finset.mem_Iic.2 (Nat.le_floor (hle i)), hprime i⟩
  have hsum : (∑ i, Real.log (p i) / (p i : ℝ))
      = ∑ n ∈ Finset.univ.image p, Real.log n / (n : ℝ) := by
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
  have hmert : (∑ i, Real.log (p i) / (p i : ℝ)) ≤ 4 * Real.log ⌊y⌋₊ := by
    rw [hsum]
    refine (Finset.sum_le_sum_of_subset_of_nonneg himg ?_).trans (mertens_crude _ hfloor2)
    intro n hn _
    simp only [Finset.mem_filter] at hn
    have : (0:ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn.2.one_lt.le)
    positivity
  have hfl : Real.log ⌊y⌋₊ ≤ L := by
    refine Real.log_le_log ?_ (Nat.floor_le hy0.le)
    have : (0:ℕ) < ⌊y⌋₊ := lt_of_lt_of_le (by norm_num) hfloor2
    exact_mod_cast this
  have hchain : (∑ i, Real.log (p i) / (p i : ℝ)) ≤ 4 * L := by linarith
  have h2α : (0:ℝ) ≤ 2 * α := by positivity
  calc 2 * α * (∑ i, Real.log (p i) / (p i : ℝ))
      ≤ 2 * α * (4 * L) := mul_le_mul_of_nonneg_left hchain h2α
    _ = 4 := by rw [show 2 * α * (4 * L) = 8 * (α * L) by ring, hαL]; norm_num
    _ ≤ 20 := by norm_num

/-! ## The retained-box tail with the budget discharged -/

open scoped Classical in
/-- **The retained-box tail, unconditionally.**  Instantiating `radical_box_tail`
at `α = 1 / (2 log y)` with the arithmetic budget `radical_moment_budget`
discharged: for an injective family of primes `p` with `k ≤ p i` and `p i ≤ y`
and `log y ≥ 2`, the model mass outside the retained box `B(T)` is at most
`k * exp 20 / T ^ (1 / (2 log y))`.  No moment hypothesis remains. -/
theorem radical_box_tail_exp20 (k : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℕ} {T y : ℝ}
    (hinj : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (hkp : ∀ i, k ≤ p i) (hy0 : 0 < y) (hy : 2 ≤ Real.log y)
    (hle : ∀ i, (p i : ℝ) ≤ y) (hT : 1 ≤ T) :
    ∑ s ∈ (retainedBox k p T)ᶜ, weight k (primeRecip p) s
      ≤ (k : ℝ) * Real.exp 20 / T ^ (1 / (2 * Real.log y)) := by
  have hL2 : 0 < Real.log y := by linarith
  exact radical_box_tail k hkp (fun i => (hprime i).one_lt.le.trans' (by norm_num)) hT
    (by positivity) (radical_moment_budget hinj hprime hy0 hy hle)

end NormalNumbers.PrimeModel.Radical
