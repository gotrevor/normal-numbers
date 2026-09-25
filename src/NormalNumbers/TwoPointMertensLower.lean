import NormalNumbers.TwoPointDelangeLF

/-!
# Towards Mertens' first theorem in lower-bound form

Part II of the complex Wirsing step (`TwoPointDelangeLF.lean`, lap 37) needs

    Σ_{p ≤ N} (log p) / p  ≥  log N − C ,

the lower half of Mertens' first theorem.  The repo has only the crude upper bound
`mertens_crude : Σ_{p≤N} log p/p ≤ 4 log N` (`PrimeModelRadicalMoment.lean`).

The classical elementary proof counts `log(N!)` two ways:

* **from below**, `log(N!) ≥ N log N − N` — proved here (`log_factorial_ge`), *discretely*: the
  increment of `n ↦ n log n − n` is `n log n − (n−1)log(n−1) − 1`, and it is at most `log n`
  exactly because `(n−1)·log(n/(n−1)) ≤ 1`, which is the same `log(m+1) − log m ≤ 1/m` bound the
  Abel step used.  No integrals;
* **from above**, Legendre's formula `log(N!) = Σ_{p≤N} (Σ_{k≥1} ⌊N/p^k⌋) log p` together with
  `Σ_{k≥1} ⌊N/p^k⌋ ≤ N/(p−1)` — the geometric bound proved here
  (`sum_div_pow_le`), and `1/(p−1) = 1/p + 1/(p(p−1))`, whose second piece sums to a constant.

This file lands the two elementary halves; the Legendre assembly is the next brick.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- **`log(N!) ≥ N log N − N`, discretely.**  Telescoping `n log n − n` against `log n`, using
`log(n+1) − log n ≤ 1/n`. -/
theorem log_factorial_ge (N : ℕ) :
    (N : ℝ) * Real.log N - (N : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, Real.log n := by
  induction N with
  | zero => simp
  | succ N ih =>
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        simp
      have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      have hstep : (N : ℝ) * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) ≤ 1 := by
        have h := log_succ_sub_log_le hN
        have : (N : ℝ) * (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ))
            ≤ (N : ℝ) * (1 / (N : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h hNR.le
        rw [mul_one_div, div_self (ne_of_gt hNR)] at this
        exact this
      have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [Finset.sum_Icc_succ_top (by omega), hcast]
      nlinarith [ih, hstep]

/-- **The geometric bound on Legendre's exponent.**  `Σ_{k=1}^{K} ⌊N/p^k⌋ ≤ N/(p−1)`. -/
theorem sum_div_pow_le {p : ℕ} (hp : 2 ≤ p) (N K : ℕ) :
    ∑ k ∈ Finset.Ico 1 K, ((N / p ^ k : ℕ) : ℝ) ≤ (N : ℝ) / ((p : ℝ) - 1) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hfl : ∀ k : ℕ, ((N / p ^ k : ℕ) : ℝ) ≤ (N : ℝ) / (p : ℝ) ^ k := by
    intro k
    have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
    rw [le_div_iff₀ hpk]
    have h1 : (N / p ^ k : ℕ) * p ^ k ≤ N := Nat.div_mul_le_self N (p ^ k)
    calc ((N / p ^ k : ℕ) : ℝ) * (p : ℝ) ^ k = (((N / p ^ k : ℕ) * p ^ k : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (N : ℝ) := by exact_mod_cast h1
  refine le_trans (Finset.sum_le_sum fun k _ => hfl k) ?_
  -- `Σ_{k≥1} N/p^k = (N/p)·1/(1−1/p) = N/(p−1)`, and a partial sum is at most the total
  have hgeo : ∑ k ∈ Finset.Ico 1 K, (N : ℝ) / (p : ℝ) ^ k
      ≤ (N : ℝ) / ((p : ℝ) - 1) := by
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have hexact : ∀ M : ℕ, ∑ k ∈ Finset.Ico 1 (M + 1), (1 : ℝ) / (p : ℝ) ^ k
        = 1 / ((p : ℝ) - 1) * (1 - 1 / (p : ℝ) ^ M) := by
      intro M
      induction M with
      | zero => simp
      | succ M ihM =>
          rw [Finset.sum_Ico_succ_top (by omega), ihM]
          have hpM : (0 : ℝ) < (p : ℝ) ^ M := by positivity
          field_simp
          ring
    have hkey : ∀ K : ℕ, ∑ k ∈ Finset.Ico 1 K, (1 : ℝ) / (p : ℝ) ^ k
        ≤ 1 / ((p : ℝ) - 1) := by
      intro K
      rcases Nat.eq_zero_or_pos K with hK | hK
      · subst hK
        rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
        positivity
      · obtain ⟨M, rfl⟩ : ∃ M, K = M + 1 := ⟨K - 1, by omega⟩
        rw [hexact]
        have h3 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) * (1 / (p : ℝ) ^ M) := by positivity
        nlinarith [h3]
    calc ∑ k ∈ Finset.Ico 1 K, (N : ℝ) / (p : ℝ) ^ k
        = (N : ℝ) * ∑ k ∈ Finset.Ico 1 K, (1 : ℝ) / (p : ℝ) ^ k := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ (N : ℝ) * (1 / ((p : ℝ) - 1)) := mul_le_mul_of_nonneg_left (hkey K) hNnn
      _ = (N : ℝ) / ((p : ℝ) - 1) := by ring
  exact hgeo

/-! ### The convergent correction `Σ (log n)/(n(n−1))`

`1/(p−1) = 1/p + 1/(p(p−1))`, so the `log(N!)` upper bound produces, besides `N·Σ log p/p`, the
correction `N·Σ_{p≤N} (log p)/(p(p−1))`.  That sum is bounded by an absolute constant.  Proof,
entirely elementary: `log n ≤ 2√n` (apply `log x ≤ x − 1` to `√n`), `n − 1 ≥ n/2` for `n ≥ 2`, so
the term is `≤ 4/n^{3/2}`, and `4/n^{3/2} ≤ 8(1/√(n−1) − 1/√n)` telescopes to `8`. -/

lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hx.le] at h
  linarith [Real.sqrt_nonneg x]

/-- `4/n^{3/2} ≤ 8(1/√(n−1) − 1/√n)` for `n ≥ 2`. -/
lemma inv_rpow_le_telescope {n : ℕ} (hn : 2 ≤ n) :
    4 / ((n : ℝ) * Real.sqrt n)
      ≤ 8 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set a : ℝ := Real.sqrt (n : ℝ) with ha
  set b : ℝ := Real.sqrt ((n : ℝ) - 1) with hb
  have ha2 : a ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hapos : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hbpos : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hba : b ≤ a := Real.sqrt_le_sqrt (by linarith)
  have hkey : 1 / (a ^ 2 * a) ≤ 2 * (1 / b - 1 / a) := by
    rw [div_le_iff₀ (by positivity)]
    have hexp : 2 * (1 / b - 1 / a) * (a ^ 2 * a) = 2 * a ^ 2 * (a - b) * a / (a * b) := by
      field_simp
      try ring
    rw [hexp, le_div_iff₀ (by positivity)]
    nlinarith [hapos, hbpos, hba, ha2, hb2, sq_nonneg (a - b), sq_nonneg (a + b)]
  have hn2 : (n : ℝ) * a = a ^ 2 * a := by rw [ha2]
  rw [hn2]
  have h4 : (4 : ℝ) / (a ^ 2 * a) = 4 * (1 / (a ^ 2 * a)) := by ring
  rw [h4]
  linarith [hkey]

/-- The telescoping sum. -/
lemma sum_inv_sqrt_telescope : ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.Icc 2 N, (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ))
      = 1 - 1 / Real.sqrt (N : ℝ) := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
      intro _
      rcases Nat.lt_or_ge N 1 with hN | hN
      · have hN0 : N = 0 := by omega
        subst hN0
        simp
      rw [Finset.sum_Icc_succ_top (by omega), ih hN]
      have hcast : ((N + 1 : ℕ) : ℝ) - 1 = (N : ℝ) := by push_cast; ring
      rw [hcast]
      have hcast2 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast2]
      ring

/-- **The correction is bounded by `8`, absolutely.** -/
theorem sum_log_div_mul_pred_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 8 := by
  have hterm : ∀ n ∈ Finset.Icc 2 N,
      Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
        ≤ 8 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt (n : ℝ)) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
    have hlog : Real.log n ≤ 2 * Real.sqrt (n : ℝ) := log_le_two_sqrt (by linarith)
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
    have hstep : Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 4 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
      rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
      have hmul := mul_le_mul_of_nonneg_right hlog
        (by positivity : (0 : ℝ) ≤ (n : ℝ) * Real.sqrt (n : ℝ))
      nlinarith [hmul, hsq, hnR, hs]
    exact le_trans hstep (inv_rpow_le_telescope hn.1)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rcases Nat.lt_or_ge N 1 with hN | hN
  · have hN0 : N = 0 := by omega
    subst hN0
    simp
  rw [← Finset.mul_sum, sum_inv_sqrt_telescope N hN]
  have : (0 : ℝ) ≤ 1 / Real.sqrt (N : ℝ) := by positivity
  linarith

/-! ### The assembly: Mertens' first theorem, lower half

`log(N!)` counted two ways.  mathlib supplies Legendre's bound directly
(`Nat.factorization_factorial_le_div_pred : (N!).factorization p ≤ N/(p−1)`), so the geometric
step is free and `sum_div_pow_le` above is only a standalone record of it. -/

/-- `log(N!) = Σ_{n=1}^{N} log n`. -/
lemma log_factorial_eq_sum (N : ℕ) :
    Real.log ((Nat.factorial N : ℕ) : ℝ) = ∑ n ∈ Finset.Icc 1 N, Real.log n := by
  have hIcc : ∑ n ∈ Finset.Icc 1 N, Real.log n = ∑ i ∈ Finset.range N, Real.log ((i : ℝ) + 1) := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
        have : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
        rw [this]
  rw [hIcc, Nat.factorial_eq_prod_range_add_one]
  push_cast
  rw [Real.log_prod]
  intro i hi
  positivity

/-- `log(N!) = Σ_{p ≤ N} v_p(N!)·log p`. -/
lemma log_factorial_eq_prime_sum (N : ℕ) :
    Real.log ((Nat.factorial N : ℕ) : ℝ)
      = ∑ p ∈ primesLe N, (((Nat.factorial N).factorization p : ℕ) : ℝ) * Real.log p := by
  classical
  have hne : (Nat.factorial N) ≠ 0 := Nat.factorial_ne_zero N
  have hfac : (Nat.factorial N : ℕ) = ∏ p ∈ (Nat.factorial N).primeFactors, p ^ ((Nat.factorial N).factorization p) :=
    (Nat.factorization_prod_pow_eq_self hne).symm
  have hsub : (Nat.factorial N).primeFactors ⊆ primesLe N := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hple : p ≤ N := (Nat.Prime.dvd_factorial hpp).mp hdvd
    simp only [primesLe, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpp⟩
  have hprod : ((Nat.factorial N : ℕ) : ℝ) = ∏ p ∈ (Nat.factorial N).primeFactors, ((p : ℝ) ^ ((Nat.factorial N).factorization p)) := by
    conv_lhs => rw [hfac]
    push_cast
    rfl
  rw [hprod, Real.log_prod]
  · have h1 : ∑ p ∈ (Nat.factorial N).primeFactors,
        Real.log ((p : ℝ) ^ ((Nat.factorial N).factorization p))
        = ∑ p ∈ (Nat.factorial N).primeFactors,
            (((Nat.factorial N).factorization p : ℕ) : ℝ) * Real.log p :=
      Finset.sum_congr rfl fun p _ => by rw [Real.log_pow]
    rw [h1]
    refine Finset.sum_subset hsub ?_
    intro p hp hnot
    have hz : (Nat.factorial N).factorization p = 0 := by
      by_contra hc
      exact hnot (Nat.support_factorization (n := Nat.factorial N) ▸ Finsupp.mem_support_iff.mpr hc)
    rw [hz]
    simp
  · intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    positivity

/-- **MERTENS' FIRST THEOREM, LOWER HALF.**  `Σ_{p ≤ N} (log p)/p ≥ log N − 9`, with an explicit
absolute constant and an entirely elementary proof. -/
theorem mertens_lower (N : ℕ) (hN : 1 ≤ N) :
    Real.log N - 9 ≤ ∑ p ∈ primesLe N, Real.log p / (p : ℝ) := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- the upper count
  have hupper : Real.log ((Nat.factorial N : ℕ) : ℝ)
      ≤ (N : ℝ) * ∑ p ∈ primesLe N, Real.log p / ((p : ℝ) - 1) := by
    rw [log_factorial_eq_prime_sum N, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp := prime_of_mem_primesLe hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    have hnat := Nat.factorization_factorial_le_div_pred hpp N
    have hcast : (((Nat.factorial N).factorization p : ℕ) : ℝ) ≤ (N : ℝ) / ((p : ℝ) - 1) := by
      have h1 : (((Nat.factorial N).factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
        exact_mod_cast hnat
      have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p : ℝ) - 1) := by
        have hpm : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
          have : 1 ≤ p := hpp.one_lt.le
          push_cast [Nat.cast_sub this]
          ring
        rw [← hpm]
        exact cast_div_le N (p - 1)
      linarith
    calc (((Nat.factorial N).factorization p : ℕ) : ℝ) * Real.log p
        ≤ ((N : ℝ) / ((p : ℝ) - 1)) * Real.log p := mul_le_mul_of_nonneg_right hcast hlog
      _ = (N : ℝ) * (Real.log p / ((p : ℝ) - 1)) := by ring
  -- split `1/(p−1) = 1/p + 1/(p(p−1))`
  have hsplit : ∑ p ∈ primesLe N, Real.log p / ((p : ℝ) - 1)
      = (∑ p ∈ primesLe N, Real.log p / (p : ℝ))
        + ∑ p ∈ primesLe N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpp := prime_of_mem_primesLe hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have h1 : (p : ℝ) ≠ 0 := by linarith
    have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  -- the correction is `≤ 8`
  have hcorr : ∑ p ∈ primesLe N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 8 := by
    refine le_trans ?_ (sum_log_div_mul_pred_le N)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n hn _ => ?_)
    · intro p hp
      have hpp := prime_of_mem_primesLe hp
      have hple : p ≤ N := by
        rw [primesLe, Finset.mem_filter, Finset.mem_range] at hp
        omega
      simp only [Finset.mem_Icc]
      exact ⟨hpp.two_le, hple⟩
    · simp only [Finset.mem_Icc] at hn
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      have : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
      have hd : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      positivity
  -- the lower count
  have hlower : (N : ℝ) * Real.log N - (N : ℝ) ≤ Real.log ((Nat.factorial N : ℕ) : ℝ) := by
    rw [log_factorial_eq_sum N]
    exact log_factorial_ge N
  rw [hsplit] at hupper
  have hfinal : (N : ℝ) * Real.log N - (N : ℝ)
      ≤ (N : ℝ) * ((∑ p ∈ primesLe N, Real.log p / (p : ℝ)) + 8) := by
    refine le_trans hlower (le_trans hupper ?_)
    have : (∑ p ∈ primesLe N, Real.log p / (p : ℝ))
        + ∑ p ∈ primesLe N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ (∑ p ∈ primesLe N, Real.log p / (p : ℝ)) + 8 := by linarith [hcorr]
    exact mul_le_mul_of_nonneg_left this hNR.le
  have hdiv : Real.log N - 1 ≤ (∑ p ∈ primesLe N, Real.log p / (p : ℝ)) + 8 := by
    have := (div_le_div_iff_of_pos_right hNR).mpr hfinal
    nlinarith [hfinal, hNR]
  linarith [hdiv]

end NormalNumbers.CastingOut
