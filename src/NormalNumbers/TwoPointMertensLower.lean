import NormalNumbers.TwoPointDelangeLF
import NormalNumbers.PrimeModelRadicalMoment

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

/-! ### The sharp upper half

`mertens_crude` gives `Σ_{p≤N} log p/p ≤ 4 log N`, whose constant `4` is useless for a Toeplitz
normalisation.  The same `log(N!)` count run in the other direction gives the sharp constant:
keep only the `k = 1` term of Legendre, use `⌊N/p⌋ ≥ N/p − 1`, and pay `θ(N) ≤ N log 4`
(Chebyshev, `PrimeModelRadicalMoment.theta_le`). -/

/-- **MERTENS' FIRST THEOREM, SHARP UPPER HALF.**  `Σ_{p≤N}(log p)/p ≤ log N + log 4`. -/
theorem mertens_upper (N : ℕ) (hN : 1 ≤ N) :
    ∑ p ∈ primesLe N, Real.log p / (p : ℝ) ≤ Real.log N + Real.log 4 := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- upper bound on `log(N!)`
  have hupper : Real.log ((Nat.factorial N : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N := by
    rw [log_factorial_eq_sum N]
    have hstep : ∀ n ∈ Finset.Icc 1 N, Real.log n ≤ Real.log N := by
      intro n hn
      simp only [Finset.mem_Icc] at hn
      have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.1
      exact Real.log_le_log h1 (by exact_mod_cast hn.2)
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have : ((N + 1 - 1 : ℕ) : ℝ) = (N : ℝ) := by push_cast; ring
    rw [this]
  -- lower bound on `log(N!)` keeping only the `k = 1` Legendre term
  have hlower : (N : ℝ) * (∑ p ∈ primesLe N, Real.log p / (p : ℝ))
      - (N : ℝ) * Real.log 4 ≤ Real.log ((Nat.factorial N : ℕ) : ℝ) := by
    rw [log_factorial_eq_prime_sum N]
    have hterm : ∀ p ∈ primesLe N,
        (N : ℝ) * (Real.log p / (p : ℝ)) - Real.log p
          ≤ (((Nat.factorial N).factorization p : ℕ) : ℝ) * Real.log p := by
      intro p hp
      have hpp := prime_of_mem_primesLe hp
      have hple : p ≤ N := by
        rw [primesLe, Finset.mem_filter, Finset.mem_range] at hp
        omega
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
      have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
      -- `v_p(N!) ≥ ⌊N/p⌋`
      have hb : Nat.log p N < Nat.log p N + 1 := Nat.lt_succ_self _
      have hleg := Nat.factorization_factorial hpp hb
      have hmem : (1 : ℕ) ∈ Finset.Ico 1 (Nat.log p N + 1) := by
        simp only [Finset.mem_Ico]
        refine ⟨le_rfl, ?_⟩
        have : 1 ≤ Nat.log p N := Nat.le_log_of_pow_le hpp.one_lt (by simpa using hple)
        omega
      have hge : N / p ≤ (Nat.factorial N).factorization p := by
        rw [hleg]
        have := Finset.single_le_sum (f := fun i => N / p ^ i)
          (fun i _ => Nat.zero_le _) hmem
        simpa using this
      have hgeR : ((N / p : ℕ) : ℝ) ≤ (((Nat.factorial N).factorization p : ℕ) : ℝ) := by
        exact_mod_cast hge
      have hfl : (N : ℝ) / (p : ℝ) - 1 ≤ ((N / p : ℕ) : ℝ) := sub_one_le_cast_div N p hpp.pos
      have hchain : (N : ℝ) / (p : ℝ) - 1 ≤ (((Nat.factorial N).factorization p : ℕ) : ℝ) := by
        linarith
      have := mul_le_mul_of_nonneg_right hchain hlogp
      calc (N : ℝ) * (Real.log p / (p : ℝ)) - Real.log p
          = ((N : ℝ) / (p : ℝ) - 1) * Real.log p := by ring
        _ ≤ _ := this
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    have hth : ∑ p ∈ primesLe N, Real.log p ≤ (N : ℝ) * Real.log 4 := by
      have hset : primesLe N = (Finset.Iic N).filter Nat.Prime := by
        rw [primesLe, Nat.range_succ_eq_Iic]
      rw [hset]
      exact NormalNumbers.PrimeModel.Radical.theta_le N
    have hrewrite : ∑ p ∈ primesLe N, (N : ℝ) * (Real.log p / (p : ℝ))
        = (N : ℝ) * ∑ p ∈ primesLe N, Real.log p / (p : ℝ) := by
      rw [Finset.mul_sum]
    linarith [hsum, hth]
  have hcomb : (N : ℝ) * (∑ p ∈ primesLe N, Real.log p / (p : ℝ))
      ≤ (N : ℝ) * (Real.log N + Real.log 4) := by
    have : (N : ℝ) * (∑ p ∈ primesLe N, Real.log p / (p : ℝ)) - (N : ℝ) * Real.log 4
        ≤ (N : ℝ) * Real.log N := le_trans hlower hupper
    nlinarith [this]
  nlinarith [hcomb, hNR]

/-! ### The complex step, part II(a): replacing `S^{(p)}` by `S` costs `O(1)`

The Levin–Fainleib identity is stated with the coprimality-restricted sums `S^{(p)}`.  For the
Toeplitz argument they must be replaced by `S` itself.  The cost is bounded by an absolute
constant — it does NOT grow with `N` — because `Σ_p (log p)/p² < ∞`, which is
`sum_log_div_mul_pred_le` (`TwoPointMertensLower.lean`) again via `1/p² ≤ 1/(p(p−1))`. -/

/-- The identity of lap 33, restated on the named sums. -/
theorem delangeT_eq_prime_sum (z : ℂ) (N : ℕ) :
    delangeT z N
      = (z - 1) * ∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeSrestr z p (N / p) :=
  sum_delangeKernel_mul_log z N

/-- **`S^{(p)}` is bounded whenever `S` is**, uniformly in `p` and `M`, with the clean constant
`2B`.  Strong induction on `M` through `delangeSrestr_rec`, using `u/p ≤ 1/2`. -/
theorem norm_delangeSrestr_le_two_mul {z : ℂ} (hu : ‖z - 1‖ ≤ 1) {p : ℕ} (hp : p.Prime)
    {B : ℝ} (hB : ∀ M, ‖delangeS z M‖ ≤ B) (M : ℕ) : ‖delangeSrestr z p M‖ ≤ 2 * B := by
  have hBnn : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  induction M using Nat.strong_induction_on with
  | _ M ih =>
      rcases Nat.eq_zero_or_pos M with hM | hM
      · subst hM
        simp only [delangeSrestr]
        rw [show Finset.Ioc 0 0 = (∅ : Finset ℕ) by simp]
        simp
        linarith
      have hlt : M / p < M := Nat.div_lt_self hM hp.one_lt
      have hrec := delangeSrestr_rec z hp M
      rw [hrec]
      refine le_trans (norm_sub_le _ _) ?_
      have h1 : ‖((z - 1) / (p : ℂ)) * delangeSrestr z p (M / p)‖
          = ‖z - 1‖ / (p : ℝ) * ‖delangeSrestr z p (M / p)‖ := by
        rw [norm_mul, norm_div, Complex.norm_natCast]
      rw [h1]
      have h2 := ih (M / p) hlt
      have h3 : ‖z - 1‖ / (p : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      have h4 : (0 : ℝ) ≤ ‖z - 1‖ / (p : ℝ) := by positivity
      nlinarith [hB M, h2, h3, h4, hBnn]

/-- **The replacement cost is an absolute constant.**  `‖T(N) − (z−1)·Σ_{p≤N}(log p/p)·S(N/p)‖
≤ 16·B`, uniformly in `N`. -/
theorem norm_delangeT_sub_primeSum_le {z : ℂ} (hu : ‖z - 1‖ ≤ 1) {B : ℝ}
    (hB : ∀ M, ‖delangeS z M‖ ≤ B) (N : ℕ) :
    ‖delangeT z N
        - (z - 1) * ∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p)‖
      ≤ 16 * B := by
  classical
  have hBnn : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  rw [delangeT_eq_prime_sum z N, ← mul_sub, ← Finset.sum_sub_distrib]
  rw [norm_mul]
  have hstep : ∀ p ∈ primesLe N,
      ‖((Real.log p : ℂ) / (p : ℂ)) * delangeSrestr z p (N / p)
        - ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p)‖
        ≤ 2 * B * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    intro p hp
    have hpp := prime_of_mem_primesLe hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    -- the difference is exactly `((z−1)/p)·S^{(p)}(N/p²)`
    have hrec := delangeSrestr_rec z hpp (N / p)
    rw [← mul_sub, hrec]
    have hcollapse : delangeS z (N / p) - ((z - 1) / (p : ℂ)) * delangeSrestr z p (N / p / p)
        - delangeS z (N / p) = -(((z - 1) / (p : ℂ)) * delangeSrestr z p (N / p / p)) := by
      ring
    rw [hcollapse, norm_mul, norm_neg, norm_mul, norm_div, norm_div, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogp]
    have hb := norm_delangeSrestr_le_two_mul hu hpp hB (N / p / p)
    have hpe : Real.log p / (p : ℝ) * (‖z - 1‖ / (p : ℝ) * ‖delangeSrestr z p (N / p / p)‖)
        ≤ Real.log p / (p : ℝ) * (1 / (p : ℝ) * (2 * B)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hppos : (0 : ℝ) < (p : ℝ) := by linarith
      have h1 : ‖z - 1‖ / (p : ℝ) ≤ 1 / (p : ℝ) := by
        rw [div_le_div_iff₀ hppos hppos]
        nlinarith [hu, hppos]
      nlinarith [hb, h1, norm_nonneg (delangeSrestr z p (N / p / p)), hBnn,
        (by positivity : (0:ℝ) ≤ 1 / (p : ℝ))]
    refine le_trans hpe ?_
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hpp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have key : Real.log p / (p : ℝ) * (1 / (p : ℝ) * (2 * B))
        = 2 * B * (Real.log p / ((p : ℝ) * (p : ℝ))) := by
      field_simp
      try ring
    rw [key]
    have hmono : Real.log p / ((p : ℝ) * (p : ℝ))
        ≤ Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hlogp, hp2]
    nlinarith [hmono, hBnn]
  have hsum := Finset.sum_le_sum hstep
  have hnormsum : ‖∑ p ∈ primesLe N,
      (((Real.log p : ℂ) / (p : ℂ)) * delangeSrestr z p (N / p)
        - ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p))‖
      ≤ ∑ p ∈ primesLe N, 2 * B * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) :=
    le_trans (norm_sum_le _ _) hsum
  have hcorr : ∑ p ∈ primesLe N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 8 := by
    refine le_trans ?_ (sum_log_div_mul_pred_le N)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n hn _ => ?_)
    · intro q hq
      have hqq := prime_of_mem_primesLe hq
      have hqle : q ≤ N := by
        rw [primesLe, Finset.mem_filter, Finset.mem_range] at hq
        omega
      simp only [Finset.mem_Icc]
      exact ⟨hqq.two_le, hqle⟩
    · simp only [Finset.mem_Icc] at hn
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      have : (0 : ℝ) ≤ Real.log n := Real.log_nonneg (by linarith)
      have hd : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      positivity
  rw [← Finset.mul_sum] at hnormsum
  have hfin : ‖z - 1‖ * ‖∑ p ∈ primesLe N,
      (((Real.log p : ℂ) / (p : ℂ)) * delangeSrestr z p (N / p)
        - ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p))‖ ≤ 1 * (2 * B * 8) := by
    refine mul_le_mul hu (le_trans hnormsum ?_) (norm_nonneg _) (by norm_num)
    nlinarith [hcorr, hBnn]
  linarith [hfin]

/-! ### The complex step, part II(b): the prime-sum side is a Toeplitz average

`norm_delangeT_sub_primeSum_le` (part II(a)) replaced `S^{(p)}` by `S` at cost `O(1)`, leaving

    T(N) = (z−1) · Σ_{p ≤ N} (log p / p) · S(N/p) + O(1).

The prime sum is again a regular average of `S`: the weights `log p / p` are nonnegative and, by
the two-sided Mertens bracket (`mertens_lower`, `mertens_upper`), total `log N + O(1)`.  The only
wrinkle over the Abel case is that the argument `N/p` is *small* for the largest primes; but those
`p` carry weight `O_{M₀}(1)` — exactly the difference of the Mertens bracket at `N` and at
`N/M₀` — so they die after dividing by `log N`. -/

/-- **The heavy primes carry bounded weight.**  The primes `p ≤ N` for which `N/p` has not yet
reached `M₀` have total Mertens weight at most `log(2M₀) + log 4 + 9`, an absolute constant in
`N`.  This is the difference of the two-sided Mertens bracket at `N` and at `N/M₀`. -/
theorem sum_weight_tail_le {M₀ N : ℕ} (hM₀ : 1 ≤ M₀) (hN : 2 * M₀ ≤ N) :
    ∑ p ∈ (primesLe N).filter (fun p => N / p < M₀), Real.log p / (p : ℝ)
      ≤ Real.log (2 * M₀) + Real.log 4 + 9 := by
  classical
  set K : ℕ := N / M₀ with hK
  have hM₀pos : 0 < M₀ := hM₀
  have hK2 : 2 ≤ K := (Nat.le_div_iff_mul_le hM₀pos).mpr (by omega)
  have hKN : K ≤ N := Nat.div_le_self _ _
  have hN1 : 1 ≤ N := by omega
  have hK1 : 1 ≤ K := by omega
  -- nonnegativity of the summand
  have hnn : ∀ p ∈ primesLe N, (0 : ℝ) ≤ Real.log p / (p : ℝ) := by
    intro p hp
    have hpp := prime_of_mem_primesLe hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    positivity
  -- `primesLe K ⊆ primesLe N`
  have hsub : primesLe K ⊆ primesLe N := by
    intro p hp
    rw [primesLe, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  -- the filtered set avoids `primesLe K`
  have hsub2 : (primesLe N).filter (fun p => N / p < M₀) ⊆ primesLe N \ primesLe K := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpN, hlt⟩ := hp
    have hpp := prime_of_mem_primesLe hpN
    refine Finset.mem_sdiff.mpr ⟨hpN, ?_⟩
    intro hmem
    rw [primesLe, Finset.mem_filter, Finset.mem_range] at hmem
    have hpK : p ≤ K := by omega
    have hMK : M₀ * K ≤ N := by
      rw [hK, Nat.mul_comm]; exact Nat.div_mul_le_self N M₀
    have : M₀ * p ≤ N := le_trans (Nat.mul_le_mul_left _ hpK) hMK
    have : M₀ ≤ N / p := (Nat.le_div_iff_mul_le hpp.pos).mpr (by omega)
    omega
  have hle1 : ∑ p ∈ (primesLe N).filter (fun p => N / p < M₀), Real.log p / (p : ℝ)
      ≤ ∑ p ∈ primesLe N \ primesLe K, Real.log p / (p : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun p hp _ => hnn p (Finset.mem_sdiff.mp hp).1)
  have hsd : ∑ p ∈ primesLe N \ primesLe K, Real.log p / (p : ℝ)
      + ∑ p ∈ primesLe K, Real.log p / (p : ℝ)
      = ∑ p ∈ primesLe N, Real.log p / (p : ℝ) := Finset.sum_sdiff hsub
  -- Mertens both sides
  have hup := mertens_upper N hN1
  have hlo := mertens_lower K hK1
  -- `log N ≤ log(2M₀) + log K`
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
  have hM₀R : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀
  have hidr : (N : ℝ) = (M₀ : ℝ) * (K : ℝ) + ((N % M₀ : ℕ) : ℝ) := by
    have := Nat.div_add_mod N M₀
    have : (M₀ * K + N % M₀ : ℕ) = N := by rw [hK]; exact Nat.div_add_mod N M₀
    exact_mod_cast this.symm
  have hrR : ((N % M₀ : ℕ) : ℝ) < (M₀ : ℝ) := by
    exact_mod_cast Nat.mod_lt _ hM₀pos
  have hNK : (N : ℝ) ≤ 2 * (M₀ : ℝ) * (K : ℝ) := by nlinarith [hidr, hrR, hKR, hM₀R]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hlogN : Real.log N ≤ Real.log (2 * M₀) + Real.log K := by
    have h1 : Real.log N ≤ Real.log (2 * (M₀ : ℝ) * (K : ℝ)) := Real.log_le_log hNpos hNK
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    linarith [h1]
  linarith [hle1, hsd, hup, hlo, hlogN]

/-- **Toeplitz regularity of the prime-sum average.**  If `S(N) → L` then
`(Σ_{p≤N}(log p/p)·S(N/p)) / log N → L`.  The weights are nonnegative with total `log N + O(1)`
(Mertens, both halves), and the primes at which `N/p` has not yet reached the `ε`-threshold `M₀`
carry only `O_{M₀}(1)` weight (`sum_weight_tail_le`). -/
theorem tendsto_primeSum_div_log (z : ℂ) {L : ℂ}
    (h : Tendsto (fun N => delangeS z N) atTop (𝓝 L)) :
    Tendsto (fun N => (∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p))
        / (Real.log N : ℂ)) atTop (𝓝 L) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M₁, hM₁⟩ := (Metric.tendsto_atTop.mp h) (ε / 4) (by linarith)
  set M₀ : ℕ := max 1 M₁ with hM₀def
  have hM₀1 : 1 ≤ M₀ := le_max_left _ _
  have hM₀S : ∀ M, M₀ ≤ M → ‖delangeS z M - L‖ ≤ ε / 4 := by
    intro M hM
    have := hM₁ M (le_trans (le_max_right 1 M₁) hM)
    rw [Complex.dist_eq] at this
    linarith
  set C₀ : ℝ := ∑ M ∈ Finset.range M₀, ‖delangeS z M - L‖ with hC₀def
  have hC₀nn : (0 : ℝ) ≤ C₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hC₀ : ∀ M, M < M₀ → ‖delangeS z M - L‖ ≤ C₀ := by
    intro M hM
    exact Finset.single_le_sum (f := fun M => ‖delangeS z M - L‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr hM)
  set D : ℝ := Real.log (2 * M₀) + Real.log 4 + 9 with hDdef
  have hM₀R : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀1
  have hDnn : (0 : ℝ) ≤ D := by
    have h1 : (0 : ℝ) ≤ Real.log (2 * (M₀ : ℝ)) := Real.log_nonneg (by linarith)
    have h2 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [hDdef]; linarith
  set X : ℝ := C₀ * D + 9 * ‖L‖ with hXdef
  have hXnn : (0 : ℝ) ≤ X := by
    rw [hXdef]; have := norm_nonneg L; nlinarith [hC₀nn, hDnn]
  have hlogtt : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := (hlogtt.eventually_gt_atTop
    (max (max 1 (Real.log 4)) (2 * X / ε))).exists_forall_of_atTop
  refine ⟨max (2 * M₀) N₁, fun N hN => ?_⟩
  have hN2M : 2 * M₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1' : 1 ≤ N := by omega
  have hbig := hN₁ N (le_trans (le_max_right _ _) hN)
  have hlog1 : (1 : ℝ) < Real.log N :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hbig
  have hlog4 : Real.log 4 < Real.log N :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hbig
  have hlogX : 2 * X / ε < Real.log N := lt_of_le_of_lt (le_max_right _ _) hbig
  have hLpos : (0 : ℝ) < Real.log N := by linarith
  have hLc : ((Real.log N : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hLpos
  set W : ℝ := ∑ p ∈ primesLe N, Real.log p / (p : ℝ) with hWdef
  have hwnn : ∀ p ∈ primesLe N, (0 : ℝ) ≤ Real.log p / (p : ℝ) := by
    intro p hp
    have hpp := prime_of_mem_primesLe hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    positivity
  have hnormterm : ∀ p ∈ primesLe N, ∀ x : ℂ,
      ‖((Real.log p : ℂ) / (p : ℂ)) * x‖ = Real.log p / (p : ℝ) * ‖x‖ := by
    intro p hp x
    have hpp := prime_of_mem_primesLe hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlp : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlp,
      Complex.norm_natCast]
  -- the exact decomposition
  have hcastW : ((W : ℝ) : ℂ) = ∑ p ∈ primesLe N, (Real.log p : ℂ) / (p : ℂ) := by
    rw [hWdef]; push_cast; rfl
  have hdecomp : (∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p))
      - L * ((W : ℝ) : ℂ)
      = ∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * (delangeS z (N / p) - L) := by
    rw [hcastW, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  -- the two-piece bound
  have hsplit := Finset.sum_filter_add_sum_filter_not (primesLe N) (fun p => N / p < M₀)
    (fun p => ‖((Real.log p : ℂ) / (p : ℂ)) * (delangeS z (N / p) - L)‖)
  have hheavy : ∑ p ∈ (primesLe N).filter (fun p => N / p < M₀),
      ‖((Real.log p : ℂ) / (p : ℂ)) * (delangeS z (N / p) - L)‖ ≤ C₀ * D := by
    have hstep : ∀ p ∈ (primesLe N).filter (fun p => N / p < M₀),
        ‖((Real.log p : ℂ) / (p : ℂ)) * (delangeS z (N / p) - L)‖
          ≤ C₀ * (Real.log p / (p : ℝ)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [hnormterm p hp.1]
      have h1 := hC₀ (N / p) hp.2
      have h2 := hwnn p hp.1
      nlinarith [h1, h2]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have := sum_weight_tail_le (M₀ := M₀) (N := N) hM₀1 hN2M
    nlinarith [this, hC₀nn]
  have hlight : ∑ p ∈ (primesLe N).filter (fun p => ¬ N / p < M₀),
      ‖((Real.log p : ℂ) / (p : ℂ)) * (delangeS z (N / p) - L)‖ ≤ (ε / 4) * W := by
    have hstep : ∀ p ∈ (primesLe N).filter (fun p => ¬ N / p < M₀),
        ‖((Real.log p : ℂ) / (p : ℂ)) * (delangeS z (N / p) - L)‖
          ≤ (ε / 4) * (Real.log p / (p : ℝ)) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [hnormterm p hp.1]
      have h1 := hM₀S (N / p) (by omega)
      have h2 := hwnn p hp.1
      nlinarith [h1, h2]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have hsub : ∑ p ∈ (primesLe N).filter (fun p => ¬ N / p < M₀), Real.log p / (p : ℝ) ≤ W := by
      rw [hWdef]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p hp _ => hwnn p hp)
    nlinarith [hsub, hε]
  -- Mertens bracket
  have hup := mertens_upper N hN1'
  have hlo := mertens_lower N hN1'
  have hlog4nn : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4le : Real.log 4 ≤ 9 := by
    have : Real.log 4 ≤ 4 - 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num)
      linarith
    linarith
  have hWbr : Real.log N - 9 ≤ W ∧ W ≤ Real.log N + Real.log 4 := ⟨hlo, hup⟩
  -- assemble
  have hkey : ‖(∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p))
      - L * ((W : ℝ) : ℂ)‖ ≤ (ε / 4) * W + C₀ * D := by
    rw [hdecomp]
    refine le_trans (norm_sum_le _ _) ?_
    rw [← hsplit]
    linarith [hheavy, hlight]
  have hshift : ‖L * ((W : ℝ) : ℂ) - L * ((Real.log N : ℝ) : ℂ)‖ ≤ 9 * ‖L‖ := by
    rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have : |W - Real.log N| ≤ 9 := by
      rw [abs_le]; constructor <;> linarith [hWbr.1, hWbr.2, hlog4le]
    nlinarith [this, norm_nonneg L]
  have htotal : ‖(∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p))
      - L * ((Real.log N : ℝ) : ℂ)‖ ≤ (ε / 4) * W + C₀ * D + 9 * ‖L‖ := by
    have := norm_add_le
      ((∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p)) - L * ((W : ℝ) : ℂ))
      (L * ((W : ℝ) : ℂ) - L * ((Real.log N : ℝ) : ℂ))
    have heq : ((∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p))
        - L * ((W : ℝ) : ℂ)) + (L * ((W : ℝ) : ℂ) - L * ((Real.log N : ℝ) : ℂ))
        = (∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p))
          - L * ((Real.log N : ℝ) : ℂ) := by ring
    rw [heq] at this
    linarith [this, hkey, hshift]
  rw [Complex.dist_eq]
  have hrw : (∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p))
        / ((Real.log N : ℝ) : ℂ) - L
      = ((∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p))
        - L * ((Real.log N : ℝ) : ℂ)) / ((Real.log N : ℝ) : ℂ) := by
    field_simp
  rw [hrw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLpos.le,
    div_lt_iff₀ hLpos]
  -- `(ε/4)·W ≤ (ε/2)·log N` and `X < (ε/2)·log N`
  have hWle : W ≤ 2 * Real.log N := by linarith [hWbr.2, hlog4]
  have h1 : (ε / 4) * W ≤ (ε / 2) * Real.log N := by nlinarith [hWle, hε]
  have h2 : X < (ε / 2) * Real.log N := by
    rw [div_lt_iff₀ hε] at hlogX
    linarith [hlogX]
  have h3 : C₀ * D + 9 * ‖L‖ = X := by rw [hXdef]
  linarith [htotal, h1, h2, h3]

/-! ### The complex step, part II(c): convergence of `S` already forces `S → 0`

With both Toeplitz limits in hand the value of the limit is no longer free.  `T(N)/log N → 0`
(lap 37) and `T(N) = (z−1)·Σ_p(log p/p)·S(N/p) + O(1)` (part II(a)) and
`Σ_p(log p/p)·S(N/p)/log N → L` (part II(b)) together give `(z−1)·L = 0`.  So for `z ≠ 1` the
residue `DelangeKernelMean z` is **equivalent to the mere convergence of `S`** — the limit is
automatically `0`. -/

/-- A convergent sequence in `ℂ` is bounded, in the uniform-`∀ M` form the `S^{(p)}` lemmas want. -/
theorem exists_bound_of_tendsto {f : ℕ → ℂ} {L : ℂ} (h : Tendsto f atTop (𝓝 L)) :
    ∃ B, ∀ M, ‖f M‖ ≤ B := by
  classical
  obtain ⟨M₀, hM₀⟩ := (Metric.tendsto_atTop.mp h) 1 (by norm_num)
  refine ⟨(∑ M ∈ Finset.range M₀, ‖f M‖) + ‖L‖ + 1, fun M => ?_⟩
  have hsnn : (0 : ℝ) ≤ ∑ M ∈ Finset.range M₀, ‖f M‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  rcases lt_or_ge M M₀ with hM | hM
  · have := Finset.single_le_sum (f := fun M => ‖f M‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr hM)
    have := norm_nonneg L
    linarith
  · have hd := hM₀ M hM
    rw [Complex.dist_eq] at hd
    have := norm_sub_norm_le (f M) L
    linarith

/-- **The limit of `S` is forced to be `0`.**  For `z ≠ 1` with `‖z−1‖ ≤ 1`, if `S` converges at
all then it converges to `0`, i.e. `DelangeKernelMean z` holds. -/
theorem delangeKernelMean_of_converges {z : ℂ} (hz : z ≠ 1) (hu : ‖z - 1‖ ≤ 1)
    (h : ∃ L, Tendsto (fun N => delangeS z N) atTop (𝓝 L)) : DelangeKernelMean z := by
  classical
  obtain ⟨L, hL⟩ := h
  obtain ⟨B, hB⟩ := exists_bound_of_tendsto hL
  have hBnn : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hlogtt : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- the `O(1)` replacement error dies after dividing by `log N`
  have herr : Tendsto (fun N : ℕ => (delangeT z N
      - (z - 1) * ∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p))
      / (Real.log N : ℂ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (Filter.Tendsto.const_div_atTop hlogtt (16 * B))
    filter_upwards [Filter.eventually_gt_atTop 1] with N hN
    have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hLpos : (0 : ℝ) < Real.log N := Real.log_pos hNR
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLpos.le]
    have := norm_delangeT_sub_primeSum_le hu hB N
    gcongr
  -- so `(z−1)·(prime average) → 0`
  have hT := tendsto_delangeT_div_log z hL
  have hdiff : Tendsto (fun N : ℕ => (delangeT z N) / (Real.log N : ℂ)
      - (delangeT z N
        - (z - 1) * ∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p))
        / (Real.log N : ℂ)) atTop (𝓝 (0 - 0)) := hT.sub herr
  rw [sub_zero] at hdiff
  have hcongr : Tendsto (fun N : ℕ => (z - 1)
      * ((∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p))
        / (Real.log N : ℂ))) atTop (𝓝 0) := by
    refine hdiff.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 1] with N hN
    have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hLpos : (0 : ℝ) < Real.log N := Real.log_pos hNR
    have hLc : ((Real.log N : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hLpos
    field_simp
    ring
  -- but it also tends to `(z−1)·L`
  have hP := (tendsto_primeSum_div_log z hL).const_mul (z - 1)
  have hzero : (z - 1) * L = 0 := tendsto_nhds_unique hP hcongr
  have hz1 : z - 1 ≠ 0 := sub_ne_zero_of_ne hz
  have hL0 : L = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h hz1
    · exact h
  rw [delangeKernelMean_iff]
  rw [hL0] at hL
  exact hL

end NormalNumbers.CastingOut
