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

end NormalNumbers.CastingOut
