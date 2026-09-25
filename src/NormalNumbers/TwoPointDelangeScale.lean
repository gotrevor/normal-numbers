import NormalNumbers.TwoPointDelangeOmega

/-!
# The scale route's summation tools

`delange_scale_equation` (`TwoPointDelangeOmega.lean`) is

    ‖S(N)·log N − z·Abel(N)‖ ≤ 19·A(N),        Abel(N+1) − Abel(N) = δ_N·S(N),

with `δ_N = log(N+1) − log N` and `A(N) = Σ_{n≤N}‖h_z(n)‖/n`.  Closing `DelangeKernelMean` from it
is a discrete integrating-factor argument, and both of its halves consume the same two elementary
facts about the *relative* increment

    s_m := (log(m+1) − log m) / log m .

This file proves them.

1. **The telescoping bound** `Σ_{N₀ ≤ m < N} s_m ≤ log log N − log log N₀ + 1/(N₀−1)`.  The engine
   is an exact identity — `log(m+1) = log m · (1 + s_m)`, because `log` increments *additively* by
   `δ_m` and `s_m` is that increment measured in units of `log m` — so
   `log log(m+1) − log log m = log(1 + s_m)`, and `log(1+s) ≥ s − s²` gives `s_m` back up to `s_m²`,
   whose sum telescopes against `1/(m−1) − 1/m`.  No integral, no prime input, no Mertens.

2. **The Gronwall closure** `a_{m+1} ≤ a_m(1 + c·s_m) ⟹ a_N ≤ C·(log N)^c`, from `1 + x ≤ exp x`.

Both are used twice: at `c = 1 + ‖z−1‖` to bound the error term `A(N)` by `(log N)^{u'}`, and inside
the integrating-factor induction for `Abel`.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- `s_m = (log(m+1) − log m)/log m`: the increment of `log` at `m`, in units of `log m`. -/
noncomputable def logRatioStep (m : ℕ) : ℝ :=
  (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) / Real.log (m : ℝ)

lemma one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  have h : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  have := Real.log_lt_log (Real.exp_pos 1) h
  rwa [Real.log_exp] at this

lemma one_le_log_cast {m : ℕ} (hm : 3 ≤ m) : (1 : ℝ) ≤ Real.log (m : ℝ) := by
  have h3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  exact le_trans one_lt_log_three.le (Real.log_le_log (by norm_num) h3)

lemma logRatioStep_nonneg {m : ℕ} (hm : 3 ≤ m) : 0 ≤ logRatioStep m :=
  div_nonneg (log_succ_sub_log_nonneg (by omega)) (by linarith [one_le_log_cast hm])

lemma logRatioStep_le_inv {m : ℕ} (hm : 3 ≤ m) : logRatioStep m ≤ 1 / (m : ℝ) := by
  have hL := one_le_log_cast hm
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [logRatioStep, div_le_div_iff₀ (by linarith) (by linarith)]
  have h := log_succ_sub_log_le (show 1 ≤ m by omega)
  have : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := h
  calc (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * (m : ℝ)
      ≤ (1 / (m : ℝ)) * (m : ℝ) := by
        refine mul_le_mul_of_nonneg_right this (by linarith)
    _ = 1 := by field_simp
    _ ≤ 1 * Real.log (m : ℝ) := by linarith
/-- `log(1+s) ≥ s − s²` for `s ≥ 0`.  Two applications of `log x ≤ x − 1`. -/
lemma log_one_add_ge_sub_sq {s : ℝ} (hs : 0 ≤ s) : s - s ^ 2 ≤ Real.log (1 + s) := by
  have hpos : (0 : ℝ) < 1 + s := by linarith
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 + s) by positivity)
  rw [Real.log_div one_ne_zero (ne_of_gt hpos), Real.log_one, zero_sub] at h
  have hrw : (1 : ℝ) / (1 + s) - 1 = -(s / (1 + s)) := by field_simp; ring
  rw [hrw] at h
  have h2 : s / (1 + s) ≤ Real.log (1 + s) := by linarith
  have h3 : s - s ^ 2 ≤ s / (1 + s) := by
    rw [le_div_iff₀ hpos]
    nlinarith [pow_nonneg hs 3, hs]
  linarith

/-- **The exact identity.**  `log(m+1) = log m · (1 + s_m)`. -/
lemma log_succ_eq_mul {m : ℕ} (hm : 3 ≤ m) :
    Real.log ((m : ℝ) + 1) = Real.log (m : ℝ) * (1 + logRatioStep m) := by
  have hL := one_le_log_cast hm
  rw [logRatioStep]
  field_simp
  ring

/-- **The step of the telescope.**  `s_m ≤ (log log(m+1) − log log m) + s_m²`. -/
lemma logRatioStep_le_logLog_step {m : ℕ} (hm : 3 ≤ m) :
    logRatioStep m
      ≤ (Real.log (Real.log ((m : ℝ) + 1)) - Real.log (Real.log (m : ℝ)))
        + (logRatioStep m) ^ 2 := by
  have hL := one_le_log_cast hm
  have hs := logRatioStep_nonneg hm
  have hkey := log_one_add_ge_sub_sq hs
  rw [log_succ_eq_mul hm, Real.log_mul (by linarith) (by linarith)]
  linarith

/-- **THE TELESCOPING BOUND.**  `Σ_{N₀ ≤ m < N} s_m ≤ G(N) − G(N₀)` with
`G(x) = log log x − 1/(x−1)`.  No primes, no integrals, no Mertens. -/
theorem sum_logRatioStep_le {N₀ : ℕ} (h0 : 3 ≤ N₀) :
    ∀ N, N₀ ≤ N → ∑ m ∈ Finset.Ico N₀ N, logRatioStep m
      ≤ (Real.log (Real.log (N : ℝ)) - 1 / ((N : ℝ) - 1))
        - (Real.log (Real.log (N₀ : ℝ)) - 1 / ((N₀ : ℝ) - 1)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      have hm3 : 3 ≤ N := le_trans h0 hN
      have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm3
      rw [Finset.sum_Ico_succ_top hN]
      have hstep := logRatioStep_le_logLog_step hm3
      have hs0 := logRatioStep_nonneg hm3
      have hsinv := logRatioStep_le_inv hm3
      have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
      have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
      have hsq : (logRatioStep N) ^ 2 ≤ 1 / ((N : ℝ) - 1) - 1 / (N : ℝ) := by
        have h1 : (logRatioStep N) ^ 2 ≤ (1 / (N : ℝ)) ^ 2 := pow_le_pow_left₀ hs0 hsinv 2
        have hkey : 1 / ((N : ℝ) - 1) - 1 / (N : ℝ) = 1 / (((N : ℝ) - 1) * (N : ℝ)) := by
          field_simp
          ring
        have h2 : (1 / (N : ℝ)) ^ 2 ≤ 1 / ((N : ℝ) - 1) - 1 / (N : ℝ) := by
          rw [hkey, div_pow, one_pow, div_le_div_iff₀ (by positivity) (mul_pos hN1 hN0)]
          nlinarith
        linarith
      have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hsimp : (N : ℝ) + 1 - 1 = (N : ℝ) := by ring
      rw [hsimp]
      linarith

/-- The usable form: the `1/(N−1)` correction dropped. -/
theorem sum_logRatioStep_le' {N₀ N : ℕ} (h0 : 3 ≤ N₀) (hN : N₀ ≤ N) :
    ∑ m ∈ Finset.Ico N₀ N, logRatioStep m
      ≤ Real.log (Real.log (N : ℝ)) - Real.log (Real.log (N₀ : ℝ)) + 1 / ((N₀ : ℝ) - 1) := by
  have h := sum_logRatioStep_le h0 N hN
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_trans h0 hN
  have : (0 : ℝ) ≤ 1 / ((N : ℝ) - 1) := by
    have : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    positivity
  linarith

/-! ### The Gronwall closure -/

/-- **DISCRETE GRONWALL.**  `a_{m+1} ≤ a_m(1 + c·s_m)` for `m ≥ N₀` forces
`a_N ≤ a_{N₀}·exp(c·Σ s_m)`. -/
theorem gronwall_logRatio {c : ℝ} (hc : 0 ≤ c) {a : ℕ → ℝ} {N₀ : ℕ} (h0 : 3 ≤ N₀)
    (hanneg : ∀ m, 0 ≤ a m)
    (hstep : ∀ m, N₀ ≤ m → a (m + 1) ≤ a m * (1 + c * logRatioStep m)) :
    ∀ N, N₀ ≤ N → a N ≤ a N₀ * Real.exp (c * ∑ m ∈ Finset.Ico N₀ N, logRatioStep m) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      have hm3 : 3 ≤ N := le_trans h0 hN
      have hs0 := logRatioStep_nonneg hm3
      rw [Finset.sum_Ico_succ_top hN]
      have hfac : 1 + c * logRatioStep N ≤ Real.exp (c * logRatioStep N) := by
        have := Real.add_one_le_exp (c * logRatioStep N)
        linarith
      calc a (N + 1) ≤ a N * (1 + c * logRatioStep N) := hstep N hN
        _ ≤ (a N₀ * Real.exp (c * ∑ m ∈ Finset.Ico N₀ N, logRatioStep m))
              * Real.exp (c * logRatioStep N) := by
            refine mul_le_mul ih hfac ?_ ?_
            · have := mul_nonneg hc hs0; linarith
            · exact mul_nonneg (hanneg N₀) (Real.exp_pos _).le
        _ = a N₀ * Real.exp (c * (∑ m ∈ Finset.Ico N₀ N, logRatioStep m + logRatioStep N)) := by
            rw [mul_assoc, ← Real.exp_add, mul_add]

/-- **THE `(log N)^c` FORM.**  The constant is explicit and depends only on `a N₀`, `c`, `N₀`. -/
theorem gronwall_le_rpow {c : ℝ} (hc : 0 ≤ c) {a : ℕ → ℝ} {N₀ : ℕ} (h0 : 3 ≤ N₀)
    (hanneg : ∀ m, 0 ≤ a m)
    (hstep : ∀ m, N₀ ≤ m → a (m + 1) ≤ a m * (1 + c * logRatioStep m)) :
    ∀ N, N₀ ≤ N → a N
      ≤ (a N₀ * Real.exp (c * (1 / ((N₀ : ℝ) - 1) - Real.log (Real.log (N₀ : ℝ)))))
          * (Real.log (N : ℝ)) ^ c := by
  intro N hN
  have hg := gronwall_logRatio hc h0 hanneg hstep N hN
  have hsum := sum_logRatioStep_le' h0 hN
  have hLN : (1 : ℝ) ≤ Real.log (N : ℝ) := one_le_log_cast (le_trans h0 hN)
  have hexp : Real.exp (c * ∑ m ∈ Finset.Ico N₀ N, logRatioStep m)
      ≤ Real.exp (c * (1 / ((N₀ : ℝ) - 1) - Real.log (Real.log (N₀ : ℝ))))
        * (Real.log (N : ℝ)) ^ c := by
    have hmono : c * ∑ m ∈ Finset.Ico N₀ N, logRatioStep m
        ≤ c * (Real.log (Real.log (N : ℝ)) - Real.log (Real.log (N₀ : ℝ)) + 1 / ((N₀ : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hsum hc
    refine le_trans (Real.exp_le_exp.2 hmono) ?_
    rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    ring_nf
    linarith
  calc a N ≤ a N₀ * Real.exp (c * ∑ m ∈ Finset.Ico N₀ N, logRatioStep m) := hg
    _ ≤ a N₀ * (Real.exp (c * (1 / ((N₀ : ℝ) - 1) - Real.log (Real.log (N₀ : ℝ))))
          * (Real.log (N : ℝ)) ^ c) := mul_le_mul_of_nonneg_left hexp (hanneg N₀)
    _ = (a N₀ * Real.exp (c * (1 / ((N₀ : ℝ) - 1) - Real.log (Real.log (N₀ : ℝ)))))
          * (Real.log (N : ℝ)) ^ c := by ring

end NormalNumbers.CastingOut
