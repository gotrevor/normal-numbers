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


/-! ### Brick 2: the error term `A(N)` is `O((log N)^{u'})` with `u' < 1`

`delange_scale_equation`'s error term is `A(N) = Σ_{n≤N}‖h_z(n)‖/n`, and the classical route to
`A(N) ≍ (log N)^u` is the Euler product plus **Mertens' second theorem** `Σ_{p≤N}1/p = log log N +
O(1)`.  That is not needed here, and the repo's available form (`primeRecipSum_le`) has constant
`12`, which would shrink the discharged regime to `‖z−1‖ < 1/12`.

The structural observation: `A` is **itself a kernel sum**.  With `u = ‖z−1‖` and the *real*
parameter `z' = 1 + u` one has `delangeKernel z' n = ‖delangeKernel z n‖`, hence

    delangeS z' N = A(N),    delangeA z' N = A(N),    ‖z' − 1‖ = u ≤ 1,

so the scale equation applies at `z'` and, everything now being real, reads

    | A(N)·log N − (1+u)·Ā(N) | ≤ 19·A(N),      Ā(N) = Σ_{1≤m<N} δ_m·A(m) ≥ 0.

Brick 1's Gronwall then gives the sharp exponent, with the `19` costing only an `ε`. -/

lemma norm_ofReal_sub_one (z : ℂ) : ‖((1 + ‖z - 1‖ : ℝ) : ℂ) - 1‖ = ‖z - 1‖ := by
  rw [show ((1 + ‖z - 1‖ : ℝ) : ℂ) - 1 = ((‖z - 1‖ : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- **`h_{1+u} = ‖h_z‖`** pointwise: the absolute companion is a kernel in its own right. -/
lemma delangeKernel_ofReal_abs (z : ℂ) (n : ℕ) :
    delangeKernel ((1 + ‖z - 1‖ : ℝ) : ℂ) n
      = ((if Squarefree n then ‖z - 1‖ ^ omegaNat n else 0 : ℝ) : ℂ) := by
  unfold delangeKernel
  split
  · push_cast
    ring
  · simp

lemma delangeS_ofReal_eq (z : ℂ) (N : ℕ) :
    delangeS ((1 + ‖z - 1‖ : ℝ) : ℂ) N = ((delangeA z N : ℝ) : ℂ) := by
  rw [delangeS, delangeA, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [delangeKernel_ofReal_abs, norm_delangeKernel, Complex.ofReal_div, Complex.ofReal_natCast]

lemma delangeA_ofReal_eq (z : ℂ) (N : ℕ) :
    delangeA ((1 + ‖z - 1‖ : ℝ) : ℂ) N = delangeA z N := by
  rw [delangeA, delangeA]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [norm_delangeKernel, norm_delangeKernel, norm_ofReal_sub_one]

/-- The real Abel transform of the absolute companion. -/
noncomputable def delangeAbs (z : ℂ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico 1 N, (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * delangeA z m

lemma delangeAbs_nonneg (z : ℂ) (N : ℕ) : 0 ≤ delangeAbs z N := by
  refine Finset.sum_nonneg fun m hm => ?_
  simp only [Finset.mem_Ico] at hm
  exact mul_nonneg (log_succ_sub_log_nonneg hm.1) (delangeA_nonneg z m)

lemma delangeAbel_ofReal_eq (z : ℂ) (N : ℕ) :
    delangeAbel ((1 + ‖z - 1‖ : ℝ) : ℂ) N = ((delangeAbs z N : ℝ) : ℂ) := by
  rw [delangeAbel, delangeAbs, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [delangeS_ofReal_eq, Complex.ofReal_mul]

/-- **THE SCALE EQUATION AT THE REAL PARAMETER `1+u`.**  A purely real inequality tying `A` to its
own Abel transform — the scale equation bounding its own error term. -/
theorem delangeA_scale_real {z : ℂ} (hu : ‖z - 1‖ ≤ 1) (N : ℕ) :
    |delangeA z N * Real.log (N : ℝ) - (1 + ‖z - 1‖) * delangeAbs z N| ≤ 19 * delangeA z N := by
  have hz' : ‖((1 + ‖z - 1‖ : ℝ) : ℂ) - 1‖ ≤ 1 := by rw [norm_ofReal_sub_one]; exact hu
  have h := delange_scale_equation hz' N
  rw [delangeS_ofReal_eq, delangeAbel_ofReal_eq, delangeA_ofReal_eq] at h
  rw [show ((delangeA z N : ℝ) : ℂ) * ((Real.log (N : ℝ) : ℝ) : ℂ)
        - ((1 + ‖z - 1‖ : ℝ) : ℂ) * ((delangeAbs z N : ℝ) : ℂ)
      = ((delangeA z N * Real.log (N : ℝ) - (1 + ‖z - 1‖) * delangeAbs z N : ℝ) : ℂ) by
    push_cast; ring] at h
  rwa [Complex.norm_real, Real.norm_eq_abs] at h

/-- **BRICK 2.**  For `‖z−1‖ < 1` the error term of the scale equation is `O((log N)^{u'})` with
`u' < 1`, unconditionally and with no Mertens input. -/
theorem exists_delangeA_le_rpow {z : ℂ} (hu : ‖z - 1‖ < 1) :
    ∃ C u' : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 ≤ u' ∧ u' < 1 ∧ 3 ≤ N₀ ∧
      ∀ N, N₀ ≤ N → delangeA z N ≤ C * (Real.log (N : ℝ)) ^ u' := by
  have hu0 : (0 : ℝ) ≤ ‖z - 1‖ := norm_nonneg _
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (1 - ‖z - 1‖) / 4 := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = (1 + ‖z - 1‖) * (1 + ε) := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by rw [hcdef]; nlinarith
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hc2 : c < 2 := by
    rw [hcdef, hεdef]
    nlinarith [mul_pos (show (0:ℝ) < 1 - ‖z - 1‖ by linarith)
      (show (0:ℝ) < 3 - ‖z - 1‖ by linarith)]
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 19 * (1 + ε) / ε := ⟨_, rfl⟩
  obtain ⟨N₀, hN0def⟩ : ∃ N₀ : ℕ, N₀ = max 3 ⌈Real.exp B⌉₊ := ⟨_, rfl⟩
  have h03 : 3 ≤ N₀ := by rw [hN0def]; exact le_max_left _ _
  have hN0pos : (0 : ℝ) < (N₀ : ℝ) := by
    have : 0 < N₀ := by omega
    exact_mod_cast this
  have hlogN₀ : B ≤ Real.log (N₀ : ℝ) := by
    rw [Real.le_log_iff_exp_le hN0pos]
    refine le_trans (Nat.le_ceil _) ?_
    have : ⌈Real.exp B⌉₊ ≤ N₀ := by rw [hN0def]; exact le_max_right _ _
    exact_mod_cast this
  -- the key inequality: `A(m)·log m ≤ c·Ā(m)`
  have hkey : ∀ m, N₀ ≤ m → delangeA z m * Real.log (m : ℝ) ≤ c * delangeAbs z m := by
    intro m hm
    have hmR : (N₀ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hLB : B ≤ Real.log (m : ℝ) :=
      le_trans hlogN₀ (Real.log_le_log hN0pos hmR)
    have hAnn := delangeA_nonneg z m
    have h1 : delangeA z m * Real.log (m : ℝ) - (1 + ‖z - 1‖) * delangeAbs z m
        ≤ 19 * delangeA z m := (abs_le.1 (delangeA_scale_real hu.le m)).2
    have hεL : 19 * (1 + ε) ≤ ε * Real.log (m : ℝ) := by
      rw [hBdef] at hLB
      calc 19 * (1 + ε) = (19 * (1 + ε) / ε) * ε := by field_simp
        _ ≤ Real.log (m : ℝ) * ε := mul_le_mul_of_nonneg_right hLB hε.le
        _ = ε * Real.log (m : ℝ) := by ring
    have hL19 : Real.log (m : ℝ) ≤ (1 + ε) * (Real.log (m : ℝ) - 19) := by nlinarith [hεL]
    have hAi : delangeA z m * (Real.log (m : ℝ) - 19) ≤ (1 + ‖z - 1‖) * delangeAbs z m := by
      nlinarith [h1]
    calc delangeA z m * Real.log (m : ℝ)
        ≤ delangeA z m * ((1 + ε) * (Real.log (m : ℝ) - 19)) :=
          mul_le_mul_of_nonneg_left hL19 hAnn
      _ = (1 + ε) * (delangeA z m * (Real.log (m : ℝ) - 19)) := by ring
      _ ≤ (1 + ε) * ((1 + ‖z - 1‖) * delangeAbs z m) :=
          mul_le_mul_of_nonneg_left hAi (by linarith)
      _ = c * delangeAbs z m := by rw [hcdef]; ring
  -- the Gronwall recursion for `Ā`
  have hstep : ∀ m, N₀ ≤ m → delangeAbs z (m + 1) ≤ delangeAbs z m * (1 + c * logRatioStep m) := by
    intro m hm
    have hm1 : 1 ≤ m := by omega
    have hm3 : 3 ≤ m := le_trans h03 hm
    have hL := one_le_log_cast hm3
    have hsplit : delangeAbs z (m + 1)
        = delangeAbs z m + (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * delangeA z m := by
      rw [delangeAbs, delangeAbs, Finset.sum_Ico_succ_top hm1]
    have hdelta : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) = logRatioStep m * Real.log (m : ℝ) := by
      rw [logRatioStep]
      field_simp
    rw [hsplit, hdelta]
    have hk := hkey m hm
    have hs0 := logRatioStep_nonneg hm3
    calc delangeAbs z m + logRatioStep m * Real.log (m : ℝ) * delangeA z m
        = delangeAbs z m + logRatioStep m * (delangeA z m * Real.log (m : ℝ)) := by ring
      _ ≤ delangeAbs z m + logRatioStep m * (c * delangeAbs z m) := by
          linarith [mul_le_mul_of_nonneg_left hk hs0]
      _ = delangeAbs z m * (1 + c * logRatioStep m) := by ring
  have hgr := gronwall_le_rpow hc0 h03 (fun m => delangeAbs_nonneg z m) hstep
  obtain ⟨C₀, hC0def⟩ : ∃ C₀ : ℝ, C₀ = delangeAbs z N₀
      * Real.exp (c * (1 / ((N₀ : ℝ) - 1) - Real.log (Real.log (N₀ : ℝ)))) := ⟨_, rfl⟩
  have hC0nn : (0 : ℝ) ≤ C₀ := by
    rw [hC0def]; exact mul_nonneg (delangeAbs_nonneg z N₀) (Real.exp_pos _).le
  refine ⟨c * C₀ + 1, c - 1, N₀, ?_, by linarith, by linarith, h03, ?_⟩
  · have := mul_nonneg hc0 hC0nn; linarith
  intro N hN
  have hm3 : 3 ≤ N := le_trans h03 hN
  have hL := one_le_log_cast hm3
  have hLpos : (0 : ℝ) < Real.log (N : ℝ) := by linarith
  have h1 : delangeAbs z N ≤ C₀ * (Real.log (N : ℝ)) ^ c := by rw [hC0def]; exact hgr N hN
  have h2 : delangeA z N * Real.log (N : ℝ) ≤ c * (C₀ * (Real.log (N : ℝ)) ^ c) :=
    le_trans (hkey N hN) (mul_le_mul_of_nonneg_left h1 hc0)
  have hrpow : (Real.log (N : ℝ)) ^ c = (Real.log (N : ℝ)) ^ (c - 1) * Real.log (N : ℝ) := by
    have h := (Real.rpow_add hLpos (c - 1) 1).symm
    rw [Real.rpow_one] at h
    rw [h]
    congr 1
    ring
  have hcancel : delangeA z N ≤ (c * C₀) * (Real.log (N : ℝ)) ^ (c - 1) := by
    refine le_of_mul_le_mul_right ?_ hLpos
    calc delangeA z N * Real.log (N : ℝ) ≤ c * (C₀ * (Real.log (N : ℝ)) ^ c) := h2
      _ = (c * C₀) * ((Real.log (N : ℝ)) ^ (c - 1) * Real.log (N : ℝ)) := by rw [hrpow]; ring
      _ = ((c * C₀) * (Real.log (N : ℝ)) ^ (c - 1)) * Real.log (N : ℝ) := by ring
  have hrp : (0 : ℝ) ≤ (Real.log (N : ℝ)) ^ (c - 1) := Real.rpow_nonneg (by linarith) _
  nlinarith [hcancel, hrp]


/-! ### Brick 3: the discrete integrating factor

The continuous argument multiplies `Abel` by `(log x)^{-z}` and reads off
`‖Abel(N)‖ ≲ (log N)^{Re z} + (log N)^{u'}`.  Formalising *that* needs a second-order Taylor bound
on `Complex.cpow`.  It is cheaper, and gives everything the closure needs, to fix ANY exponent
`θ` strictly between `max(Re z, u')` and `1` and prove `‖Abel(N)‖ ≤ C·(log N)^θ` by induction.
Then only a REAL `rpow` appears, and the two inputs are

* `‖1 + z·s‖ ≤ 1 + s·Re z + s²/2`  — the sign `Re z < 1` enters here, and nowhere else;
* `(1+s)^θ ≥ 1 + θs − s²`  — enough slack to absorb both `s²` terms.

The step then needs exactly `19·A(N) + (3/2)·C·L^θ·s ≤ C·L^θ·(θ − Re z)`: the first summand from
brick 2 by taking `C` large, the second because `s_N ≤ 1/N → 0`. -/

/-- `‖1 + z·s‖ ≤ 1 + s·Re z + s²/2` for `‖z‖ = 1`, `s ≥ 0`.  An exact norm-square plus
`(s·Re z + s²/2)² ≥ 0`. -/
lemma norm_one_add_mul_ofReal_le {z : ℂ} (hz : ‖z‖ = 1) {s : ℝ} (hs : 0 ≤ s) :
    ‖1 + z * (s : ℂ)‖ ≤ 1 + s * z.re + s ^ 2 / 2 := by
  have hn : z.re * z.re + z.im * z.im = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simp only [Complex.normSq_apply] at h
    nlinarith [h]
  have hreg : (-1 : ℝ) ≤ z.re := by nlinarith [hn, mul_self_nonneg z.im]
  have hsq : ‖1 + z * (s : ℂ)‖ ^ 2 = 1 + 2 * s * z.re + s ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
    nlinarith [hn]
  have hB : (0 : ℝ) ≤ 1 + s * z.re + s ^ 2 / 2 := by
    nlinarith [mul_nonneg hs (show (0:ℝ) ≤ z.re + 1 by linarith), sq_nonneg (s - 1)]
  have hle : ‖1 + z * (s : ℂ)‖ ^ 2 ≤ (1 + s * z.re + s ^ 2 / 2) ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (s * z.re + s ^ 2 / 2)]
  have := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hB] at this

/-- `(1+s)^θ ≥ 1 + θs − s²` for `s ≥ 0`, `0 ≤ θ ≤ 1`.  `exp x ≥ 1 + x` on top of
`log(1+s) ≥ s − s²`. -/
lemma one_add_rpow_ge {s θ : ℝ} (hs : 0 ≤ s) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1 + θ * s - s ^ 2 ≤ (1 + s) ^ θ := by
  have hpos : (0 : ℝ) < 1 + s := by linarith
  rw [Real.rpow_def_of_pos hpos]
  have h1 := Real.add_one_le_exp (Real.log (1 + s) * θ)
  have h2 := log_one_add_ge_sub_sq hs
  have hA : θ * (s - s ^ 2) ≤ θ * Real.log (1 + s) := mul_le_mul_of_nonneg_left h2 hθ0
  have hB : (0 : ℝ) ≤ (1 - θ) * s ^ 2 := mul_nonneg (by linarith) (sq_nonneg s)
  nlinarith [h1, hA, hB]

/-- **BRICK 3.**  `‖Abel(N)‖ ≤ C·(log N)^θ` for some `θ < 1`.  The exponent is not sharp — the
integrating factor gives `max(Re z, u')` — and does not need to be. -/
theorem exists_norm_delangeAbel_le_rpow {z : ℂ} (hz : ‖z‖ = 1) (hzne : z ≠ 1)
    (hu1 : ‖z - 1‖ < 1) :
    ∃ C θ : ℝ, ∃ N₀ : ℕ, 0 < C ∧ 0 ≤ θ ∧ θ < 1 ∧ 3 ≤ N₀ ∧
      ∀ N, N₀ ≤ N → ‖delangeAbel z N‖ ≤ C * (Real.log (N : ℝ)) ^ θ := by
  obtain ⟨C₁, u', M₀, hC1pos, hu'0, hu'1, hM03, hA⟩ := exists_delangeA_le_rpow hu1
  have hre := re_lt_one_of_norm_one z hz hzne
  have hn : z.re * z.re + z.im * z.im = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simp only [Complex.normSq_apply] at h
    nlinarith [h]
  have hreg : (-1 : ℝ) ≤ z.re := by nlinarith [hn, mul_self_nonneg z.im]
  -- the exponent, strictly between `max (Re z) u'` and `1`
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = (max z.re u' + 1) / 2 := ⟨_, rfl⟩
  have hθu' : u' < θ := by rw [hθdef]; have := le_max_right z.re u'; linarith
  have hθre : z.re < θ := by rw [hθdef]; have := le_max_left z.re u'; linarith
  have hθ1 : θ < 1 := by
    rw [hθdef]
    have : max z.re u' < 1 := max_lt hre hu'1
    linarith
  have hθ0 : 0 ≤ θ := by rw [hθdef]; have := le_max_right z.re u'; linarith
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = θ - z.re := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; linarith
  have hθeq : θ = z.re + κ := by rw [hκdef]; ring
  obtain ⟨N₀, hN0def⟩ : ∃ N₀ : ℕ, N₀ = max M₀ (max 3 ⌈(3 / κ : ℝ)⌉₊) := ⟨_, rfl⟩
  have h03 : 3 ≤ N₀ := by
    rw [hN0def]; exact le_trans (le_max_left 3 _) (le_max_right M₀ _)
  have hM0N0 : M₀ ≤ N₀ := by rw [hN0def]; exact le_max_left _ _
  have hs3 : ∀ m, N₀ ≤ m → logRatioStep m ≤ κ / 3 := by
    intro m hm
    have hm3 : 3 ≤ m := le_trans h03 hm
    have hceil : (3 / κ : ℝ) ≤ (m : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      have hc : ⌈(3 / κ : ℝ)⌉₊ ≤ m := by
        refine le_trans ?_ hm
        rw [hN0def]
        exact le_trans (le_max_right 3 _) (le_max_right M₀ _)
      exact_mod_cast hc
    have hκ3 : (0 : ℝ) < 3 / κ := by positivity
    calc logRatioStep m ≤ 1 / (m : ℝ) := logRatioStep_le_inv hm3
      _ ≤ 1 / (3 / κ) := one_div_le_one_div_of_le hκ3 hceil
      _ = κ / 3 := by field_simp
  -- the constant
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = 38 * C₁ / κ + ‖delangeAbel z N₀‖ + 1 := ⟨_, rfl⟩
  have hdivnn : (0 : ℝ) ≤ 38 * C₁ / κ := by positivity
  have hCpos : 0 < C := by rw [hCdef]; linarith [norm_nonneg (delangeAbel z N₀)]
  have hCA : ‖delangeAbel z N₀‖ ≤ C := by rw [hCdef]; linarith
  have hCκ : 38 * C₁ ≤ C * κ := by
    have hbase : 38 * C₁ / κ ≤ C := by rw [hCdef]; linarith [norm_nonneg (delangeAbel z N₀)]
    calc 38 * C₁ = (38 * C₁ / κ) * κ := by field_simp
      _ ≤ C * κ := mul_le_mul_of_nonneg_right hbase hκ.le
  refine ⟨C, θ, N₀, hCpos, hθ0, hθ1, h03, ?_⟩
  intro N hN
  induction N, hN using Nat.le_induction with
  | base =>
      have hL := one_le_log_cast h03
      have hone : (1 : ℝ) ≤ (Real.log (N₀ : ℝ)) ^ θ := by
        calc (1 : ℝ) = (1 : ℝ) ^ θ := (Real.one_rpow θ).symm
          _ ≤ (Real.log (N₀ : ℝ)) ^ θ := Real.rpow_le_rpow (by norm_num) hL hθ0
      nlinarith [hCA, hone, hCpos]
  | succ N hN ih =>
      have hm3 : 3 ≤ N := le_trans h03 hN
      have hm1 : 1 ≤ N := by omega
      have hs0 := logRatioStep_nonneg hm3
      have hL := one_le_log_cast hm3
      have hLpos : (0 : ℝ) < Real.log (N : ℝ) := by linarith
      have hPnn : (0 : ℝ) ≤ (Real.log (N : ℝ)) ^ θ := Real.rpow_nonneg hLpos.le _
      -- the recursion
      have hsplit : delangeAbel z (N + 1)
          = delangeAbel z N
            + ((Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) : ℝ) : ℂ) * delangeS z N := by
        rw [delangeAbel, delangeAbel, Finset.sum_Ico_succ_top hm1]
      have hdelta : ((Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) : ℝ) : ℂ)
          = ((logRatioStep N : ℝ) : ℂ) * ((Real.log (N : ℝ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        rw [logRatioStep]
        field_simp
      have hrec : delangeAbel z (N + 1)
          = delangeAbel z N * (1 + z * ((logRatioStep N : ℝ) : ℂ))
            + ((logRatioStep N : ℝ) : ℂ)
              * (delangeS z N * ((Real.log (N : ℝ) : ℝ) : ℂ) - z * delangeAbel z N) := by
        rw [hsplit, hdelta]; ring
      have hsc := delange_scale_equation hu1.le N
      have hfac : (0 : ℝ) ≤ 1 + logRatioStep N * z.re + (logRatioStep N) ^ 2 / 2 := by
        nlinarith [mul_nonneg hs0 (show (0:ℝ) ≤ z.re + 1 by linarith),
          sq_nonneg (logRatioStep N - 1)]
      have hnorm : ‖delangeAbel z (N + 1)‖
          ≤ ‖delangeAbel z N‖ * (1 + logRatioStep N * z.re + (logRatioStep N) ^ 2 / 2)
            + logRatioStep N * (19 * delangeA z N) := by
        rw [hrec]
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
        exact add_le_add (mul_le_mul_of_nonneg_left (norm_one_add_mul_ofReal_le hz hs0)
          (norm_nonneg _)) (mul_le_mul_of_nonneg_left hsc hs0)
      -- the scalar step inequality
      have hscalar : C * (1 + logRatioStep N * z.re + (logRatioStep N) ^ 2 / 2)
            + logRatioStep N * (19 * C₁)
          ≤ C * (1 + θ * logRatioStep N - (logRatioStep N) ^ 2) := by
        rw [hθeq]
        nlinarith [mul_nonneg hs0 (show (0:ℝ) ≤ C * κ / 2 - 19 * C₁ by linarith),
          mul_nonneg (mul_nonneg hCpos.le hs0)
            (show (0:ℝ) ≤ κ / 3 - logRatioStep N by linarith [hs3 N hN])]
      have hAN : delangeA z N ≤ C₁ * (Real.log (N : ℝ)) ^ θ := by
        refine le_trans (hA N (le_trans hM0N0 hN)) ?_
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hL hθu'.le) hC1pos.le
      have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hLsucc : (Real.log ((N : ℝ) + 1)) ^ θ
          = (Real.log (N : ℝ)) ^ θ * (1 + logRatioStep N) ^ θ := by
        rw [log_succ_eq_mul hm3, Real.mul_rpow hLpos.le (by linarith)]
      rw [hLsucc]
      have hber := one_add_rpow_ge hs0 hθ0 hθ1.le
      calc ‖delangeAbel z (N + 1)‖
          ≤ ‖delangeAbel z N‖ * (1 + logRatioStep N * z.re + (logRatioStep N) ^ 2 / 2)
            + logRatioStep N * (19 * delangeA z N) := hnorm
        _ ≤ (C * (Real.log (N : ℝ)) ^ θ)
              * (1 + logRatioStep N * z.re + (logRatioStep N) ^ 2 / 2)
            + logRatioStep N * (19 * (C₁ * (Real.log (N : ℝ)) ^ θ)) := by
              refine add_le_add (mul_le_mul_of_nonneg_right ih hfac) ?_
              exact mul_le_mul_of_nonneg_left (by linarith) hs0
        _ ≤ (C * (Real.log (N : ℝ)) ^ θ)
              * (1 + θ * logRatioStep N - (logRatioStep N) ^ 2) := by
              nlinarith [mul_le_mul_of_nonneg_left hscalar hPnn]
        _ ≤ (C * (Real.log (N : ℝ)) ^ θ) * ((1 + logRatioStep N) ^ θ) := by
              exact mul_le_mul_of_nonneg_left hber (mul_nonneg hCpos.le hPnn)
        _ = C * ((Real.log (N : ℝ)) ^ θ * (1 + logRatioStep N) ^ θ) := by ring


/-! ### The closure: `DelangeKernelMean` on `0 < ‖z−1‖ < 1` -/

lemma rpow_sub_one_mul {L : ℝ} (hL : 0 < L) (θ : ℝ) : L ^ θ = L ^ (θ - 1) * L := by
  have h := (Real.rpow_add hL (θ - 1) 1).symm
  rw [Real.rpow_one] at h
  rw [h]
  congr 1
  ring

/-- **THE DISCHARGE.**  `Σ_{n≤N} h_z(n)/n → 0` for every `z` on the unit circle with
`z ≠ 1` and `‖z−1‖ < 1`, unconditionally.  Mechanism: the scale equation
`‖S(N)·log N − z·Abel(N)‖ ≤ 19A(N)` with `‖Abel(N)‖ ≤ C(log N)^θ` (brick 3) and
`A(N) ≤ C₁(log N)^{u'}` (brick 2) gives `‖S(N)‖ ≤ (C+19C₁)(log N)^{ϑ−1}` with `ϑ < 1`. -/
theorem delangeKernelMean_of_norm_lt_one {z : ℂ} (hz : ‖z‖ = 1) (hzne : z ≠ 1)
    (hu1 : ‖z - 1‖ < 1) : DelangeKernelMean z := by
  obtain ⟨C₁, u', M₀, hC1pos, hu'0, hu'1, hM03, hA⟩ := exists_delangeA_le_rpow hu1
  obtain ⟨C, θ, N₁, hCpos, hθ0, hθ1, hN13, hAbel⟩ :=
    exists_norm_delangeAbel_le_rpow hz hzne hu1
  obtain ⟨ϑ, hϑdef⟩ : ∃ ϑ : ℝ, ϑ = max θ u' := ⟨_, rfl⟩
  have hϑ0 : 0 ≤ ϑ := by rw [hϑdef]; exact le_trans hθ0 (le_max_left _ _)
  have hϑ1 : ϑ < 1 := by rw [hϑdef]; exact max_lt hθ1 hu'1
  have hθϑ : θ ≤ ϑ := by rw [hϑdef]; exact le_max_left _ _
  have hu'ϑ : u' ≤ ϑ := by rw [hϑdef]; exact le_max_right _ _
  obtain ⟨N₂, hN2def⟩ : ∃ N₂ : ℕ, N₂ = max M₀ N₁ := ⟨_, rfl⟩
  have hN23 : 3 ≤ N₂ := by rw [hN2def]; exact le_trans hM03 (le_max_left _ _)
  -- the majorant
  have hlim : Tendsto (fun N : ℕ => (C + 19 * C₁) * (Real.log (N : ℝ)) ^ (ϑ - 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ (ϑ - 1)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 - ϑ by linarith)
      simpa [neg_sub] using this
    have h2 : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    simpa using (h1.comp h2).const_mul (C + 19 * C₁)
  show Tendsto (fun N : ℕ => delangeS z N) atTop (𝓝 0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop N₂] with N hN
  have hM0N : M₀ ≤ N := le_trans (by rw [hN2def]; exact le_max_left _ _) hN
  have hN1N : N₁ ≤ N := le_trans (by rw [hN2def]; exact le_max_right _ _) hN
  have hN3 : 3 ≤ N := le_trans hN23 hN
  have hL := one_le_log_cast hN3
  have hLpos : (0 : ℝ) < Real.log (N : ℝ) := by linarith
  -- from the scale equation
  have hsc := delange_scale_equation hu1.le N
  have hsplit : ‖delangeS z N * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      ≤ ‖z * delangeAbel z N‖ + 19 * delangeA z N := by
    have h := norm_sub_norm_le (delangeS z N * ((Real.log (N : ℝ) : ℝ) : ℂ))
      (z * delangeAbel z N)
    linarith
  have hlhs : ‖delangeS z N * ((Real.log (N : ℝ) : ℝ) : ℂ)‖
      = ‖delangeS z N‖ * Real.log (N : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLpos.le]
  have hzabel : ‖z * delangeAbel z N‖ = ‖delangeAbel z N‖ := by
    rw [norm_mul, hz, one_mul]
  -- the two rpow majorisations, at the common exponent `ϑ`
  have h1 : ‖delangeAbel z N‖ ≤ C * (Real.log (N : ℝ)) ^ ϑ :=
    le_trans (hAbel N hN1N)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hθϑ) hCpos.le)
  have h2 : delangeA z N ≤ C₁ * (Real.log (N : ℝ)) ^ ϑ :=
    le_trans (hA N hM0N)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hu'ϑ) hC1pos.le)
  have hmain : ‖delangeS z N‖ * Real.log (N : ℝ)
      ≤ ((C + 19 * C₁) * (Real.log (N : ℝ)) ^ (ϑ - 1)) * Real.log (N : ℝ) := by
    have hstep : ‖delangeS z N‖ * Real.log (N : ℝ) ≤ (C + 19 * C₁) * (Real.log (N : ℝ)) ^ ϑ := by
      rw [← hlhs]
      rw [hzabel] at hsplit
      linarith
    calc ‖delangeS z N‖ * Real.log (N : ℝ) ≤ (C + 19 * C₁) * (Real.log (N : ℝ)) ^ ϑ := hstep
      _ = ((C + 19 * C₁) * (Real.log (N : ℝ)) ^ (ϑ - 1)) * Real.log (N : ℝ) := by
          rw [rpow_sub_one_mul hLpos ϑ]; ring
  exact le_of_mul_le_mul_right hmain hLpos

/-- **`DelangeMean t` — the 🟡 axiom, DISCHARGED on `‖phase t − 1‖ < 1`.**  The cited hypothesis
of `SwingC1Delange.lean` is a theorem in this regime, with no analytic number theory: two exact
hyperbola identities, Mertens' FIRST theorem, and elementary summation. -/
theorem delangeMean_of_norm_lt_one (t : ℝ) (htne : phase t ≠ 1) (ht : ‖phase t - 1‖ < 1) :
    DelangeMean t :=
  delangeMean_of_kernelMean t ht (delangeKernelMean_of_norm_lt_one (norm_phase t) htne ht)

end NormalNumbers.CastingOut
