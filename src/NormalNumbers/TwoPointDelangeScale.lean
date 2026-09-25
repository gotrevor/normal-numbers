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

end NormalNumbers.CastingOut
