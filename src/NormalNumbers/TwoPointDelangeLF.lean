import NormalNumbers.TwoPointDelangeTail
import NormalNumbers.TwoPointKataiRearrange

/-!
# The Levin–Fainleib identity for the Delange kernel

`TwoPointDelangeTail.lean` discharged one of the two residues of the `DelangeMean` axiom.  The
remaining one is `DelangeKernelMean z : Σ_{n ≤ N} h_z(n)/n → 0`, `h_z = μ · z^ω`.

**Rankin's trick cannot do it** (recorded here so it is not retried): for `u = ‖z−1‖ ∈ (0,1)` the
absolute sum `Σ_{n ≤ N} μ²(n) u^{ω(n)}/n ≍ (log N)^u` DIVERGES, while the Euler product
`Π_{p≤N}(1+(z−1)/p)` has modulus `≍ (log N)^{Re z − 1} → 0`.  So the sum and its product differ by
a smooth tail that is *larger* than either, and the comparison is irreducibly a cancellation
statement — there is no absolute-value route from `prod_delangeLocal_tendsto_zero` to
`DelangeKernelMean`.

The correct engine is Levin–Fainleib/Wirsing, which runs on the `log`-weighted sum.  This file
proves its exact starting identity, with no analytic input at all:

    Σ_{n ≤ N} h(n) log n / n  =  (z−1) · Σ_{p ≤ N} (log p / p) · Σ_{m ≤ N/p, p ∤ m} h(m)/m .

Both the "`log n` splits over the prime factors of a squarefree `n`" step and the reindexing
`n = p·m` are exact, so the identity holds for every `N`.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- For squarefree `n ≠ 0`, `log n` is the plain sum of `log p` over its prime factors. -/
lemma log_eq_sum_log_primeFactors {n : ℕ} (hn : n ≠ 0) (hsq : Squarefree n) :
    Real.log n = ∑ p ∈ n.primeFactors, Real.log p := by
  classical
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
  rw [Nat.cast_prod, Real.log_prod]
  intro p hp
  have hpos := (Nat.prime_of_mem_primeFactors hp).pos
  exact_mod_cast hpos.ne'

/-- **The kernel is multiplicative at a prime.**  `h(pm) = (z−1)·h(m)` when `p ∤ m`, and `0`
otherwise. -/
lemma delangeKernel_prime_mul {z : ℂ} {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    delangeKernel z (p * m) = if p ∣ m then 0 else (z - 1) * delangeKernel z m := by
  classical
  by_cases hdvd : p ∣ m
  · rw [if_pos hdvd]
    obtain ⟨c, rfl⟩ := hdvd
    have hns : ¬ Squarefree (p * (p * c)) := by
      intro hsq
      have : p * p ∣ p * (p * c) := ⟨c, by ring⟩
      exact hp.not_isUnit (hsq p this)
    rw [delangeKernel, if_neg hns]
  · rw [if_neg hdvd]
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd
    have hsqiff : Squarefree (p * m) ↔ Squarefree m := by
      rw [Nat.squarefree_mul hcop]
      exact ⟨fun h => h.2, fun h => ⟨hp.squarefree, h⟩⟩
    have homega : omegaNat (p * m) = omegaNat m + 1 := by
      rw [omegaNat_mul_coprime hp.pos.ne' hm hcop]
      have : omegaNat p = 1 := by
        simp [omegaNat, Nat.Prime.primeFactors hp]
      omega
    by_cases hsq : Squarefree m
    · rw [delangeKernel, delangeKernel, if_pos (hsqiff.mpr hsq), if_pos hsq, homega]
      ring
    · rw [delangeKernel, delangeKernel, if_neg (fun h => hsq (hsqiff.mp h)), if_neg hsq, mul_zero]

/-- **THE LEVIN–FAINLEIB IDENTITY.**  Exact, for every `N`. -/
theorem sum_delangeKernel_mul_log (z : ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, delangeKernel z n * (Real.log n : ℂ) / (n : ℂ)
      = (z - 1) * ∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ))
          * ∑ m ∈ (Finset.Ioc 0 (N / p)).filter (fun m => ¬ p ∣ m),
              delangeKernel z m / (m : ℂ) := by
  classical
  -- Step 1: split `log n` over the prime factors, as a sum over `primesLe N`.
  have hstep : ∀ n ∈ Finset.Ioc 0 N,
      delangeKernel z n * (Real.log n : ℂ) / (n : ℂ)
        = ∑ p ∈ primesLe N,
            (if p ∣ n then delangeKernel z n * (Real.log p : ℂ) / (n : ℂ) else 0) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    by_cases hsq : Squarefree n
    · have hn0 : n ≠ 0 := by omega
      have hsub : n.primeFactors ⊆ primesLe N := by
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hple : p ≤ N := le_trans (Nat.le_of_dvd (by omega)
          (Nat.dvd_of_mem_primeFactors hp)) hn.2
        simp only [primesLe, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hpp⟩
      have hfil : ∑ p ∈ primesLe N,
          (if p ∣ n then delangeKernel z n * (Real.log p : ℂ) / (n : ℂ) else 0)
          = ∑ p ∈ n.primeFactors, delangeKernel z n * (Real.log p : ℂ) / (n : ℂ) := by
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ fun p _ => rfl
        ext p
        simp only [Finset.mem_filter, Nat.mem_primeFactors]
        constructor
        · rintro ⟨hmem, hdvd⟩
          exact ⟨prime_of_mem_primesLe hmem, hdvd, hn0⟩
        · rintro ⟨hpp, hdvd, -⟩
          exact ⟨hsub (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, hn0⟩), hdvd⟩
      rw [hfil, ← Finset.sum_div, ← Finset.mul_sum]
      congr 2
      rw [log_eq_sum_log_primeFactors hn0 hsq]
      push_cast
      rfl
    · simp [delangeKernel, hsq]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp := prime_of_mem_primesLe hp
  -- Step 2: reindex `n = p·m` on the multiples of `p`.
  rw [← Finset.sum_filter,
    sum_multiples_reindex p N hpp.pos
      (fun n => delangeKernel z n * (Real.log p : ℂ) / (n : ℂ))]
  -- Step 3: use `h(pm) = (z−1)h(m)·[p ∤ m]`.
  have hinner : ∀ m ∈ Finset.Ioc 0 (N / p),
      delangeKernel z (p * m) * (Real.log p : ℂ) / ((p * m : ℕ) : ℂ)
        = (z - 1) * ((Real.log p : ℂ) / (p : ℂ))
            * (if ¬ p ∣ m then delangeKernel z m / (m : ℂ) else 0) := by
    intro m hm
    simp only [Finset.mem_Ioc] at hm
    have hm0 : m ≠ 0 := by omega
    have hpc : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hpp.pos.ne'
    have hmc : ((m : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hm0
    rw [delangeKernel_prime_mul hpp hm0]
    by_cases hdvd : p ∣ m
    · simp [hdvd]
    · simp only [hdvd, if_false, not_false_eq_true, if_true, if_neg]
      push_cast
      field_simp
      try ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, ← Finset.sum_filter, mul_assoc]

/-! ### Removing the `p ∤ m` restriction, and the working inequality -/

/-- The truncated kernel sum.  `DelangeKernelMean z` is exactly `delangeS z N → 0`. -/
noncomputable def delangeS (z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, delangeKernel z n / (n : ℂ)

/-- Its absolute companion `Σ_{n≤N} μ²(n) u^{ω(n)}/n`. -/
noncomputable def delangeA (z : ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N, ‖delangeKernel z n‖ / (n : ℝ)

/-- The sum restricted to `m` coprime to `p`, as it appears in the Levin–Fainleib identity. -/
noncomputable def delangeSrestr (z : ℂ) (p M : ℕ) : ℂ :=
  ∑ m ∈ (Finset.Ioc 0 M).filter (fun m => ¬ p ∣ m), delangeKernel z m / (m : ℂ)

/-- The `log`-weighted sum. -/
noncomputable def delangeT (z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, delangeKernel z n * (Real.log n : ℂ) / (n : ℂ)

lemma delangeA_nonneg (z : ℂ) (N : ℕ) : 0 ≤ delangeA z N :=
  Finset.sum_nonneg fun n _ => by positivity

lemma delangeA_mono (z : ℂ) {M N : ℕ} (h : M ≤ N) : delangeA z M ≤ delangeA z N := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
  exact Finset.Ioc_subset_Ioc_right h

/-- **The restriction is a one-step recursion**, not a loss: removing `p ∤ m` costs exactly one
more application of the same prime step, scaled by `(z−1)/p`. -/
theorem delangeSrestr_rec (z : ℂ) {p : ℕ} (hp : p.Prime) (M : ℕ) :
    delangeSrestr z p M = delangeS z M - ((z - 1) / (p : ℂ)) * delangeSrestr z p (M / p) := by
  classical
  have hpc : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne'
  have hsplit : delangeS z M
      = delangeSrestr z p M
        + ∑ n ∈ (Finset.Ioc 0 M).filter (fun n => p ∣ n), delangeKernel z n / (n : ℂ) := by
    rw [delangeS, delangeSrestr, add_comm]
    exact (Finset.sum_filter_add_sum_filter_not _ (fun n => p ∣ n) _).symm
  have hmul : ∑ n ∈ (Finset.Ioc 0 M).filter (fun n => p ∣ n), delangeKernel z n / (n : ℂ)
      = ((z - 1) / (p : ℂ)) * delangeSrestr z p (M / p) := by
    rw [sum_multiples_reindex p M hp.pos (fun n => delangeKernel z n / (n : ℂ))]
    rw [delangeSrestr, Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.mem_Ioc] at hj
    have hj0 : j ≠ 0 := by omega
    have hjc : ((j : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hj0
    rw [delangeKernel_prime_mul hp hj0]
    by_cases hdvd : p ∣ j
    · rw [if_pos hdvd, if_neg (not_not_intro hdvd)]
      simp
    · rw [if_neg hdvd, if_pos hdvd]
      push_cast
      field_simp
      try ring
  rw [hsplit, hmul]
  ring

/-- Removing the restriction costs at most `u/p · A(M)`. -/
theorem norm_delangeSrestr_le (z : ℂ) {p : ℕ} (hp : p.Prime) (M : ℕ) :
    ‖delangeSrestr z p M‖ ≤ ‖delangeS z M‖ + ‖z - 1‖ / (p : ℝ) * delangeA z M := by
  classical
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have htail : ‖delangeSrestr z p (M / p)‖ ≤ delangeA z M := by
    refine le_trans (norm_sum_le _ _) ?_
    have hcongr : ∀ n : ℕ, ‖delangeKernel z n / (n : ℂ)‖ = ‖delangeKernel z n‖ / (n : ℝ) :=
      fun n => by rw [norm_div, Complex.norm_natCast]
    have h1 : ∑ m ∈ (Finset.Ioc 0 (M / p)).filter (fun m => ¬ p ∣ m),
        ‖delangeKernel z m / (m : ℂ)‖ ≤ delangeA z (M / p) := by
      rw [Finset.sum_congr rfl (fun n _ => hcongr n), delangeA]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ => by positivity)
    exact le_trans h1 (delangeA_mono z (Nat.div_le_self M p))
  have hrec := delangeSrestr_rec z hp M
  rw [hrec]
  refine le_trans (norm_sub_le _ _) ?_
  have hnorm : ‖((z - 1) / (p : ℂ)) * delangeSrestr z p (M / p)‖
      = ‖z - 1‖ / (p : ℝ) * ‖delangeSrestr z p (M / p)‖ := by
    rw [norm_mul, norm_div, Complex.norm_natCast]
  rw [hnorm]
  have hc : (0 : ℝ) ≤ ‖z - 1‖ / (p : ℝ) := by positivity
  nlinarith [htail, hc]

/-- **THE WORKING INEQUALITY.**  Levin–Fainleib, with the restriction removed and everything
explicit: no `O(·)`, no hidden constant. -/
theorem norm_delangeT_le (z : ℂ) (N : ℕ) :
    ‖delangeT z N‖
      ≤ ‖z - 1‖ * ∑ p ∈ primesLe N, Real.log p / (p : ℝ)
          * (‖delangeS z (N / p)‖ + ‖z - 1‖ / (p : ℝ) * delangeA z (N / p)) := by
  classical
  rw [delangeT, sum_delangeKernel_mul_log z N, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
  have hpp := prime_of_mem_primesLe hp
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
  have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog]
  exact mul_le_mul_of_nonneg_left (norm_delangeSrestr_le z hpp (N / p)) (by positivity)

/-- The named residue, restated on `delangeS`: this is literally `DelangeKernelMean`. -/
theorem delangeKernelMean_iff (z : ℂ) :
    DelangeKernelMean z ↔ Tendsto (fun N => delangeS z N) atTop (𝓝 0) := Iff.rfl

/-! ### Abel summation: `S(N) log N = T(N) + Σ_{m<N} (log(m+1) − log m)·S(m)`

The purely discrete form of `Σ_{n≤N}(h(n)/n)log(N/n) = ∫_1^N S(t) dt/t`.  Writing
`log(N/n) = Σ_{m=n}^{N−1}(log(m+1) − log m)` and swapping turns the `log`-weighted sum into a
weighted average of `S` at SMALLER arguments — which is exactly the shape a Gronwall/Wirsing
induction consumes.  Proved by induction on `N`, so no integrals are needed. -/

/-- The Abel term `Σ_{1 ≤ m < N} (log(m+1) − log m)·S(m)`. -/
noncomputable def delangeAbel (z : ℂ) (N : ℕ) : ℂ :=
  ∑ m ∈ Finset.Ico 1 N, ((Real.log (m + 1) - Real.log m : ℝ) : ℂ) * delangeS z m

/-- **Discrete Abel summation for the kernel sum.**  Exact, for every `N`. -/
theorem delangeS_mul_log (z : ℂ) (N : ℕ) :
    delangeS z N * (Real.log N : ℂ) = delangeT z N + delangeAbel z N := by
  classical
  induction N with
  | zero => simp [delangeS, delangeT, delangeAbel]
  | succ N ih =>
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        simp [delangeS, delangeT, delangeAbel]
      have hS : delangeS z (N + 1)
          = delangeS z N + delangeKernel z (N + 1) / ((N + 1 : ℕ) : ℂ) := by
        rw [delangeS, delangeS, Finset.sum_Ioc_succ_top (by omega)]
      have hT : delangeT z (N + 1)
          = delangeT z N
            + delangeKernel z (N + 1) * (Real.log ((N + 1 : ℕ) : ℝ) : ℂ) / ((N + 1 : ℕ) : ℂ) := by
        rw [delangeT, delangeT, Finset.sum_Ioc_succ_top (by omega)]
      have hA : delangeAbel z (N + 1)
          = delangeAbel z N
            + ((Real.log ((N : ℝ) + 1) - Real.log (N : ℝ) : ℝ) : ℂ) * delangeS z N := by
        rw [delangeAbel, delangeAbel, Finset.sum_Ico_succ_top (by omega)]
      have hc1 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      have hc2 : ((N + 1 : ℕ) : ℂ) = (N : ℂ) + 1 := by push_cast; ring
      have hpush : (((Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) : ℝ) : ℂ)
          = ((Real.log ((N : ℝ) + 1) : ℝ) : ℂ) - ((Real.log (N : ℝ) : ℝ) : ℂ) :=
        Complex.ofReal_sub _ _
      rw [hS, hT, hA, hc1, hc2, hpush]
      linear_combination ih

/-- `log(m+1) − log m ≤ 1/m`. -/
lemma log_succ_sub_log_le {m : ℕ} (hm : 1 ≤ m) :
    Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hx : (0 : ℝ) < ((m : ℝ) + 1) / (m : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (by positivity) (ne_of_gt hmR)] at h
  have heq : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by field_simp; ring
  rw [heq] at h
  exact h

lemma log_succ_sub_log_nonneg {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have := Real.log_le_log hmR (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)
  linarith

/-- **The Gronwall shape.**  `‖Abel(N)‖ ≤ Σ_{1 ≤ m < N} ‖S(m)‖/m`. -/
theorem norm_delangeAbel_le (z : ℂ) (N : ℕ) :
    ‖delangeAbel z N‖ ≤ ∑ m ∈ Finset.Ico 1 N, ‖delangeS z m‖ / (m : ℝ) := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m hm => ?_)
  simp only [Finset.mem_Ico] at hm
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (log_succ_sub_log_nonneg hm.1)]
  have h := log_succ_sub_log_le hm.1
  have hS : (0 : ℝ) ≤ ‖delangeS z m‖ := norm_nonneg _
  calc (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * ‖delangeS z m‖
      ≤ (1 / (m : ℝ)) * ‖delangeS z m‖ := mul_le_mul_of_nonneg_right h hS
    _ = ‖delangeS z m‖ / (m : ℝ) := by ring

/-- **THE RECURSION.**  Combining Abel summation with the Levin–Fainleib inequality:

    ‖S(N)‖·log N  ≤  u·Σ_{p≤N} (log p/p)·(‖S(N/p)‖ + (u/p)·A(N/p))  +  Σ_{m<N} ‖S(m)‖/m .

Both right-hand terms involve `S` only at arguments `< N`, so this is a genuine induction on `N` —
the Wirsing endgame.  No analytic input has been used anywhere to reach this point. -/
theorem norm_delangeS_mul_log_le (z : ℂ) (N : ℕ) :
    ‖delangeS z N‖ * Real.log N
      ≤ ‖z - 1‖ * (∑ p ∈ primesLe N, Real.log p / (p : ℝ)
            * (‖delangeS z (N / p)‖ + ‖z - 1‖ / (p : ℝ) * delangeA z (N / p)))
        + ∑ m ∈ Finset.Ico 1 N, ‖delangeS z m‖ / (m : ℝ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero, Real.log_zero, mul_zero]
    have h1 : (0 : ℝ) ≤ ‖z - 1‖ * (∑ p ∈ primesLe 0, Real.log p / (p : ℝ)
        * (‖delangeS z (0 / p)‖ + ‖z - 1‖ / (p : ℝ) * delangeA z (0 / p))) := by
      refine mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun p hp => ?_)
      have hpp := prime_of_mem_primesLe hp
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
      have hlog : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
      have hA := delangeA_nonneg z (0 / p)
      have : (0 : ℝ) ≤ ‖delangeS z (0 / p)‖ + ‖z - 1‖ / (p : ℝ) * delangeA z (0 / p) := by
        positivity
      positivity
    rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, add_zero]
    exact h1
  have hid := delangeS_mul_log z N
  have hnorm : ‖delangeS z N‖ * Real.log N ≤ ‖delangeT z N‖ + ‖delangeAbel z N‖ := by
    have hlog : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    have : ‖delangeS z N * (Real.log N : ℂ)‖ = ‖delangeS z N‖ * Real.log N := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
    rw [← this, hid]
    exact norm_add_le _ _
  linarith [hnorm, norm_delangeT_le z N, norm_delangeAbel_le z N]

/-! ### The absolute companion `A(N)` is dominated by its Euler product

`A(N) = Σ_{n≤N} μ²(n) u^{ω(n)}/n` appears in the recursion's error term.  Expanding
`Π_{p≤N}(1 + u/p)` over subsets of `primesLe N` produces exactly the terms `u^{ω(n)}/n` for the
squarefree `n` built from those primes — a superset of the `n ≤ N`, and all terms are nonnegative.
So the bound is an inclusion of index sets, with no estimate anywhere. -/

/-- Squarefree naturals are determined by their prime-factor sets. -/
lemma primeFactors_injOn_squarefree :
    Set.InjOn Nat.primeFactors {n : ℕ | n ≠ 0 ∧ Squarefree n} := by
  rintro m ⟨hm0, hm⟩ n ⟨hn0, hn⟩ h
  rw [← Nat.prod_primeFactors_of_squarefree hm, ← Nat.prod_primeFactors_of_squarefree hn, h]

/-- **`A(N) ≤ Π_{p≤N}(1 + u/p)`.**  Pure index-set inclusion: no estimate is used. -/
theorem delangeA_le_prod (z : ℂ) (N : ℕ) :
    delangeA z N ≤ ∏ p ∈ primesLe N, (1 + ‖z - 1‖ / (p : ℝ)) := by
  classical
  set u : ℝ := ‖z - 1‖ with hu
  have hu0 : 0 ≤ u := norm_nonneg _
  -- the product, expanded over subsets
  have hprod : ∏ p ∈ primesLe N, (1 + u / (p : ℝ))
      = ∑ t ∈ (primesLe N).powerset, ∏ p ∈ t, (u / (p : ℝ)) := by
    rw [Finset.prod_congr rfl (fun p (_ : p ∈ primesLe N) => add_comm (1 : ℝ) (u / (p : ℝ)))]
    rw [Finset.prod_add]
    simp
  -- the sum, restricted to its support
  have hsupp : delangeA z N
      = ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => Squarefree n), ‖delangeKernel z n‖ / (n : ℝ) := by
    rw [delangeA, ← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 N) (fun n => Squarefree n)]
    have hzero : ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ Squarefree n),
        ‖delangeKernel z n‖ / (n : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      simp only [Finset.mem_filter] at hn
      rw [norm_delangeKernel, if_neg hn.2, zero_div]
    rw [hzero, add_zero]
  -- reindex the sum by prime-factor sets
  have hterm : ∀ n ∈ (Finset.Ioc 0 N).filter (fun n => Squarefree n),
      ‖delangeKernel z n‖ / (n : ℝ) = ∏ p ∈ n.primeFactors, (u / (p : ℝ)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    have hn0 : n ≠ 0 := by omega
    rw [norm_delangeKernel, if_pos hn.2, Finset.prod_div_distrib, Finset.prod_const,
      ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hn.2]
    rfl
  have hinj : ∀ x ∈ (Finset.Ioc 0 N).filter (fun n => Squarefree n),
      ∀ y ∈ (Finset.Ioc 0 N).filter (fun n => Squarefree n),
      x.primeFactors = y.primeFactors → x = y := by
    intro m hm n hn h
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hm hn
    exact primeFactors_injOn_squarefree ⟨by omega, hm.2⟩ ⟨by omega, hn.2⟩ h
  have himg : ((Finset.Ioc 0 N).filter (fun n => Squarefree n)).image Nat.primeFactors
      ⊆ (primesLe N).powerset := by
    intro t ht
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc] at ht
    obtain ⟨n, ⟨⟨hn1, hn2⟩, -⟩, rfl⟩ := ht
    rw [Finset.mem_powerset]
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hple : p ≤ N :=
      le_trans (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)) hn2
    simp only [primesLe, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpp⟩
  have hre : ∑ t ∈ ((Finset.Ioc 0 N).filter (fun n => Squarefree n)).image Nat.primeFactors,
      (∏ p ∈ t, u / (p : ℝ))
      = ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => Squarefree n),
          ∏ p ∈ n.primeFactors, u / (p : ℝ) := Finset.sum_image hinj
  rw [hsupp, Finset.sum_congr rfl hterm, ← hre, hprod]
  refine Finset.sum_le_sum_of_subset_of_nonneg himg fun t _ _ => ?_
  exact Finset.prod_nonneg fun p _ => by positivity

/-! ### The complex step, part I: a convergent `S` forces `T(N) = o(log N)`

Lap 35 recorded that a real-valued Gronwall on `‖S‖` cannot reach `o(1)`; the endgame needs the
complex cancellation.  Here is its first half, and it needs **no Mertens and no analytic input**.

The Abel weights `c_m = log(m+1) − log m` are nonnegative and sum to exactly `log N`
(`sum_log_telescope`), so `Abel(N)/log N` is a regular (Toeplitz) average of `S`: if `S(N) → L`
then `Abel(N)/log N → L`.  Since `S(N)·log N = T(N) + Abel(N)` exactly, this gives
`T(N)/log N → L − L = 0`.

Combined with the Levin–Fainleib identity `T(N) = (z−1)·Σ_{p≤N}(log p/p)·S^{(p)}(N/p)`, whose
right-hand side is `(z−1)·L·log N + o(log N)` once Mertens `Σ_{p≤N} log p/p ~ log N` is available,
this forces `(z−1)L = 0`, i.e. **`L = 0` for `z ≠ 1`**.  So `DelangeKernelMean` reduces to the mere
*convergence* of `S` — its value is then automatic.  Part II (the prime-sum side) is the Mertens
step and is the only remaining analytic input. -/

/-- The Abel weights sum to exactly `log N`. -/
theorem sum_log_telescope (N : ℕ) :
    ∑ m ∈ Finset.Ico 1 N, (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) = Real.log N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN; simp
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      have : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [this]
      ring

/-- **Toeplitz regularity of the Abel average.**  If `S(N) → L` then `Abel(N)/log N → L`. -/
theorem tendsto_delangeAbel_div_log (z : ℂ) {L : ℂ}
    (h : Tendsto (fun N => delangeS z N) atTop (𝓝 L)) :
    Tendsto (fun N => delangeAbel z N / (Real.log N : ℂ)) atTop (𝓝 L) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose a tail where `S` is within `ε/2` of `L`
  obtain ⟨M₀, hM₀⟩ := (Metric.tendsto_atTop.mp h) (ε / 2) (by linarith)
  set C : ℝ := ∑ m ∈ Finset.Ico 1 M₀,
    (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * ‖delangeS z m - L‖ with hC
  have hCnn : 0 ≤ C := by
    refine Finset.sum_nonneg fun m hm => ?_
    simp only [Finset.mem_Ico] at hm
    exact mul_nonneg (log_succ_sub_log_nonneg hm.1) (norm_nonneg _)
  -- `log N → ∞`, so the head contributes `o(1)`
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := (hlog.eventually_gt_atTop (max 1 (2 * C / ε))).exists_forall_of_atTop
  refine ⟨max (max 2 M₀) N₁, fun N hN => ?_⟩
  have hNM₀ : M₀ ≤ N := le_trans (le_trans (le_max_right 2 M₀) (le_max_left _ _)) hN
  have hN2 : 2 ≤ N := le_trans (le_trans (le_max_left 2 M₀) (le_max_left _ _)) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_right _ _) hN
  have hLbig := hN₁ N hNN₁
  have hL1 : (1 : ℝ) < Real.log N := lt_of_le_of_lt (le_max_left _ _) hLbig
  have hL2 : 2 * C / ε < Real.log N := lt_of_le_of_lt (le_max_right _ _) hLbig
  have hLpos : (0 : ℝ) < Real.log N := by linarith
  have hLc : ((Real.log N : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hLpos
  -- the exact decomposition
  have hdecomp : delangeAbel z N - L * ((Real.log N : ℝ) : ℂ)
      = ∑ m ∈ Finset.Ico 1 N,
          ((Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) : ℝ) : ℂ) * (delangeS z m - L) := by
    rw [delangeAbel, ← sum_log_telescope N, Complex.ofReal_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hbound : ‖∑ m ∈ Finset.Ico 1 N,
      ((Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) : ℝ) : ℂ) * (delangeS z m - L)‖
      ≤ C + (ε / 2) * Real.log N := by
    refine le_trans (norm_sum_le _ _) ?_
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Ico 1 N) (fun m => m < M₀)
      (fun m => ‖((Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) : ℝ) : ℂ) * (delangeS z m - L)‖)
    rw [← hsplit]
    have hhead : ∑ m ∈ (Finset.Ico 1 N).filter (fun m => m < M₀),
        ‖((Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) : ℝ) : ℂ) * (delangeS z m - L)‖ ≤ C := by
      have hcongr : ∀ m ∈ (Finset.Ico 1 N).filter (fun m => m < M₀),
          ‖((Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) : ℝ) : ℂ) * (delangeS z m - L)‖
            = (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * ‖delangeS z m - L‖ := by
        intro m hm
        simp only [Finset.mem_filter, Finset.mem_Ico] at hm
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (log_succ_sub_log_nonneg hm.1.1)]
      rw [Finset.sum_congr rfl hcongr, hC]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m hm _ => ?_)
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_Ico] at hm ⊢
        exact ⟨hm.1.1, hm.2⟩
      · simp only [Finset.mem_Ico] at hm
        exact mul_nonneg (log_succ_sub_log_nonneg hm.1) (norm_nonneg _)
    have htail : ∑ m ∈ (Finset.Ico 1 N).filter (fun m => ¬ m < M₀),
        ‖((Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) : ℝ) : ℂ) * (delangeS z m - L)‖
        ≤ (ε / 2) * Real.log N := by
      have hstep : ∀ m ∈ (Finset.Ico 1 N).filter (fun m => ¬ m < M₀),
          ‖((Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) : ℝ) : ℂ) * (delangeS z m - L)‖
            ≤ (ε / 2) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by
        intro m hm
        simp only [Finset.mem_filter, Finset.mem_Ico] at hm
        have hd := hM₀ m (by omega)
        rw [Complex.dist_eq] at hd
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (log_succ_sub_log_nonneg hm.1.1)]
        have hc := log_succ_sub_log_nonneg hm.1.1
        nlinarith [hd, hc]
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.mul_sum]
      have hle : ∑ m ∈ (Finset.Ico 1 N).filter (fun m => ¬ m < M₀),
          (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) ≤ Real.log N := by
        rw [← sum_log_telescope N]
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun m hm _ => ?_
        simp only [Finset.mem_Ico] at hm
        exact log_succ_sub_log_nonneg hm.1
      nlinarith [hle, hε]
    linarith [hhead, htail]
  rw [Complex.dist_eq]
  have hrw : delangeAbel z N / ((Real.log N : ℝ) : ℂ) - L
      = (delangeAbel z N - L * ((Real.log N : ℝ) : ℂ)) / ((Real.log N : ℝ) : ℂ) := by
    field_simp
  rw [hrw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLpos.le, hdecomp,
    div_lt_iff₀ hLpos]
  have hCle : C < (ε / 2) * Real.log N := by
    rcases eq_or_lt_of_le hCnn with hC0 | hC0
    · nlinarith [hLpos, hε]
    · rw [div_lt_iff₀ hε] at hL2
      nlinarith [hL2, hε]
  linarith [hbound, hCle]

/-- **A convergent `S` has `T(N) = o(log N)`.**  Immediate from Abel summation plus Toeplitz. -/
theorem tendsto_delangeT_div_log (z : ℂ) {L : ℂ}
    (h : Tendsto (fun N => delangeS z N) atTop (𝓝 L)) :
    Tendsto (fun N => delangeT z N / (Real.log N : ℂ)) atTop (𝓝 0) := by
  have hA := tendsto_delangeAbel_div_log z h
  have hdiff : Tendsto (fun N : ℕ => delangeS z N - delangeAbel z N / (Real.log N : ℂ))
      atTop (𝓝 (L - L)) := h.sub hA
  rw [sub_self] at hdiff
  refine hdiff.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 1] with N hN
  have hNR : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hLpos : (0 : ℝ) < Real.log N := Real.log_pos hNR
  have hLc : ((Real.log N : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hLpos
  have hid := delangeS_mul_log z N
  rw [eq_div_iff hLc, sub_mul, div_mul_cancel₀ _ hLc]
  linear_combination hid

end NormalNumbers.CastingOut
