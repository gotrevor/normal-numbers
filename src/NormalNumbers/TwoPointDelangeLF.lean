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

end NormalNumbers.CastingOut
