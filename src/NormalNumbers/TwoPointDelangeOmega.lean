import NormalNumbers.TwoPointMertensLower

/-!
# The `ω`-weighted Levin–Fainleib identity: a second engine for `DelangeKernelMean`

`TwoPointDelangeLF.lean` runs the classical `log`-weighted identity.  Its Gronwall closure was
refuted in lap 35: passing to `‖·‖` replaces the multiplier `z−1` by `u = ‖z−1‖ > 0`, and the
real fixed point is `θ ≈ u`, i.e. `(log N)^u`, which diverges.  The *sign* `Re(z−1) < 0` — the
only reason `S` tends to `0` at all — is destroyed at that step.

This file provides the identity that keeps the sign available.  Grade the kernel by `ω`:

    S(N; v) = Σ_{k} v^k a_k(N),    a_k(N) = Σ_{n ≤ N, μ²(n)=1, ω(n)=k} 1/n ≥ 0,

so `S(N; ·)` is a *polynomial in `v = z−1`* of degree `≤ log₂ N`, and `∂_v` of it is the
`ω`-weighted sum.  Counting each squarefree `n` once per prime factor gives the exact recursion

    Σ_{n ≤ N} ω(n) h(n)/n  =  (z−1) · Σ_{p ≤ N} (1/p) · S^{(p)}(N/p),

i.e. **`∂_v S(N;v) = Σ_{p ≤ N} (1/p) · S^{(p)}(N/p; v)`** — a differential equation in the
*parameter*, with no `log`, no Abel summation and no Mertens input.  The multiplier on the right
is `Σ_{p≤N} 1/p = log log N + O(1)`, real and positive, so along the ray `v = r e^{iθ}` the energy
obeys

    d/dr ‖S‖²  =  2 Re( conj(S) · e^{iθ} · Σ_p (1/p) S^{(p)}(N/p) )  ≈  2 (log log N) cos θ ‖S‖²,

and `cos θ < 0` exactly when `Re(z−1) < 0`.  That is the decay mechanism the `log`-weighted route
throws away.  The remaining obligation is the same one every route faces — comparing
`S^{(p)}(N/p)` with `S(N)` — but it now sits against a multiplier whose phase is preserved.

This lap lands the exact identity and the grading.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- The `ω`-weighted kernel sum: the `v`-derivative of `S(N; v)` at `v = z − 1`. -/
noncomputable def delangeOmegaT (z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, (omegaNat n : ℂ) * delangeKernel z n / (n : ℂ)

/-- For `0 < n ≤ N`, the primes `p ≤ N` dividing `n` are exactly the prime factors of `n`. -/
lemma filter_dvd_primesLe {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (primesLe N).filter (fun p => p ∣ n) = n.primeFactors := by
  classical
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, primesLe, Finset.mem_range]
  constructor
  · rintro ⟨⟨-, hpp⟩, hdvd⟩
    exact ⟨hpp, hdvd, by omega⟩
  · rintro ⟨hpp, hdvd, -⟩
    have hple : p ≤ N := le_trans (Nat.le_of_dvd hn hdvd) hnN
    exact ⟨⟨by omega, hpp⟩, hdvd⟩

/-- **THE `ω`-WEIGHTED LEVIN–FAINLEIB IDENTITY.**  Exact, for every `N`; no analytic input.
In generating-function form: `∂_v S(N; v) = Σ_{p ≤ N} (1/p) · S^{(p)}(N/p; v)`. -/
theorem delangeOmegaT_eq (z : ℂ) (N : ℕ) :
    delangeOmegaT z N
      = (z - 1) * ∑ p ∈ primesLe N, (1 / (p : ℂ)) * delangeSrestr z p (N / p) := by
  classical
  -- Step 1: `ω(n) = #{p ≤ N : p ∣ n}` for `0 < n ≤ N`.
  have hstep : ∀ n ∈ Finset.Ioc 0 N,
      (omegaNat n : ℂ) * delangeKernel z n / (n : ℂ)
        = ∑ p ∈ primesLe N, (if p ∣ n then delangeKernel z n / (n : ℂ) else 0) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    rw [← Finset.sum_filter, filter_dvd_primesLe hn.1 hn.2, Finset.sum_const, nsmul_eq_mul,
      omegaNat]
    ring
  rw [delangeOmegaT, Finset.sum_congr rfl hstep, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp := prime_of_mem_primesLe hp
  -- Step 2: reindex `n = p·m`.
  rw [← Finset.sum_filter,
    sum_multiples_reindex p N hpp.pos (fun n => delangeKernel z n / (n : ℂ))]
  -- Step 3: `h(pm) = (z−1)·h(m)·[p ∤ m]`.
  have hinner : ∀ m ∈ Finset.Ioc 0 (N / p),
      delangeKernel z (p * m) / ((p * m : ℕ) : ℂ)
        = (z - 1) * (1 / (p : ℂ)) * (if ¬ p ∣ m then delangeKernel z m / (m : ℂ) else 0) := by
    intro m hm
    simp only [Finset.mem_Ioc] at hm
    have hm0 : m ≠ 0 := by omega
    have hpc : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hpp.pos.ne'
    have hmc : ((m : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hm0
    rw [delangeKernel_prime_mul hpp hm0]
    by_cases hdvd : p ∣ m
    · simp [hdvd]
    · simp only [hdvd, not_false_eq_true, if_true, if_neg]
      push_cast
      field_simp
      try ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, ← Finset.sum_filter, mul_assoc,
    delangeSrestr]

/-! ### The grading: `S(N; ·)` is a polynomial with NONNEGATIVE real coefficients

`S(N; v) = Σ_k v^k a_k(N)` with `a_k(N) = Σ_{n ≤ N, μ²(n)=1, ω(n)=k} 1/n ≥ 0`, a finite sum
(`ω(n) ≤ n`).  This is what makes the `v`-derivative identity above a genuine ODE in the
parameter, and it isolates the exact point at which lap 35's Gronwall loses: `‖S(N; v)‖` is
compared with `S(N; ‖v‖) = Σ_k ‖v‖^k a_k(N)`, i.e. with the *same polynomial evaluated on the
positive ray*, where no cancellation between the grades can occur. -/

/-- `a_k(N)`: the mass of the squarefree integers `≤ N` with exactly `k` prime factors. -/
noncomputable def delangeGrade (N k : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => Squarefree n ∧ omegaNat n = k), 1 / (n : ℝ)

lemma delangeGrade_nonneg (N k : ℕ) : 0 ≤ delangeGrade N k :=
  Finset.sum_nonneg fun n _ => by positivity

lemma omegaNat_le_self {n : ℕ} (hn : 0 < n) : omegaNat n ≤ n := by
  classical
  have hsub : n.primeFactors ⊆ Finset.Icc 1 n := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    simp only [Finset.mem_Icc]
    exact ⟨hpp.one_lt.le, Nat.le_of_dvd hn hdvd⟩
  have := Finset.card_le_card hsub
  simpa [omegaNat, Nat.card_Icc] using this

/-- **The grading of `S`.**  `S(N; v) = Σ_{k ≤ N} v^k a_k(N)`, a polynomial identity in `v`. -/
theorem delangeS_grade (z : ℂ) (N : ℕ) :
    delangeS z N = ∑ k ∈ Finset.range (N + 1), (z - 1) ^ k * (delangeGrade N k : ℂ) := by
  classical
  have hmaps : ∀ n ∈ Finset.Ioc 0 N, omegaNat n ∈ Finset.range (N + 1) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp only [Finset.mem_range]
    have := omegaNat_le_self hn.1
    omega
  have hfib := Finset.sum_fiberwise_of_maps_to (g := omegaNat) hmaps
    (fun n => delangeKernel z n / (n : ℂ))
  rw [delangeS, ← hfib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hterm : ∀ n ∈ (Finset.Ioc 0 N).filter (fun n => omegaNat n = k),
      delangeKernel z n / (n : ℂ)
        = if Squarefree n then (z - 1) ^ k * (1 / (n : ℝ) : ℝ) else 0 := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    rw [delangeKernel, hn.2]
    by_cases hsq : Squarefree n
    · simp only [hsq, if_true]
      push_cast
      ring
    · simp [hsq]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.filter_filter,
    delangeGrade, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr ?_ fun n _ => by push_cast; ring
  ext n
  simp only [Finset.mem_filter]
  tauto


/-! ### The parametrised sum and the identity in derivative form

To run the energy argument one needs `S` as a *function of the parameter* `v`, differentiable in
`v`, with `∂_v S` identified.  `delangeSv N` is exactly `delangeS (1+v) N` viewed that way; it is a
polynomial in `v`, so differentiability is free, and the `ω`-identity above becomes the clean

    ∂_v S(N; v) = Σ_{p ≤ N} (1/p) · S^{(p)}(N/p; v),

valid at *every* `v` including `v = 0` (both sides are `Σ_{p≤N} 1/p` there).  Stated in this form
there is no division by `v`, so no case split. -/

/-- `S(N; v) = Σ_{n ≤ N} μ²(n) v^{ω(n)}/n`, as a function of the parameter. -/
noncomputable def delangeSv (N : ℕ) (v : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, (if Squarefree n then v ^ omegaNat n else 0) / (n : ℂ)

/-- The coprimality-restricted companion of `delangeSv`. -/
noncomputable def delangeSvRestr (p M : ℕ) (v : ℂ) : ℂ :=
  ∑ m ∈ (Finset.Ioc 0 M).filter (fun m => ¬ p ∣ m),
    (if Squarefree m then v ^ omegaNat m else 0) / (m : ℂ)

lemma delangeSv_eq (z : ℂ) (N : ℕ) : delangeSv N (z - 1) = delangeS z N := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [delangeKernel]

lemma delangeSvRestr_eq (z : ℂ) (p M : ℕ) : delangeSvRestr p M (z - 1) = delangeSrestr z p M := by
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [delangeKernel]

/-- The formal `v`-derivative of `delangeSv`. -/
noncomputable def delangeSvDeriv (N : ℕ) (v : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N,
    (if Squarefree n then (omegaNat n : ℂ) * v ^ (omegaNat n - 1) else 0) / (n : ℂ)

/-- `p ∤ m` makes `p·m` squarefree exactly when `m` is, and adds one prime factor. -/
lemma squarefree_mul_prime_iff {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hdvd : ¬ p ∣ m) :
    (Squarefree (p * m) ↔ Squarefree m) ∧ omegaNat (p * m) = omegaNat m + 1 := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd
  constructor
  · rw [Nat.squarefree_mul hcop]
    exact ⟨fun h => h.2, fun h => ⟨hp.squarefree, h⟩⟩
  · rw [omegaNat_mul_coprime hp.pos.ne' hm hcop]
    have : omegaNat p = 1 := by simp [omegaNat, Nat.Prime.primeFactors hp]
    omega

/-- Non-squarefree `p·m` when `p ∣ m`. -/
lemma not_squarefree_mul_self {p m : ℕ} (hp : p.Prime) (hdvd : p ∣ m) : ¬ Squarefree (p * m) := by
  obtain ⟨c, rfl⟩ := hdvd
  intro hsq
  have : p * p ∣ p * (p * c) := ⟨c, by ring⟩
  exact hp.not_isUnit (hsq p this)

/-- **The `ω`-identity in derivative form**, with no division by `v`. -/
theorem delangeSvDeriv_eq (N : ℕ) (v : ℂ) :
    delangeSvDeriv N v = ∑ p ∈ primesLe N, (1 / (p : ℂ)) * delangeSvRestr p (N / p) v := by
  classical
  have hstep : ∀ n ∈ Finset.Ioc 0 N,
      (if Squarefree n then (omegaNat n : ℂ) * v ^ (omegaNat n - 1) else 0) / (n : ℂ)
        = ∑ p ∈ primesLe N,
            (if p ∣ n then (if Squarefree n then v ^ (omegaNat n - 1) else 0) / (n : ℂ) else 0) := by
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    rw [← Finset.sum_filter, filter_dvd_primesLe hn.1 hn.2, Finset.sum_const, nsmul_eq_mul,
      omegaNat]
    by_cases hsq : Squarefree n
    · simp only [hsq, if_true, omegaNat]
      ring
    · simp [hsq]
  rw [delangeSvDeriv, Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp := prime_of_mem_primesLe hp
  rw [← Finset.sum_filter,
    sum_multiples_reindex p N hpp.pos
      (fun n => (if Squarefree n then v ^ (omegaNat n - 1) else 0) / (n : ℂ))]
  have hinner : ∀ m ∈ Finset.Ioc 0 (N / p),
      (if Squarefree (p * m) then v ^ (omegaNat (p * m) - 1) else 0) / ((p * m : ℕ) : ℂ)
        = (1 / (p : ℂ))
            * (if ¬ p ∣ m then (if Squarefree m then v ^ omegaNat m else 0) / (m : ℂ) else 0) := by
    intro m hm
    simp only [Finset.mem_Ioc] at hm
    have hm0 : m ≠ 0 := by omega
    have hpc : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hpp.pos.ne'
    have hmc : ((m : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hm0
    by_cases hdvd : p ∣ m
    · rw [if_neg (not_squarefree_mul_self hpp hdvd)]
      simp [hdvd]
    · obtain ⟨hiff, homega⟩ := squarefree_mul_prime_iff hpp hm0 hdvd
      simp only [hdvd, not_false_eq_true, if_true]
      by_cases hsq : Squarefree m
      · rw [if_pos (hiff.mpr hsq), if_pos hsq, homega]
        push_cast
        field_simp
      · rw [if_neg (fun h => hsq (hiff.mp h)), if_neg hsq]
        simp
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, ← Finset.sum_filter, delangeSvRestr]

/-- **`S(N; ·)` is differentiable in the parameter, with the identity as its derivative.**
This is the exact ODE in `v` driving the energy argument: the multiplier
`Σ_{p ≤ N} 1/p = log log N + O(1)` is real and positive. -/
theorem hasDerivAt_delangeSv (N : ℕ) (v : ℂ) :
    HasDerivAt (delangeSv N) (∑ p ∈ primesLe N, (1 / (p : ℂ)) * delangeSvRestr p (N / p) v) v := by
  classical
  rw [← delangeSvDeriv_eq, delangeSvDeriv]
  show HasDerivAt (fun w : ℂ =>
      ∑ n ∈ Finset.Ioc 0 N, (if Squarefree n then w ^ omegaNat n else 0) / (n : ℂ)) _ v
  refine HasDerivAt.fun_sum (A := fun (n : ℕ) (w : ℂ) =>
      (if Squarefree n then w ^ omegaNat n else 0) / (n : ℂ)) fun n _ => ?_
  by_cases hsq : Squarefree n
  · simp only [hsq, if_true]
    exact ((hasDerivAt_pow (omegaNat n) v).div_const (n : ℂ))
  · simp only [hsq, if_false]
    simpa using hasDerivAt_const v (0 : ℂ)


end NormalNumbers.CastingOut
