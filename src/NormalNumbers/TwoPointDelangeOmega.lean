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


/-! ### The integrating factor

`L := Σ_{p≤N} 1/p` is real and positive, and the ODE is `∂_v S = L·S + E` with

    E_N(v) := Σ_{p≤N} (1/p)·S^{(p)}(N/p; v) − L·S(N; v) = Σ_{p≤N} (1/p)·( S^{(p)}(N/p;v) − S(N;v) ).

Along the ray `v = r·ξ`, `‖ξ‖ = 1`, the function `H(r) = e^{-c r} S(N; rξ)` with `c = L·ξ` has
`H'(r) = e^{-c r}·ξ·E_N(rξ)` — the whole `L·S` main term is absorbed, and what multiplies the
initial condition is `e^{c}`, of modulus `e^{L·Re ξ}`.  When `Re ξ < 0` (⟺ `Re z < 1`) that is
`(log N)^{-|…|} → 0`. -/

/-- `L = Σ_{p ≤ N} 1/p`, the ODE's multiplier: real, positive, `= log log N + O(1)`. -/
noncomputable def delangeL (N : ℕ) : ℝ := ∑ p ∈ primesLe N, 1 / (p : ℝ)

lemma delangeL_nonneg (N : ℕ) : 0 ≤ delangeL N :=
  Finset.sum_nonneg fun p _ => by positivity

lemma delangeL_cast (N : ℕ) :
    ((delangeL N : ℝ) : ℂ) = ∑ p ∈ primesLe N, (1 / (p : ℂ)) := by
  rw [delangeL]; push_cast; rfl

/-- The scale-comparison error `E_N(v) = Σ_{p≤N} (1/p)·( S^{(p)}(N/p;v) − S(N;v) )`. -/
noncomputable def delangeE (N : ℕ) (v : ℂ) : ℂ :=
  (∑ p ∈ primesLe N, (1 / (p : ℂ)) * delangeSvRestr p (N / p) v) - (delangeL N : ℂ) * delangeSv N v

lemma delangeE_eq_sum (N : ℕ) (v : ℂ) :
    delangeE N v
      = ∑ p ∈ primesLe N, (1 / (p : ℂ)) * (delangeSvRestr p (N / p) v - delangeSv N v) := by
  rw [delangeE, delangeL_cast, Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- The ODE in the form the integrating factor consumes. -/
theorem hasDerivAt_delangeSv' (N : ℕ) (v : ℂ) :
    HasDerivAt (delangeSv N) ((delangeL N : ℂ) * delangeSv N v + delangeE N v) v := by
  have h := hasDerivAt_delangeSv N v
  rwa [show (delangeL N : ℂ) * delangeSv N v + delangeE N v
      = ∑ p ∈ primesLe N, (1 / (p : ℂ)) * delangeSvRestr p (N / p) v by rw [delangeE]; ring]

lemma continuous_delangeSv (N : ℕ) : Continuous (delangeSv N) := by
  classical
  refine continuous_finset_sum _ fun n _ => ?_
  by_cases hsq : Squarefree n
  · simp only [hsq, if_true]; fun_prop
  · simp only [hsq, if_false]; fun_prop

lemma continuous_delangeSvRestr (p M : ℕ) : Continuous (delangeSvRestr p M) := by
  classical
  refine continuous_finset_sum _ fun n _ => ?_
  by_cases hsq : Squarefree n
  · simp only [hsq, if_true]; fun_prop
  · simp only [hsq, if_false]; fun_prop

lemma continuous_delangeE (N : ℕ) : Continuous (delangeE N) := by
  refine Continuous.sub (continuous_finset_sum _ fun p _ => ?_) ?_
  · exact continuous_const.mul (continuous_delangeSvRestr _ _)
  · exact continuous_const.mul (continuous_delangeSv N)

/-- **The integrating factor identity, in the complex variable.**  With `c = L·ξ`, the function
`G(w) = e^{-cw}·S(N; wξ)` has derivative `e^{-cw}·ξ·E_N(wξ)`: the `L·S` main term is absorbed, and
what multiplies the initial condition is `e^{c}`, of modulus `e^{L·Re ξ}`. -/
theorem hasDerivAt_integratingFactorC (N : ℕ) (ξ w : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (-((delangeL N : ℂ) * ξ * w)) * delangeSv N (w * ξ))
      (Complex.exp (-((delangeL N : ℂ) * ξ * w)) * ξ * delangeE N (w * ξ)) w := by
  have hray := (hasDerivAt_id w).mul_const ξ
  have hF := (hasDerivAt_delangeSv' N (w * ξ)).comp w hray
  have hlin := ((hasDerivAt_id w).const_mul ((delangeL N : ℂ) * ξ)).neg
  have hexp := (Complex.hasDerivAt_exp (-((delangeL N : ℂ) * ξ * w))).comp w hlin
  have hprod := hexp.mul hF
  refine hprod.congr_deriv ?_
  simp only [Function.comp_apply, Pi.neg_apply, id_eq, one_mul, mul_one]
  ring

/-- The same, restricted to the real ray `r ↦ r·ξ`. -/
theorem hasDerivAt_integratingFactor (N : ℕ) (ξ : ℂ) (r : ℝ) :
    HasDerivAt
      (fun r : ℝ => Complex.exp (-((delangeL N : ℂ) * ξ * (r : ℂ))) * delangeSv N ((r : ℂ) * ξ))
      (Complex.exp (-((delangeL N : ℂ) * ξ * (r : ℂ))) * ξ * delangeE N ((r : ℂ) * ξ)) r :=
  (hasDerivAt_integratingFactorC N ξ (r : ℂ)).comp_ofReal

/-! ### The closed bound

FTC on the integrating factor, plus `‖e^{-c r}‖ = e^{a r}` with `a = L·|Re ξ|`, gives the
conditional estimate with its decisive `1/a` gain. -/

lemma delangeSv_zero {N : ℕ} (hN : 1 ≤ N) : delangeSv N 0 = 1 := by
  classical
  rw [delangeSv]
  refine (Finset.sum_eq_single 1 (fun n hn hne => ?_) (fun hn => ?_)).trans ?_
  · simp only [Finset.mem_Ioc] at hn
    by_cases hsq : Squarefree n
    · have h1 : n ≠ 1 := hne
      have : omegaNat n ≠ 0 := by
        simp only [omegaNat, ne_eq, Finset.card_eq_zero, Nat.primeFactors_eq_empty]
        push_neg
        exact ⟨by omega, h1⟩
      simp [hsq, zero_pow this]
    · simp [hsq]
  · exact absurd (Finset.mem_Ioc.mpr ⟨Nat.one_pos, hN⟩) hn
  · simp [omegaNat]

/-- `∫_0^1 B·e^{ar} dr = (B/a)(e^a − 1)`, by the explicit antiderivative. -/
lemma integral_const_mul_exp_mul {a B : ℝ} (ha : a ≠ 0) :
    (∫ r in (0:ℝ)..1, B * Real.exp (a * r)) = (B / a) * (Real.exp a - 1) := by
  have hderiv : ∀ r ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => (B / a) * Real.exp (a * r)) (B * Real.exp (a * r)) r := by
    intro r _
    have h1 : HasDerivAt (fun r : ℝ => a * r) a r := by
      simpa using (hasDerivAt_id r).const_mul a
    have h2 : HasDerivAt (fun r : ℝ => Real.exp (a * r)) (Real.exp (a * r) * a) r :=
      (Real.hasDerivAt_exp (a * r)).comp r h1
    have := h2.const_mul (B / a)
    refine this.congr_deriv ?_
    field_simp
  have hint : IntervalIntegrable (fun r : ℝ => B * Real.exp (a * r)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [mul_one, mul_zero, Real.exp_zero]
  ring

/-- **THE CONDITIONAL BOUND.**  If the scale-comparison error `E_N` is bounded by `B` along the
ray `[0,1]·ξ`, with `‖ξ‖ = 1` and `Re ξ < 0`, then

    ‖S(N; ξ)‖ ≤ e^{L·Re ξ} + B / (L·|Re ξ|).

The first term is `≍ (log N)^{Re ξ} → 0`; the second carries the gain `1/L = O(1/log log N)`, so
`B = O(1)` — a *boundedness* statement — already forces `S(N; ξ) → 0`. -/
theorem norm_delangeSv_le {N : ℕ} (hN : 1 ≤ N) {ξ : ℂ} (hξ : ‖ξ‖ = 1) (hre : ξ.re < 0)
    (hL : 0 < delangeL N) {B : ℝ} (hBnn : 0 ≤ B)
    (hB : ∀ r ∈ Set.Icc (0:ℝ) 1, ‖delangeE N ((r : ℂ) * ξ)‖ ≤ B) :
    ‖delangeSv N ξ‖ ≤ Real.exp (delangeL N * ξ.re) + B / (delangeL N * (-ξ.re)) := by
  classical
  set L : ℝ := delangeL N with hLdef
  set a : ℝ := L * (-ξ.re) with hadef
  have hapos : 0 < a := by rw [hadef]; nlinarith [hL, hre]
  set H : ℝ → ℂ := fun r => Complex.exp (-((L : ℂ) * ξ * (r : ℂ))) * delangeSv N ((r : ℂ) * ξ)
    with hHdef
  set H' : ℝ → ℂ := fun r =>
    Complex.exp (-((L : ℂ) * ξ * (r : ℂ))) * ξ * delangeE N ((r : ℂ) * ξ) with hH'def
  have hderiv : ∀ r ∈ Set.uIcc (0:ℝ) 1, HasDerivAt H (H' r) r :=
    fun r _ => hasDerivAt_integratingFactor N ξ r
  -- `‖e^{-c r}‖ = e^{a r}`
  have hnormexp : ∀ r : ℝ, ‖Complex.exp (-((L : ℂ) * ξ * (r : ℂ)))‖ = Real.exp (a * r) := by
    intro r
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, hadef]
    ring
  have hcontE : Continuous fun r : ℝ => delangeE N ((r : ℂ) * ξ) :=
    (continuous_delangeE N).comp (by fun_prop)
  have hcontH' : Continuous H' := by
    rw [hH'def]
    exact ((Complex.continuous_exp.comp (by fun_prop)).mul continuous_const).mul hcontE
  have hint : IntervalIntegrable H' MeasureTheory.volume 0 1 := hcontH'.intervalIntegrable 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- bound the integral
  have hptw : ∀ r ∈ Set.Icc (0:ℝ) 1, ‖H' r‖ ≤ B * Real.exp (a * r) := by
    intro r hr
    rw [hH'def]
    simp only
    rw [norm_mul, norm_mul, hnormexp r, hξ, mul_one]
    have := hB r hr
    have hpos : (0:ℝ) < Real.exp (a * r) := Real.exp_pos _
    nlinarith [this, hpos]
  have hintnorm : IntervalIntegrable (fun r => ‖H' r‖) MeasureTheory.volume 0 1 :=
    (hcontH'.norm).intervalIntegrable 0 1
  have hintb : IntervalIntegrable (fun r : ℝ => B * Real.exp (a * r)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hle1 : ‖∫ r in (0:ℝ)..1, H' r‖ ≤ ∫ r in (0:ℝ)..1, ‖H' r‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by norm_num)
  have hle2 : (∫ r in (0:ℝ)..1, ‖H' r‖) ≤ ∫ r in (0:ℝ)..1, B * Real.exp (a * r) :=
    intervalIntegral.integral_mono_on (by norm_num) hintnorm hintb hptw
  rw [integral_const_mul_exp_mul (ne_of_gt hapos)] at hle2
  -- `H 1 = H 0 + ∫`, and `H 0 = 1`
  have hH0 : H 0 = 1 := by
    rw [hHdef]
    simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul, zero_mul]
    exact delangeSv_zero hN
  have hH1 : ‖H 1‖ ≤ 1 + (B / a) * (Real.exp a - 1) := by
    have : H 1 = H 0 + ∫ r in (0:ℝ)..1, H' r := by rw [hftc]; ring
    rw [this, hH0]
    refine le_trans (norm_add_le _ _) ?_
    simp only [norm_one]
    linarith [hle1, hle2]
  -- transfer back
  have hSeq : delangeSv N ξ = Complex.exp ((L : ℂ) * ξ) * H 1 := by
    rw [hHdef]
    simp only [Complex.ofReal_one, mul_one]
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  have hnormS : ‖delangeSv N ξ‖ = Real.exp (-a) * ‖H 1‖ := by
    rw [hSeq, norm_mul, Complex.norm_exp]
    congr 2
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hadef]
    ring
  have hexpa : Real.exp (-a) = Real.exp (L * ξ.re) := by
    congr 1; rw [hadef]; ring
  have hkey : Real.exp (-a) * (1 + (B / a) * (Real.exp a - 1))
      = Real.exp (-a) + (B / a) * (1 - Real.exp (-a)) := by
    have : Real.exp (-a) * Real.exp a = 1 := by
      rw [← Real.exp_add]; simp
    field_simp
    nlinarith [this]
  have hfin : Real.exp (-a) * ‖H 1‖ ≤ Real.exp (-a) + B / a := by
    have h1 : Real.exp (-a) * ‖H 1‖ ≤ Real.exp (-a) * (1 + (B / a) * (Real.exp a - 1)) :=
      mul_le_mul_of_nonneg_left hH1 (Real.exp_pos _).le
    rw [hkey] at h1
    have h2 : (B / a) * (1 - Real.exp (-a)) ≤ B / a := by
      have hBa : 0 ≤ B / a := by positivity
      nlinarith [Real.exp_pos (-a), hBa]
    linarith
  rw [hnormS, ← hexpa]
  exact hfin

end NormalNumbers.CastingOut
