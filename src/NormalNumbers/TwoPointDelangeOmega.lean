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
theorem norm_delangeSv_le {N : ℕ} (hN : 1 ≤ N) {ξ : ℂ} (hre : ξ.re < 0)
    (hL : 0 < delangeL N) {B : ℝ} (hBnn : 0 ≤ B)
    (hB : ∀ r ∈ Set.Icc (0:ℝ) 1, ‖delangeE N ((r : ℂ) * ξ)‖ ≤ B) :
    ‖delangeSv N ξ‖ ≤ Real.exp (delangeL N * ξ.re) + B * ‖ξ‖ / (delangeL N * (-ξ.re)) := by
  classical
  have hξ : ‖ξ‖ = ‖ξ‖ := rfl
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
  have hptw : ∀ r ∈ Set.Icc (0:ℝ) 1, ‖H' r‖ ≤ (B * ‖ξ‖) * Real.exp (a * r) := by
    intro r hr
    rw [hH'def]
    simp only
    rw [norm_mul, norm_mul, hnormexp r]
    have hE := hB r hr
    calc Real.exp (a * r) * ‖ξ‖ * ‖delangeE N ((r : ℂ) * ξ)‖
        ≤ Real.exp (a * r) * ‖ξ‖ * B :=
          mul_le_mul_of_nonneg_left hE (by positivity)
      _ = (B * ‖ξ‖) * Real.exp (a * r) := by ring
  have hintnorm : IntervalIntegrable (fun r => ‖H' r‖) MeasureTheory.volume 0 1 :=
    (hcontH'.norm).intervalIntegrable 0 1
  have hintb : IntervalIntegrable (fun r : ℝ => (B * ‖ξ‖) * Real.exp (a * r))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have hle1 : ‖∫ r in (0:ℝ)..1, H' r‖ ≤ ∫ r in (0:ℝ)..1, ‖H' r‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by norm_num)
  have hle2 : (∫ r in (0:ℝ)..1, ‖H' r‖) ≤ ∫ r in (0:ℝ)..1, (B * ‖ξ‖) * Real.exp (a * r) :=
    intervalIntegral.integral_mono_on (by norm_num) hintnorm hintb hptw
  rw [integral_const_mul_exp_mul (ne_of_gt hapos)] at hle2
  -- `H 1 = H 0 + ∫`, and `H 0 = 1`
  have hH0 : H 0 = 1 := by
    rw [hHdef]
    simp only [Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul, zero_mul]
    exact delangeSv_zero hN
  have hH1 : ‖H 1‖ ≤ 1 + ((B * ‖ξ‖) / a) * (Real.exp a - 1) := by
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
  have hkey : Real.exp (-a) * (1 + ((B * ‖ξ‖) / a) * (Real.exp a - 1))
      = Real.exp (-a) + ((B * ‖ξ‖) / a) * (1 - Real.exp (-a)) := by
    have h : Real.exp (-a) * Real.exp a = 1 := by
      rw [← Real.exp_add]; simp
    linear_combination ((B * ‖ξ‖) / a) * h
  have hfin : Real.exp (-a) * ‖H 1‖ ≤ Real.exp (-a) + (B * ‖ξ‖) / a := by
    have h1 : Real.exp (-a) * ‖H 1‖
        ≤ Real.exp (-a) * (1 + ((B * ‖ξ‖) / a) * (Real.exp a - 1)) :=
      mul_le_mul_of_nonneg_left hH1 (Real.exp_pos _).le
    rw [hkey] at h1
    have h2 : ((B * ‖ξ‖) / a) * (1 - Real.exp (-a)) ≤ (B * ‖ξ‖) / a := by
      have hBa : 0 ≤ (B * ‖ξ‖) / a := by positivity
      nlinarith [Real.exp_pos (-a), hBa]
    linarith
  rw [hnormS, ← hexpa]
  exact hfin

/-! ### Splitting the error at a cutoff

`E_N` is a `Σ_p 1/p` average, so *all* of its mass sits on small primes in the `log log` sense —
but the primes `p > K` can be discarded outright: their total weight is
`(log N + O(1) − log K)/log K`, which is `O(1)` already at `K = √N` and `o(1)` for
`K = N^{1/log log N}`.  Since each term there is trivially `≤ 2·sup‖S‖`, the large-prime half of
`E_N` is `O(sup‖S‖)` with an *absolute* constant, and `norm_delangeSv_le`'s gain `1/L` then makes
it a genuine contraction.  The whole difficulty is therefore concentrated in the small primes,
where `S^{(p)}(N/p;v)` and `S(N;v)` live at comparable scales. -/

/-- **A `Σ 1/p` Mertens corollary.**  `Σ_{K < p ≤ N} 1/p ≤ (log N + log 4 + 9 − log K)/log K`.
Immediate from the two-sided bracket of `TwoPointMertensLower.lean` by `1/p ≤ (log p/p)/log K`.
At `K = √N` the right-hand side is `≤ 1 + O(1/log N)`. -/
theorem sum_inv_prime_sdiff_le {K N : ℕ} (hK : 2 ≤ K) (hKN : K ≤ N) :
    ∑ p ∈ primesLe N \ primesLe K, 1 / (p : ℝ)
      ≤ (Real.log N + Real.log 4 + 9 - Real.log K) / Real.log K := by
  classical
  have hK1 : 1 ≤ K := by omega
  have hN1 : 1 ≤ N := by omega
  have hKR : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hlogK : 0 < Real.log K := Real.log_pos (by linarith)
  have hsub : primesLe K ⊆ primesLe N := by
    intro p hp
    rw [primesLe, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hstep : ∀ p ∈ primesLe N \ primesLe K,
      1 / (p : ℝ) ≤ (Real.log p / (p : ℝ)) / Real.log K := by
    intro p hp
    rw [Finset.mem_sdiff] at hp
    have hpp := prime_of_mem_primesLe hp.1
    have hpK : K < p := by
      by_contra hcon
      push_neg at hcon
      exact hp.2 (by rw [primesLe, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hpp⟩)
    have hpR : (K : ℝ) < (p : ℝ) := by exact_mod_cast hpK
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hlogp : Real.log K ≤ Real.log p := Real.log_le_log (by linarith) hpR.le
    rw [div_div, div_le_div_iff₀ hppos (by positivity)]
    nlinarith [hlogp, hlogK, hppos]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.sum_div]
  have hnn : ∀ p ∈ primesLe N, (0 : ℝ) ≤ Real.log p / (p : ℝ) := by
    intro p hp
    have hpp := prime_of_mem_primesLe hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have : (0 : ℝ) ≤ Real.log p := Real.log_nonneg (by linarith)
    positivity
  have hsd : ∑ p ∈ primesLe N \ primesLe K, Real.log p / (p : ℝ)
      + ∑ p ∈ primesLe K, Real.log p / (p : ℝ)
      = ∑ p ∈ primesLe N, Real.log p / (p : ℝ) := Finset.sum_sdiff hsub
  have hup := mertens_upper N hN1
  have hlo := mertens_lower K hK1
  refine div_le_div_of_nonneg_right ?_ hlogK.le
  linarith [hsd, hup, hlo]

/-- **The split of `E_N` at a cutoff `K`.**  The large primes contribute only through their
total weight `Σ_{K<p≤N} 1/p` (bounded by `sum_inv_prime_sdiff_le`), each term costing `2Φ`. -/
theorem norm_delangeE_le_split {N K : ℕ} (hKN : K ≤ N) (v : ℂ) {Φ : ℝ}
    (hS : ∀ M, ‖delangeSv M v‖ ≤ Φ) (hR : ∀ p M, ‖delangeSvRestr p M v‖ ≤ Φ) :
    ‖delangeE N v‖
      ≤ (∑ p ∈ primesLe K, (1 / (p : ℝ)) * ‖delangeSvRestr p (N / p) v - delangeSv N v‖)
        + (∑ p ∈ primesLe N \ primesLe K, 1 / (p : ℝ)) * (2 * Φ) := by
  classical
  have hΦnn : 0 ≤ Φ := le_trans (norm_nonneg _) (hS 0)
  have hsub : primesLe K ⊆ primesLe N := by
    intro p hp
    rw [primesLe, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hterm : ∀ p ∈ primesLe N,
      ‖(1 / (p : ℂ)) * (delangeSvRestr p (N / p) v - delangeSv N v)‖
        = (1 / (p : ℝ)) * ‖delangeSvRestr p (N / p) v - delangeSv N v‖ := by
    intro p hp
    have hpp := prime_of_mem_primesLe hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  rw [delangeE_eq_sum]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_sdiff hsub]
  have hbig : ∑ p ∈ primesLe N \ primesLe K,
      (1 / (p : ℝ)) * ‖delangeSvRestr p (N / p) v - delangeSv N v‖
      ≤ (∑ p ∈ primesLe N \ primesLe K, 1 / (p : ℝ)) * (2 * Φ) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp := prime_of_mem_primesLe (Finset.mem_sdiff.mp hp).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hinv : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have hd : ‖delangeSvRestr p (N / p) v - delangeSv N v‖ ≤ 2 * Φ := by
      refine le_trans (norm_sub_le _ _) ?_
      linarith [hR p (N / p), hS N]
    exact mul_le_mul_of_nonneg_left hd hinv
  linarith [hbig]

/-! ### The reduction, end to end

`L = Σ_{p≤N} 1/p → ∞` (Mertens' second theorem, via mathlib's divergence of the prime
reciprocals), so both terms of `norm_delangeSv_le` vanish and the whole of `DelangeKernelMean`
reduces to the single boundedness hypothesis on `delangeE`. -/

/-- `Σ_{p ≤ N} 1/p → ∞`. -/
theorem tendsto_delangeL_atTop : Tendsto delangeL atTop atTop := by
  classical
  have hf : ∀ n : ℕ, 0 ≤ Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) n := by
    intro n
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split <;> positivity
  have hg := (not_summable_iff_tendsto_nat_atTop_of_nonneg hf).mp not_summable_one_div_on_primes
  have hcomp := hg.comp (Filter.tendsto_add_atTop_nat 1)
  refine hcomp.congr fun N => ?_
  simp only [Function.comp_apply, Set.indicator_apply, Set.mem_setOf_eq]
  rw [← Finset.sum_filter, delangeL, primesLe]

/-- **THE REDUCTION.**  If the scale-comparison error is bounded along the ray `[0,1]·v`,
uniformly in `N`, then `S(N; v) → 0` for every `v` with `Re v < 0`. -/
theorem tendsto_delangeSv_of_errorBounded {v : ℂ} (hre : v.re < 0) {B : ℝ} (hBnn : 0 ≤ B)
    (hB : ∀ N : ℕ, ∀ r ∈ Set.Icc (0:ℝ) 1, ‖delangeE N ((r : ℂ) * v)‖ ≤ B) :
    Tendsto (fun N => delangeSv N v) atTop (𝓝 0) := by
  have hLtt := tendsto_delangeL_atTop
  -- the two pieces of the bound tend to `0`
  have h1 : Tendsto (fun N : ℕ => Real.exp (delangeL N * v.re)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact hLtt.atTop_mul_const_of_neg' hre
  have h2 : Tendsto (fun N : ℕ => B * ‖v‖ / (delangeL N * (-v.re))) atTop (𝓝 0) := by
    refine Filter.Tendsto.const_div_atTop ?_ _
    exact hLtt.atTop_mul_const (by linarith : (0:ℝ) < -v.re)
  have hsum : Tendsto (fun N : ℕ =>
      Real.exp (delangeL N * v.re) + B * ‖v‖ / (delangeL N * (-v.re))) atTop (𝓝 0) := by
    simpa using h1.add h2
  refine squeeze_zero_norm' ?_ hsum
  filter_upwards [hLtt.eventually_gt_atTop 0, Filter.eventually_ge_atTop 1] with N hLpos hN
  exact norm_delangeSv_le hN hre hLpos hBnn (fun r hr => hB N r hr)

/-- **`DelangeKernelMean` from the boundedness of `delangeE`.**  For `Re z < 1` this is now the
*only* remaining obligation of the whole Delange axiom. -/
theorem delangeKernelMean_of_errorBounded {z : ℂ} (hre : z.re < 1) {B : ℝ} (hBnn : 0 ≤ B)
    (hB : ∀ N : ℕ, ∀ r ∈ Set.Icc (0:ℝ) 1, ‖delangeE N ((r : ℂ) * (z - 1))‖ ≤ B) :
    DelangeKernelMean z := by
  rw [delangeKernelMean_iff]
  have hre' : (z - 1).re < 0 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have := tendsto_delangeSv_of_errorBounded hre' hBnn hB
  refine this.congr fun N => ?_
  exact delangeSv_eq z N

/-! ### Removing the coprimality restriction from the open core

`delangeSrestr_rec` says `S^{(p)}(M) = S(M) − (v/p)·S^{(p)}(M/p)` exactly, so replacing
`S^{(p)}(N/p)` by `S(N/p)` inside `delangeE` costs `Σ_p ‖v‖/p²·sup‖S^{(p)}‖ ≤ ‖v‖·Φ`: an absolute
constant, since `Σ_p 1/p² ≤ 1`.  What is left is a **pure Toeplitz error**

    Σ_{p ≤ N} (1/p)·( S(N/p; v) − S(N; v) ),

a statement about `delangeSv` at dilated scales only — no restricted sums anywhere. -/

/-- `Σ_{2 ≤ n ≤ N} 1/(n(n−1)) = 1 − 1/N`. -/
lemma sum_inv_mul_pred (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) * ((n : ℝ) - 1)) = 1 - 1 / (N : ℝ) := by
  induction N with
  | zero => omega
  | succ N ih =>
      rcases Nat.eq_zero_or_pos N with hN0 | hN0
      · subst hN0
        norm_num
      rw [Finset.sum_Icc_succ_top (by omega), ih hN0]
      have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN0
      have h1 : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [h1, show ((N : ℝ) + 1) - 1 = (N : ℝ) from by ring]
      have hNne : (N : ℝ) ≠ 0 := by linarith
      have hN1ne : (N : ℝ) + 1 ≠ 0 := by linarith
      field_simp
      ring

/-- `Σ_{p ≤ N} 1/p² ≤ 1`. -/
theorem sum_inv_sq_prime_le (N : ℕ) : ∑ p ∈ primesLe N, 1 / ((p : ℝ) ^ 2) ≤ 1 := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [primesLe]
    norm_num [Finset.filter_singleton, Nat.not_prime_zero]
  have hsub : primesLe N ⊆ Finset.Icc 2 N := by
    intro p hp
    have hpp := prime_of_mem_primesLe hp
    rw [primesLe, Finset.mem_filter, Finset.mem_range] at hp
    simp only [Finset.mem_Icc]
    exact ⟨hpp.two_le, by omega⟩
  have hstep : ∀ n ∈ Finset.Icc 2 N,
      1 / ((n : ℝ) ^ 2) ≤ 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
    nlinarith
  have h1 : ∑ p ∈ primesLe N, 1 / ((p : ℝ) ^ 2) ≤ ∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) ^ 2) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => ?_
    simp only [Finset.mem_Icc] at hn
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    positivity
  have h2 := Finset.sum_le_sum hstep
  rw [sum_inv_mul_pred N hN] at h2
  have h3 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  linarith

/-- The restriction recursion, in the parametrised variable. -/
lemma delangeSvRestr_rec (v : ℂ) {p : ℕ} (hp : p.Prime) (M : ℕ) :
    delangeSvRestr p M v = delangeSv M v - (v / (p : ℂ)) * delangeSvRestr p (M / p) v := by
  have h := delangeSrestr_rec (1 + v) hp M
  rw [← delangeSv_eq (1 + v) M, ← delangeSvRestr_eq (1 + v) p M,
    ← delangeSvRestr_eq (1 + v) p (M / p)] at h
  simp only [add_sub_cancel_left] at h
  exact h

/-- **The open core is a pure Toeplitz error.**  Removing the coprimality restriction costs at
most `‖v‖·Φ`, an absolute constant. -/
theorem norm_delangeE_sub_toeplitz_le (N : ℕ) (v : ℂ) {Φ : ℝ}
    (hR : ∀ p M, ‖delangeSvRestr p M v‖ ≤ Φ) :
    ‖delangeE N v - ∑ p ∈ primesLe N, (1 / (p : ℂ)) * (delangeSv (N / p) v - delangeSv N v)‖
      ≤ ‖v‖ * Φ := by
  classical
  have hΦnn : 0 ≤ Φ := le_trans (norm_nonneg _) (hR 2 0)
  rw [delangeE_eq_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ p ∈ primesLe N,
      ‖(1 / (p : ℂ)) * (delangeSvRestr p (N / p) v - delangeSv N v)
        - (1 / (p : ℂ)) * (delangeSv (N / p) v - delangeSv N v)‖
        ≤ (‖v‖ * Φ) * (1 / ((p : ℝ) ^ 2)) := by
    intro p hp
    have hpp := prime_of_mem_primesLe hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hrec := delangeSvRestr_rec v hpp (N / p)
    rw [← mul_sub, hrec]
    have hcollapse : delangeSv (N / p) v - (v / (p : ℂ)) * delangeSvRestr p (N / p / p) v
        - delangeSv N v - (delangeSv (N / p) v - delangeSv N v)
        = -((v / (p : ℂ)) * delangeSvRestr p (N / p / p) v) := by ring
    rw [hcollapse, norm_mul, norm_neg, norm_mul, norm_div, norm_div, norm_one,
      Complex.norm_natCast]
    have hb := hR p (N / p / p)
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    calc 1 / (p : ℝ) * (‖v‖ / (p : ℝ) * ‖delangeSvRestr p (N / p / p) v‖)
        ≤ 1 / (p : ℝ) * (‖v‖ / (p : ℝ) * Φ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hb (by positivity)
      _ = (‖v‖ * Φ) * (1 / ((p : ℝ) ^ 2)) := by field_simp; try ring
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  calc ‖v‖ * Φ * ∑ p ∈ primesLe N, 1 / ((p : ℝ) ^ 2)
      ≤ ‖v‖ * Φ * 1 :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_prime_le N) (mul_nonneg (norm_nonneg v) hΦnn)
    _ = ‖v‖ * Φ := by ring

/-! ### Swapping the Toeplitz error: an explicit, SMALL weight

`S(N/p;v) − S(N;v) = −Σ_{N/p < n ≤ N}` of the kernel, so exchanging the two sums turns the open
core into a single sum over `n` against the weight

    w_N(n) = Σ_{p ≤ N, N/p < n} 1/p ,

which `sum_inv_prime_sdiff_le` bounds by `(log n + log 4 + 9)/(log N − log n)`.  So the weight is
`O(log n/log(N/n))`: **tiny in the bulk** (`≈ 0.11` at `n = N^{0.1}`) and only reaching the full
`log log N` for `n` within a bounded power of `N`.  The obligation is therefore a *short-interval*
statement about the kernel near `n ≈ N`, not a global one. -/

/-- The swapped weight `w_N(n) = Σ_{p ≤ N,  N/p < n} 1/p`. -/
noncomputable def delangeW (N n : ℕ) : ℝ :=
  ∑ p ∈ (primesLe N).filter (fun p => N / p < n), 1 / (p : ℝ)

/-- **The swap.**  The Toeplitz error is a single kernel sum against `w_N`. -/
theorem delangeToeplitz_swap (N : ℕ) (v : ℂ) :
    ∑ p ∈ primesLe N, (1 / (p : ℂ)) * (delangeSv (N / p) v - delangeSv N v)
      = - ∑ n ∈ Finset.Ioc 0 N,
          ((if Squarefree n then v ^ omegaNat n else 0) / (n : ℂ)) * (delangeW N n : ℂ) := by
  classical
  have hdiff : ∀ p ∈ primesLe N,
      delangeSv (N / p) v - delangeSv N v
        = - ∑ n ∈ Finset.Ioc 0 N,
            (if N / p < n then (if Squarefree n then v ^ omegaNat n else 0) / (n : ℂ) else 0) := by
    intro p _
    have hple : N / p ≤ N := Nat.div_le_self _ _
    have hsplit : (Finset.Ioc 0 N).filter (fun n => N / p < n) = Finset.Ioc (N / p) N := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨lt_of_le_of_lt (Nat.zero_le (N / p)) h1, h2⟩, h1⟩
    rw [← Finset.sum_filter, hsplit]
    have hcons := Finset.sum_Ioc_consecutive
      (fun n => (if Squarefree n then v ^ omegaNat n else 0) / (n : ℂ))
      (Nat.zero_le (N / p)) hple
    rw [delangeSv, delangeSv, ← hcons]
    ring
  rw [Finset.sum_congr rfl (fun p hp => by rw [hdiff p hp])]
  have hin : ∀ p : ℕ, (1 / (p : ℂ)) *
      (- ∑ n ∈ Finset.Ioc 0 N,
        (if N / p < n then (if Squarefree n then v ^ omegaNat n else 0) / (n : ℂ) else 0))
      = - ∑ n ∈ Finset.Ioc 0 N,
        (if N / p < n then (1 / (p : ℂ)) * ((if Squarefree n then v ^ omegaNat n else 0) / (n : ℂ))
          else 0) := by
    intro p
    rw [mul_neg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by split <;> simp
  rw [Finset.sum_congr rfl (fun p _ => hin p), Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [delangeW, Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  push_cast
  ring

/-- **The weight is small away from `n ≈ N`.**  `w_N(n) ≤ (log N + log 4 + 9 − log(N/n))/log(N/n)`,
so for `n ≤ N^{δ}` it is `≤ δ/(1−δ) + O(1/log N)`. -/
theorem delangeW_le {N n : ℕ} (hK : 2 ≤ N / n) :
    delangeW N n
      ≤ (Real.log N + Real.log 4 + 9 - Real.log (N / n : ℕ)) / Real.log (N / n : ℕ) := by
  classical
  set K : ℕ := N / n with hKdef
  have hKN : K ≤ N := Nat.div_le_self _ _
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hKdef; simp at hKdef; omega
    · exact h
  have hnK : n * K ≤ N := by
    rw [hKdef, Nat.mul_comm]; exact Nat.div_mul_le_self N n
  have hsub : (primesLe N).filter (fun p => N / p < n) ⊆ primesLe N \ primesLe K := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpN, hlt⟩ := hp
    have hpp := prime_of_mem_primesLe hpN
    refine Finset.mem_sdiff.mpr ⟨hpN, ?_⟩
    intro hmem
    rw [primesLe, Finset.mem_filter, Finset.mem_range] at hmem
    have hpK : p ≤ K := by omega
    have hnp : n * p ≤ N := le_trans (Nat.mul_le_mul_left _ hpK) hnK
    have hge : n ≤ N / p := (Nat.le_div_iff_mul_le hpp.pos).mpr hnp
    exact absurd hlt (not_lt.mpr hge)
  have hnn : ∀ p ∈ primesLe N \ primesLe K, (0 : ℝ) ≤ 1 / (p : ℝ) := by
    intro p hp
    have hpp := prime_of_mem_primesLe (Finset.mem_sdiff.mp hp).1
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    positivity
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hnn p hp) ?_
  exact sum_inv_prime_sdiff_le hK hKN

end NormalNumbers.CastingOut

namespace NormalNumbers.CastingOut

open Finset Filter Topology

/-! ## A SECOND ROUTE: the scale equation

The `v`-direction route above is stuck on one cancellation statement.  The *scale* direction is
better, and the reason is arithmetic: the multiplier there is `1 + v = z`, which lies on the unit
circle, while the trivial majorant `A(N) = Σ_{n≤N} μ²(n)u^{ω(n)}/n ≍ (log N)^u` is `o(log N)`
exactly in the repo's regime `u = ‖z−1‖ < 1`.  Concretely, the two identities already in the tree,

  * `delangeS_mul_log` :  `S(N)·log N = T(N) + Abel(N)`,
  * `sum_delangeKernel_mul_log` (Levin–Fainleib) + `norm_delangeT_sub_primeSum_le` :
    `T(N) = (z−1)·Σ_{p≤N}(log p/p)·S(N/p) + O(A(N))`,

combine, once both sides are written as hyperbola sums over `n`, into

    S(N)·log N  =  z · Abel(N)  +  R(N),        ‖R(N)‖ = O(A(N)) = O((log N)^u),

because BOTH `Abel(N)` and `Σ_p (log p/p)S(N/p)` equal `Σ_{n≤N} (h(n)/n)·log(N/n)` up to `O(A(N))`
— the first exactly, the second by Mertens (`mertens_lower`/`mertens_upper`, error `≤ 9`).

With `σ = log N` and `Y = Abel`, that is the linear scale ODE `σ·Y' = z·Y + R`.  Its integrating
factor is `σ^{-z}`, of modulus `σ^{-Re z} = σ^{-(1+Re(z−1))}`, so

    ‖Y(σ)‖ ≲ σ^{Re z}·(C + ∫ ‖R‖τ^{-1-Re z} dτ) ≲ σ^{Re z} + σ^{u},
    ‖S(N)‖ = ‖z·Y + R‖/σ ≲ σ^{Re z − 1} + σ^{u−1}  →  0

for `Re z < 1` and `u < 1`.  **Both exponents are negative exactly in the repo's regime**, and
— unlike every previous attempt — no bootstrap and no a priori bound on `‖S‖` is needed: the
trivial `‖S‖ ≤ A` suffices throughout, because the sign is carried by the integrating factor
`σ^{-z}` and never by a norm.  (Lap 35's refutation does not apply: it normed the multiplier of
the `v`-direction equation, whose modulus is `u`; here the multiplier is `z`, of modulus one, and
it is never normed.)

This section builds that route.  Brick 1: both sides are hyperbola sums.
-/

/-- The Abel weights telescope on any initial segment. -/
theorem sum_log_telescope_Ico {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ∑ m ∈ Finset.Ico n N, (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))
      = Real.log N - Real.log n := by
  have h1 := sum_log_telescope n
  have h2 := sum_log_telescope N
  have hcons := Finset.sum_Ico_consecutive
    (fun m : ℕ => Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) hn hnN
  linarith [hcons, h1, h2]

/-- **Brick 1: `Abel` is a hyperbola sum.**  `Abel(N) = Σ_{n ≤ N} (h(n)/n)·log(N/n)`, exactly. -/
theorem delangeAbel_eq_hyperbola (z : ℂ) (N : ℕ) :
    delangeAbel z N
      = ∑ n ∈ Finset.Ioc 0 N,
          (delangeKernel z n / (n : ℂ)) * ((Real.log N - Real.log n : ℝ) : ℂ) := by
  classical
  rw [delangeAbel]
  have hstep : ∀ m ∈ Finset.Ico 1 N,
      ((Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) : ℝ) : ℂ) * delangeS z m
        = ∑ n ∈ Finset.Ioc 0 N,
            (if n ≤ m then ((Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) : ℝ) : ℂ)
              * (delangeKernel z n / (n : ℂ)) else 0) := by
    intro m hm
    simp only [Finset.mem_Ico] at hm
    rw [← Finset.sum_filter, delangeS, Finset.mul_sum]
    refine Finset.sum_congr ?_ fun n _ => rfl
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [Finset.mem_Ioc] at hn
  rw [← Finset.sum_filter]
  have hset : (Finset.Ico 1 N).filter (fun m => n ≤ m) = Finset.Ico n N := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [hset, ← Finset.sum_mul, ← Complex.ofReal_sum, sum_log_telescope_Ico hn.1 hn.2]
  ring

/-- **Brick 2: the prime sum is a hyperbola sum too**, with the Mertens function as weight. -/
theorem sum_primeWeight_delangeS_eq (z : ℂ) (N : ℕ) :
    ∑ p ∈ primesLe N, ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p)
      = ∑ n ∈ Finset.Ioc 0 N, (delangeKernel z n / (n : ℂ))
          * ((∑ q ∈ primesLe (N / n), Real.log q / (q : ℝ) : ℝ) : ℂ) := by
  classical
  have hstep : ∀ p ∈ primesLe N,
      ((Real.log p : ℂ) / (p : ℂ)) * delangeS z (N / p)
        = ∑ n ∈ Finset.Ioc 0 N,
            (if n ≤ N / p then ((Real.log p : ℂ) / (p : ℂ)) * (delangeKernel z n / (n : ℂ))
              else 0) := by
    intro p hp
    have hple : N / p ≤ N := Nat.div_le_self _ _
    rw [← Finset.sum_filter, delangeS, Finset.mul_sum]
    refine Finset.sum_congr ?_ fun n _ => rfl
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [Finset.mem_Ioc] at hn
  rw [← Finset.sum_filter]
  have hset : (primesLe N).filter (fun p => n ≤ N / p) = primesLe (N / n) := by
    ext p
    simp only [Finset.mem_filter, primesLe, Finset.mem_range]
    constructor
    · rintro ⟨⟨-, hpp⟩, hle⟩
      have h1 : n * p ≤ N := (Nat.le_div_iff_mul_le hpp.pos).mp hle
      have h2 : p ≤ N / n := (Nat.le_div_iff_mul_le hn.1).mpr (by rw [Nat.mul_comm]; exact h1)
      exact ⟨by omega, hpp⟩
    · rintro ⟨hlt, hpp⟩
      have hpd : p ≤ N / n := by omega
      have h1 : p * n ≤ N := (Nat.le_div_iff_mul_le hn.1).mp hpd
      have hpN : p ≤ N := le_trans (Nat.le_mul_of_pos_right p hn.1) h1
      exact ⟨⟨by omega, hpp⟩,
        (Nat.le_div_iff_mul_le hpp.pos).mpr (by rw [Nat.mul_comm]; exact h1)⟩
  rw [hset, Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  push_cast
  ring

end NormalNumbers.CastingOut
