/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtNonPretentious
import NormalNumbers.C3MrtTwoShift
import ErdosProblems.Erdos67b.PrimeEstimates

/-!
# The archimedean half of the non-pretentiousness certificate for `ζ^Ω`

`C3MrtNonPretentious` supplies Elliott's hypothesis

    (A : ℝ) ≤ pretentiousDistSqToTwist (ζ^Ω) χ t X

only at `t = 0`.  This file develops the general `t`, starting from the exact identity that
makes the whole obligation classical.

## The bridge

`ζ^Ω` is **constant** on the primes (`Ω(p) = 1`), so with `mass X = ∑_{p ≤ X} 1/p` and
`S = ∑_{p ≤ X} conj(χ(p)p^{it})/p`,

    pretentiousDistSqToTwist (ζ^Ω) χ t X  =  mass X − Re (z · S)  ≥  mass X − ‖S‖ .

The `z` has disappeared from the bound: **every** remaining analytic obligation is a bound on
the classical twisted prime sum `S`, i.e. on `log L(1 + 1/log X + it, χ)`.  Note also what the
identity says about the cost budget: Elliott only asks for `A ≤ dist` with `A` a **constant**,
so only a constant saving over the trivial `‖S‖ ≤ mass X` is needed.

## The split this sets up

* **Range 2, `|t| ≥ T/log X`** (`T` chosen from `A`): a constant saving `‖S‖ ≤ mass X − A`.
  That is `log|L(1 + 1/log X + it, χ)| ≤ log log X − A`, the Vinogradov–Korobov
  log-derivative bound — the same input the dependency isolates as
  `Erdos67b.PolynomialHeightPrimeCorrelationBound`.  Named here, not proved.
* **Range 1, `|t| ≤ T/log X`**: elementary, and the subject of the rest of this file.  Since
  `|t| log p ≤ T` for every `p ≤ X`, the resonance condition `‖z·p^{−it} − 1‖ < δ` puts
  `|t| log p` into one of only `O(T)` windows `(γ_m − ε, γ_m + ε)` with `γ_m = |arg z − 2πm|`,
  and choosing `ε ≤ |arg z|/2` forces `γ_m ≥ 2ε`, hence a window ratio
  `(γ_m + ε)/(γ_m − ε) ≤ 3` **independently of `t`**.  Each window therefore holds primes in a
  range `(U, U³]`, of bounded reciprocal mass by the dependency's two-sided Mertens theorem.
  The resonance mass is an `X`-independent constant while the class-`1 (mod q)` primes carry
  `(1/φ(q)) log log X → ∞`.

`z ≠ 1` enters exactly once, and it is essential: it is what makes `ε` positive.
-/

open Finset Real

namespace NormalNumbers

namespace CastingOut

/-! ## The conjugate archimedean phase -/

/-- `p^{−it}`: the conjugate of `Erdos67b.archimedeanTwist`. -/
noncomputable def archPhase (t : ℝ) (p : ℕ) : ℂ := (p : ℂ) ^ (-(Complex.I * (t : ℂ)))

theorem conj_archimedeanTwist_eq (t : ℝ) (p : ℕ) :
    (starRingEnd ℂ) (Erdos67b.archimedeanTwist t p) = archPhase t p :=
  Erdos67b.conj_archimedeanTwist t p

theorem norm_archPhase {p : ℕ} (hp : 0 < p) (t : ℝ) : ‖archPhase t p‖ = 1 := by
  rw [← conj_archimedeanTwist_eq, RCLike.norm_conj]
  exact Erdos67b.norm_archimedeanTwist hp t

/-- The phase written as a unit-circle exponential: `p^{−it} = exp((−t log p) i)`. -/
theorem archPhase_eq_exp {p : ℕ} (hp : 0 < p) (t : ℝ) :
    archPhase t p = Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I) := by
  have hp0 : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  rw [archPhase, Complex.cpow_def_of_ne_zero hp0]
  congr 1
  rw [← Complex.natCast_log]
  push_cast
  ring

/-! ## The bridge: distance = mass − Re (z · twisted prime sum) -/

/-- The dependency's prime index set is mathlib's. -/
theorem primesUpTo_eq_primesLE (X : ℕ) : Erdos67b.primesUpTo X = Nat.primesLE X := rfl

/-- The twisted prime sum `∑_{p ≤ X} conj(χ(p) p^{it}) / p`. -/
noncomputable def twistPrimeSum {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) : ℂ :=
  ∑ p ∈ Erdos67b.primesUpTo X,
    (starRingEnd ℂ) (Erdos67b.dirichletArchimedeanTwist χ t p) / (p : ℂ)

/-- On a prime, `ζ^Ω` takes the constant value `z`. -/
theorem restrictToNat_zOmInt_prime {z : ℂ} {p : ℕ} (hp : p.Prime) :
    Erdos67b.restrictToNat (zOmInt z) p = z := by
  rw [Erdos67b.restrictToNat, zOmInt, Erdos67b.positiveIntExtension_natCast hp.pos,
    ArithmeticFunction.cardFactors_apply_prime hp, pow_one]

/-- **The bridge.**  The pretentious distance from `ζ^Ω` to any Dirichlet–archimedean twist is
exactly the prime mass minus the real part of `z` times the twisted prime sum. -/
theorem pretentiousDistSqToTwist_zOm_eq (z : ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (X : ℕ) :
    Erdos67b.pretentiousDistSqToTwist (Erdos67b.restrictToNat (zOmInt z)) χ t X
      = Erdos67b.PrimeEstimates.primeReciprocals X - (z * twistPrimeSum χ t X).re := by
  rw [Erdos67b.pretentiousDistSqToTwist, Erdos67b.pretentiousDistSq, twistPrimeSum,
    Finset.mul_sum, Complex.re_sum, Erdos67b.PrimeEstimates.primeReciprocals,
    Erdos784.Analytic.primeReciprocals, ← primesUpTo_eq_primesLE,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Erdos67b.mem_primesUpTo] at hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.1.pos
  rw [Erdos67b.pretentiousTerm, restrictToNat_zOmInt_prime hp.1]
  have : z * ((starRingEnd ℂ) (Erdos67b.dirichletArchimedeanTwist χ t p) / (p : ℂ))
      = (z * (starRingEnd ℂ) (Erdos67b.dirichletArchimedeanTwist χ t p)) / (p : ℂ) := by ring
  rw [this, Complex.div_natCast_re]
  field_simp

/-- **The `z`-free lower bound.**  Only a bound on the classical twisted prime sum is needed. -/
theorem pretentiousDistSqToTwist_zOm_ge {z : ℂ} (hz : ‖z‖ = 1) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) :
    Erdos67b.PrimeEstimates.primeReciprocals X - ‖twistPrimeSum χ t X‖
      ≤ Erdos67b.pretentiousDistSqToTwist (Erdos67b.restrictToNat (zOmInt z)) χ t X := by
  rw [pretentiousDistSqToTwist_zOm_eq z χ t X]
  have h : (z * twistPrimeSum χ t X).re ≤ ‖twistPrimeSum χ t X‖ := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul, hz, one_mul]
  linarith


/-! ## The resonance window -/

/-- The half-width of the resonance window, `|arg z| / 2`.  Positive exactly when `z ≠ 1`, and
`≤ π/2` always; both facts are used, and the first is the ONLY place `z ≠ 1` enters. -/
noncomputable def resEps (z : ℂ) : ℝ := |z.arg| / 2

theorem resEps_pos {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) : 0 < resEps z := by
  have harg : z.arg ≠ 0 := by
    intro h
    rw [Complex.arg_eq_zero_iff] at h
    apply hz1
    have hz' : z = ((z.re : ℝ) : ℂ) := by
      refine Complex.ext rfl ?_
      simp [h.2]
    rw [hz', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1] at hz
    rw [hz', hz]
    norm_num
  have : 0 < |z.arg| := abs_pos.mpr harg
  rw [resEps]; linarith

theorem resEps_nonneg (z : ℂ) : 0 ≤ resEps z := by
  rw [resEps]; positivity

theorem resEps_le_pi_div_two (z : ℂ) : resEps z ≤ π / 2 := by
  rw [resEps]
  linarith [Complex.abs_arg_le_pi z]

/-- The unimodular phase attached to a prime: `z · p^{−it}`. -/
noncomputable def primePhase (z : ℂ) (t : ℝ) (p : ℕ) : ℂ := z * archPhase t p

theorem norm_primePhase {z : ℂ} (hz : ‖z‖ = 1) {p : ℕ} (hp : 0 < p) (t : ℝ) :
    ‖primePhase z t p‖ = 1 := by
  rw [primePhase, norm_mul, hz, norm_archPhase hp, one_mul]

theorem primePhase_ne_zero {z : ℂ} (hz : ‖z‖ = 1) {p : ℕ} (hp : 0 < p) (t : ℝ) :
    primePhase z t p ≠ 0 := by
  intro h
  have h1 := norm_primePhase hz hp t
  rw [h, norm_zero] at h1
  norm_num at h1

/-- **Off the resonance window the full `1 − cos ε` is collected.** -/
theorem one_sub_re_primePhase_ge {z : ℂ} (hz : ‖z‖ = 1) {p : ℕ} (hp : 0 < p) {t : ℝ}
    (hgood : resEps z ≤ |(primePhase z t p).arg|) :
    1 - Real.cos (resEps z) ≤ 1 - (primePhase z t p).re := by
  have hre : (primePhase z t p).re = Real.cos ((primePhase z t p).arg) := by
    rw [Complex.cos_arg (primePhase_ne_zero hz hp t), norm_primePhase hz hp t, div_one]
  have hcos : Real.cos |(primePhase z t p).arg| ≤ Real.cos (resEps z) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (resEps_nonneg z) (Complex.abs_arg_le_pi _) hgood
  rw [Real.cos_abs] at hcos
  rw [hre]
  linarith

/-! ## The covering: a resonant prime sits in one of `O(T)` multiplicative windows -/

/-- `z · p^{−it} = exp ((arg z − t log p) i)`, hence its argument differs from
`arg z − t log p` by a multiple of `2π`.  This is the covering step: it converts the analytic
resonance condition into an arithmetic window on `log p`. -/
theorem exists_int_arg_primePhase {z : ℂ} (hz : ‖z‖ = 1) {p : ℕ} (hp : 0 < p) (t : ℝ) :
    ∃ m : ℤ, z.arg - t * Real.log p - 2 * π * m = (primePhase z t p).arg := by
  have hzexp : z = Complex.exp ((z.arg : ℂ) * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rw [hz] at h
    simpa using h.symm
  have hu : primePhase z t p
      = Complex.exp (((z.arg - t * Real.log p : ℝ) : ℂ) * Complex.I) := by
    have h1 : Complex.exp (((z.arg - t * Real.log p : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((z.arg : ℂ) * Complex.I)
          * Complex.exp (((-(t * Real.log p) : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [h1, ← hzexp, primePhase, archPhase_eq_exp hp]
  have hu2 : primePhase z t p
      = Complex.exp ((((primePhase z t p).arg : ℝ) : ℂ) * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I (primePhase z t p)
    rw [norm_primePhase hz hp t] at h
    simpa using h.symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (hu.symm.trans hu2)
  refine ⟨n, ?_⟩
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2 : (((z.arg - t * Real.log p : ℝ)) : ℂ) * Complex.I
      = ((((primePhase z t p).arg : ℝ) : ℂ) + (n : ℂ) * (2 * π)) * Complex.I := by
    rw [hn]; ring
  have h3 : (((z.arg - t * Real.log p : ℝ)) : ℂ)
      = (((primePhase z t p).arg : ℝ) : ℂ) + (n : ℂ) * (2 * π) :=
    mul_right_cancel₀ hI h2
  have hreal : z.arg - t * Real.log p = (primePhase z t p).arg + n * (2 * π) := by
    exact_mod_cast h3
  linarith

/-- The shifted argument `arg z − 2πm` is never smaller than `2ε` in absolute value: for
`m = 0` it IS `2ε`, and for `m ≠ 0` it is at least `π`.  This uniform gap is what forces the
window ratio `≤ 3` below, independently of `t` and of `m`. -/
theorem two_resEps_le_abs_shift (z : ℂ) (m : ℤ) : 2 * resEps z ≤ |z.arg - 2 * π * m| := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [resEps]
    linarith
  · have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hm
    have hpi : (0 : ℝ) < π := Real.pi_pos
    have h1 : 2 * π ≤ |2 * π * (m : ℝ)| := by
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * π)]
      nlinarith
    have h2 : |z.arg| ≤ π := Complex.abs_arg_le_pi z
    have h3 : |2 * π * (m:ℝ)| - |z.arg| ≤ |z.arg - 2 * π * m| := by
      have h := abs_sub_abs_le_abs_sub (2 * π * (m:ℝ)) z.arg
      rw [abs_sub_comm] at h
      linarith
    have h4 : 2 * resEps z ≤ π := by
      have := resEps_le_pi_div_two z; linarith
    linarith

/-! ## From resonance to a multiplicative window of bounded mass -/

/-- **The window.**  A resonant prime lands in one of the windows
`|t|·log p ∈ (γ_m − ε, γ_m + ε)` with `γ_m = |arg z − 2πm|`. -/
theorem exists_window_of_resonant {z : ℂ} (hz : ‖z‖ = 1) {p : ℕ} (hp : 2 ≤ p) {t : ℝ}
    (hres : |(primePhase z t p).arg| < resEps z) :
    ∃ m : ℤ, |z.arg - 2 * π * m| - resEps z < |t| * Real.log p ∧
             |t| * Real.log p < |z.arg - 2 * π * m| + resEps z := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  obtain ⟨m, hm⟩ := exists_int_arg_primePhase hz hp0 t
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have heps : 0 < resEps z := lt_of_le_of_lt (abs_nonneg _) hres
  have hgap : 2 * resEps z ≤ |z.arg - 2 * π * m| := two_resEps_le_abs_shift z m
  have hkey : |(z.arg - 2 * π * m) - t * Real.log p| < resEps z := by
    have hc : (z.arg - 2 * π * m) - t * Real.log p = (primePhase z t p).arg := by
      rw [← hm]; ring
    rw [hc]; exact hres
  have habs : |(|z.arg - 2 * π * m|) - |t| * Real.log p| < resEps z := by
    rcases le_or_gt 0 t with hts | hts
    · have hcpos : 0 < z.arg - 2 * π * m := by
        by_contra hcon
        push_neg at hcon
        have h1 : |z.arg - 2 * π * m| = -(z.arg - 2 * π * m) := abs_of_nonpos hcon
        have h2 := (abs_lt.1 hkey).1
        have h3 : 0 ≤ t * Real.log p := mul_nonneg hts hL.le
        rw [h1] at hgap
        linarith
      rw [abs_of_pos hcpos, abs_of_nonneg hts]
      exact hkey
    · have hcneg : z.arg - 2 * π * m < 0 := by
        by_contra hcon
        push_neg at hcon
        have h1 : |z.arg - 2 * π * m| = z.arg - 2 * π * m := abs_of_nonneg hcon
        have h2 := (abs_lt.1 hkey).2
        have h3 : t * Real.log p < 0 := mul_neg_of_neg_of_pos hts hL
        rw [h1] at hgap
        linarith
      rw [abs_of_neg hcneg, abs_of_neg hts]
      have hrw : -(z.arg - 2 * π * m) - -t * Real.log p
          = -((z.arg - 2 * π * m) - t * Real.log p) := by ring
      rw [hrw, abs_neg]
      exact hkey
  have hsplit := abs_lt.1 habs
  exact ⟨m, by linarith [hsplit.2], by linarith [hsplit.1]⟩

/-- A uniform bound for the reciprocal mass of the primes in any multiplicative window
`(U, U³]`.  Constants are not optimised; only `X`-independence matters. -/
noncomputable def windowMassBound : ℝ :=
  Real.log 6 + 2 * Erdos67b.PrimeEstimates.mertensBound + 4

/-- Interval Mertens in ratio form: if `log v ≤ ρ log u` then the primes in `(u,v]` carry
reciprocal mass at most `log ρ + 2·mertensBound`. -/
theorem reciprocalPrimeInterval_le_log_ratio {u v : ℕ} (hu : 2 ≤ u) (huv : u ≤ v) {ρ : ℝ}
    (hρ : 0 < ρ) (hlog : Real.log v ≤ ρ * Real.log u) :
    Erdos67b.PrimeEstimates.reciprocalPrimeInterval u v
      ≤ Real.log ρ + 2 * Erdos67b.PrimeEstimates.mertensBound := by
  have hv : 2 ≤ v := hu.trans huv
  have hlu : 0 < Real.log u := Real.log_pos (by exact_mod_cast hu)
  have hlv : 0 < Real.log v := Real.log_pos (by exact_mod_cast hv)
  have hmain := Erdos67b.PrimeEstimates.reciprocalPrimeInterval_le_log_log_sub_add hu huv
  have hstep : Real.log (Real.log v) ≤ Real.log ρ + Real.log (Real.log u) := by
    calc Real.log (Real.log v) ≤ Real.log (ρ * Real.log u) := Real.log_le_log hlv hlog
      _ = Real.log ρ + Real.log (Real.log u) := Real.log_mul (ne_of_gt hρ) (ne_of_gt hlu)
  linarith

/-- **The bounded-mass window.**  Any set of primes confined to a single resonance window
`|t|·log p ∈ (γ − ε, γ + ε)` — with `γ = |arg z − 2πm| ≥ 2ε`, which is automatic — carries
reciprocal mass at most an absolute constant, *independently of `t`, of `m` and of `X`*.

The mechanism: the window in `log p` is `((γ−ε)/|t|, (γ+ε)/|t|)`, whose endpoint RATIO is
`(γ+ε)/(γ−ε) ≤ 3` — the `|t|` cancels — so the primes it holds lie in a fixed multiplicative
range `(U, U³]`, and the dependency's two-sided Mertens theorem bounds that. -/
theorem window_mass_le {z : ℂ} {t : ℝ} (ht : t ≠ 0) (m : ℤ) (heps : 0 < resEps z)
    {G : Finset ℕ} (hGp : ∀ p ∈ G, p.Prime)
    (hGw : ∀ p ∈ G, |z.arg - 2 * π * m| - resEps z < |t| * Real.log p ∧
                     |t| * Real.log p < |z.arg - 2 * π * m| + resEps z) :
    ∑ p ∈ G, (p : ℝ)⁻¹ ≤ windowMassBound := by
  set γ := |z.arg - 2 * π * m| with hγ
  set ε := resEps z with hε
  have hgap : 2 * ε ≤ γ := two_resEps_le_abs_shift z m
  have htpos : 0 < |t| := abs_pos.mpr ht
  set a := (γ - ε) / |t| with ha
  set b := (γ + ε) / |t| with hb
  have hapos : 0 < a := by rw [ha]; apply div_pos (by linarith) htpos
  have hab : b ≤ 3 * a := by
    rw [ha, hb, ← sub_nonneg]
    have : 3 * ((γ - ε) / |t|) - (γ + ε) / |t| = (2 * γ - 4 * ε) / |t| := by
      field_simp; ring
    rw [this]
    apply div_nonneg (by linarith) htpos.le
  -- every member of `G` sits in the real window `(exp a, exp b)`
  have hmem : ∀ p ∈ G, Real.exp a < (p : ℝ) ∧ (p : ℝ) < Real.exp b := by
    intro p hp
    have hpp := hGp p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlpos : 0 < Real.log p := Real.log_pos (by linarith)
    obtain ⟨h1, h2⟩ := hGw p hp
    have hloga : a < Real.log p := by
      rw [ha, div_lt_iff₀ htpos]
      linarith [mul_comm (Real.log (p : ℝ)) |t|]
    have hlogb : Real.log p < b := by
      rw [hb, lt_div_iff₀ htpos]
      linarith [mul_comm (Real.log (p : ℝ)) |t|]
    constructor
    · calc Real.exp a < Real.exp (Real.log p) := Real.exp_lt_exp.2 hloga
        _ = (p : ℝ) := Real.exp_log (by linarith)
    · calc (p : ℝ) = Real.exp (Real.log p) := (Real.exp_log (by linarith)).symm
        _ < Real.exp b := Real.exp_lt_exp.2 hlogb
  have hM : 0 ≤ Erdos67b.PrimeEstimates.mertensBound :=
    Erdos67b.PrimeEstimates.mertensBound_nonneg
  have hlog6 : (0 : ℝ) ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  rcases le_or_gt (Real.log 4) a with hcase | hcase
  · -- the window lies above `4`: a genuine multiplicative range `(u, u⁶]`
    set u := ⌊Real.exp a⌋₊ with hu
    set v := ⌊Real.exp b⌋₊ with hv
    have hexp4 : (4 : ℝ) ≤ Real.exp a := by
      calc (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp a := Real.exp_le_exp.2 hcase
    have hu4 : 4 ≤ u := Nat.le_floor (by exact_mod_cast hexp4)
    have hu2 : 2 ≤ u := by omega
    have hab0 : a ≤ b := by
      rw [ha, hb, sub_div, add_div]
      have : 0 ≤ ε / |t| := div_nonneg heps.le htpos.le
      linarith
    have habexp : Real.exp a ≤ Real.exp b := Real.exp_le_exp.2 hab0
    have huv : u ≤ v := Nat.floor_le_floor habexp
    have hsub : G ⊆ Erdos67b.PrimeEstimates.primesInInterval u v := by
      intro p hp
      obtain ⟨h1, h2⟩ := hmem p hp
      rw [Erdos67b.PrimeEstimates.mem_primesInInterval]
      refine ⟨?_, ?_, hGp p hp⟩
      · have : (u : ℝ) < (p : ℝ) :=
          lt_of_le_of_lt (Nat.floor_le (Real.exp_nonneg a)) h1
        exact_mod_cast this
      · exact Nat.le_floor h2.le
    have hulog : a - Real.log 2 ≤ Real.log u := by
      have hufloor : Real.exp a - 1 < (u : ℝ) := by
        have := Nat.sub_one_lt_floor (Real.exp a)
        linarith
      have hhalf : Real.exp a / 2 ≤ (u : ℝ) := by linarith
      have h2pos : (0 : ℝ) < Real.exp a / 2 := by positivity
      calc a - Real.log 2 = Real.log (Real.exp a / 2) := by
            rw [Real.log_div (Real.exp_ne_zero a) (by norm_num), Real.log_exp]
        _ ≤ Real.log u := Real.log_le_log h2pos hhalf
    have hvlog : Real.log v ≤ b := by
      have hvle : (v : ℝ) ≤ Real.exp b := Nat.floor_le (Real.exp_nonneg b)
      have hvpos : (0 : ℝ) < (v : ℝ) := by
        have : 2 ≤ v := hu2.trans huv
        exact_mod_cast lt_of_lt_of_le (by norm_num) this
      calc Real.log v ≤ Real.log (Real.exp b) := Real.log_le_log hvpos hvle
        _ = b := Real.log_exp b
    have hlog2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hratio : Real.log v ≤ 6 * Real.log u := by
      have : 6 * (a - Real.log 2) ≤ 6 * Real.log u := by linarith
      have hba : b ≤ 3 * a := hab
      rw [hlog2] at hcase
      linarith
    have hmain := reciprocalPrimeInterval_le_log_ratio hu2 huv (by norm_num : (0:ℝ) < 6) hratio
    have hsum : ∑ p ∈ G, (p : ℝ)⁻¹
        ≤ Erdos67b.PrimeEstimates.reciprocalPrimeInterval u v := by
      rw [Erdos67b.PrimeEstimates.reciprocalPrimeInterval]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    rw [windowMassBound]
    linarith
  · -- the window is entirely below `64`: bound by the total mass up to `63`
    have hb64 : Real.exp b < 64 := by
      have h3 : b < 3 * Real.log 4 := by linarith
      have h64 : Real.log 64 = 3 * Real.log 4 := by
        rw [show (64 : ℝ) = 4 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
      calc Real.exp b < Real.exp (Real.log 64) := Real.exp_lt_exp.2 (by linarith)
        _ = 64 := Real.exp_log (by norm_num)
    have hsub : G ⊆ Erdos67b.primesUpTo 63 := by
      intro p hp
      obtain ⟨_, h2⟩ := hmem p hp
      rw [Erdos67b.mem_primesUpTo]
      refine ⟨hGp p hp, ?_⟩
      have : (p : ℝ) < 64 := lt_trans h2 hb64
      have : p < 64 := by exact_mod_cast this
      omega
    have hsum : ∑ p ∈ G, (p : ℝ)⁻¹ ≤ Erdos67b.PrimeEstimates.primeReciprocals 63 := by
      rw [Erdos67b.PrimeEstimates.primeReciprocals, Erdos784.Analytic.primeReciprocals,
        ← primesUpTo_eq_primesLE]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    have hmert := Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le
      (by norm_num : 2 ≤ 63)
    rw [abs_le] at hmert
    have hl63 : Real.log ((63 : ℕ) : ℝ) ≤ 5 := by
      have h1 : Real.log ((63 : ℕ) : ℝ) ≤ Real.log 64 := by
        apply Real.log_le_log (by norm_num) (by norm_num)
      have h64 : Real.log 64 = 6 * Real.log 2 := by
        rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; push_cast; ring
      have h2 : Real.log 2 < 0.7 := by
        have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
      linarith
    have hll : Real.log (Real.log ((63 : ℕ) : ℝ)) ≤ 4 := by
      have hpos : 0 < Real.log ((63 : ℕ) : ℝ) := Real.log_pos (by norm_num)
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    rw [windowMassBound]
    linarith

/-! ## Range 1: only `O(T)` windows meet `[2, X]`, so the resonance mass is a constant -/

open scoped Classical in
/-- The index of the resonance window a prime falls into (junk value `0` if it is not
resonant). -/
noncomputable def windowIndex (z : ℂ) (t : ℝ) (p : ℕ) : ℤ :=
  if h : ∃ m : ℤ, |z.arg - 2 * π * m| - resEps z < |t| * Real.log p ∧
                   |t| * Real.log p < |z.arg - 2 * π * m| + resEps z
  then h.choose else 0

theorem windowIndex_spec {z : ℂ} (hz : ‖z‖ = 1) {p : ℕ} (hp : 2 ≤ p) {t : ℝ}
    (hres : |(primePhase z t p).arg| < resEps z) :
    |z.arg - 2 * π * windowIndex z t p| - resEps z < |t| * Real.log p ∧
      |t| * Real.log p < |z.arg - 2 * π * windowIndex z t p| + resEps z := by
  have hex := exists_window_of_resonant hz hp hres
  rw [windowIndex, dif_pos hex]
  exact hex.choose_spec

/-- The window count: with `|t| log p ≤ T` only the indices `|m| ≤ windowCount T z` occur. -/
noncomputable def windowCount (T : ℝ) (z : ℂ) : ℕ := ⌈(T + resEps z + π) / (2 * π)⌉₊

theorem abs_windowIndex_le {z : ℂ} (hz : ‖z‖ = 1) {p : ℕ} (hp : 2 ≤ p) {t : ℝ} {T : ℝ}
    (hres : |(primePhase z t p).arg| < resEps z) (hT : |t| * Real.log p ≤ T) :
    |windowIndex z t p| ≤ (windowCount T z : ℤ) := by
  set m := windowIndex z t p with hm
  obtain ⟨h1, _⟩ := windowIndex_spec hz hp hres
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hlow : 2 * π * |(m : ℝ)| - π ≤ |z.arg - 2 * π * m| := by
    have h2 : |z.arg| ≤ π := Complex.abs_arg_le_pi z
    have h3 := abs_sub_abs_le_abs_sub (2 * π * (m : ℝ)) z.arg
    rw [abs_sub_comm] at h3
    have h4 : |2 * π * (m : ℝ)| = 2 * π * |(m : ℝ)| := by
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * π)]
    linarith [h3, h4 ▸ h3]
  have hbound : 2 * π * |(m : ℝ)| - π - resEps z < T := by linarith
  have hfin : |(m : ℝ)| ≤ (T + resEps z + π) / (2 * π) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 2 * π)]
    nlinarith
  have hceil : (T + resEps z + π) / (2 * π) ≤ (windowCount T z : ℝ) :=
    Nat.le_ceil _
  have : |(m : ℝ)| ≤ (windowCount T z : ℝ) := le_trans hfin hceil
  rw [← Int.cast_abs] at this
  exact_mod_cast this

/-- **The Range-1 resonance bound.**  Under `|t| log p ≤ T` the resonant primes carry
reciprocal mass at most `(2·windowCount + 1)·windowMassBound` — a constant depending on `T`
and `z` only, and in particular **independent of `X` and of `t`**. -/
theorem resonant_mass_le {z : ℂ} (hz : ‖z‖ = 1) {t : ℝ} (ht : t ≠ 0) (heps : 0 < resEps z)
    {T : ℝ} {R : Finset ℕ} (hRp : ∀ p ∈ R, p.Prime)
    (hRres : ∀ p ∈ R, |(primePhase z t p).arg| < resEps z)
    (hRT : ∀ p ∈ R, |t| * Real.log p ≤ T) :
    ∑ p ∈ R, (p : ℝ)⁻¹ ≤ (2 * (windowCount T z) + 1 : ℕ) * windowMassBound := by
  classical
  set M₀ := windowCount T z with hM₀
  have hmaps : ∀ p ∈ R, windowIndex z t p ∈ Finset.Icc (-(M₀ : ℤ)) (M₀ : ℤ) := by
    intro p hp
    have h := abs_windowIndex_le hz (hRp p hp).two_le (hRres p hp) (hRT p hp)
    rw [Finset.mem_Icc]
    constructor <;> [linarith [abs_le.1 h |>.1]; linarith [abs_le.1 h |>.2]]
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps (fun p : ℕ => (p : ℝ)⁻¹)
  rw [← hfiber]
  have hcard : ∀ m ∈ Finset.Icc (-(M₀ : ℤ)) (M₀ : ℤ),
      ∑ p ∈ R with windowIndex z t p = m, (p : ℝ)⁻¹ ≤ windowMassBound := by
    intro m _
    refine window_mass_le ht m heps (fun p hp => hRp p (Finset.mem_filter.1 hp).1) ?_
    intro p hp
    obtain ⟨hpR, hpm⟩ := Finset.mem_filter.1 hp
    have := windowIndex_spec hz (hRp p hpR).two_le (hRres p hpR)
    rwa [hpm] at this
  calc ∑ m ∈ Finset.Icc (-(M₀ : ℤ)) (M₀ : ℤ), ∑ p ∈ R with windowIndex z t p = m, (p : ℝ)⁻¹
      ≤ ∑ _m ∈ Finset.Icc (-(M₀ : ℤ)) (M₀ : ℤ), windowMassBound := Finset.sum_le_sum hcard
    _ = ((Finset.Icc (-(M₀ : ℤ)) (M₀ : ℤ)).card : ℝ) * windowMassBound := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (2 * M₀ + 1 : ℕ) * windowMassBound := by
        have hc : (Finset.Icc (-(M₀ : ℤ)) (M₀ : ℤ)).card = 2 * M₀ + 1 := by
          rw [Int.card_Icc]; omega
        rw [hc]

/-! ## Range 1: assembling the certificate -/

/-- On a prime in the class `1 (mod q)` the twist is purely archimedean, so the pretentious
term is exactly `(1 − Re (z·p^{−it}))/p`. -/
theorem pretentiousTerm_class_eq (z : ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    {p : ℕ} (hp : p.Prime) (hpq : (p : ZMod q) = 1) :
    Erdos67b.pretentiousTerm (Erdos67b.restrictToNat (zOmInt z))
        (Erdos67b.dirichletArchimedeanTwist χ t) p
      = (1 - (primePhase z t p).re) / p := by
  have hg : (starRingEnd ℂ) (Erdos67b.dirichletArchimedeanTwist χ t p) = archPhase t p := by
    rw [Erdos67b.dirichletArchimedeanTwist, map_mul, hpq, map_one, map_one, one_mul,
      conj_archimedeanTwist_eq]
  rw [Erdos67b.pretentiousTerm, restrictToNat_zOmInt_prime hp, hg, primePhase]

/-- Every pretentious term at a prime is nonnegative for a unimodular `ζ^Ω`. -/
theorem pretentiousTerm_nonneg_prime {z : ℂ} (hz : ‖z‖ = 1) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {p : ℕ} (hp : p.Prime) :
    0 ≤ Erdos67b.pretentiousTerm (Erdos67b.restrictToNat (zOmInt z))
        (Erdos67b.dirichletArchimedeanTwist χ t) p := by
  rw [Erdos67b.pretentiousTerm]
  have hnorm : ‖Erdos67b.restrictToNat (zOmInt z) p
      * (starRingEnd ℂ) (Erdos67b.dirichletArchimedeanTwist χ t p)‖ ≤ 1 := by
    rw [norm_mul, RCLike.norm_conj, restrictToNat_zOmInt_prime hp, hz, one_mul]
    exact Erdos67b.norm_dirichletArchimedeanTwist_le_one χ t hp.pos
  have hre := le_trans (Complex.re_le_norm _) hnorm
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have : (0 : ℝ) ≤ 1 - (Erdos67b.restrictToNat (zOmInt z) p
      * (starRingEnd ℂ) (Erdos67b.dirichletArchimedeanTwist χ t p)).re := by linarith
  positivity

/-- **The good primes deliver.**  Any set `G` of primes `≤ X` in the class `1 (mod q)` that
avoids the resonance window contributes `(1 − cos ε)` times its reciprocal mass. -/
theorem pretentiousDistSq_ge_sum_good {z : ℂ} (hz : ‖z‖ = 1) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) {G : Finset ℕ}
    (hGsub : G ⊆ Erdos67b.primesUpTo X)
    (hGq : ∀ p ∈ G, (p : ZMod q) = 1)
    (hGgood : ∀ p ∈ G, resEps z ≤ |(primePhase z t p).arg|) :
    (1 - Real.cos (resEps z)) * ∑ p ∈ G, (p : ℝ)⁻¹
      ≤ Erdos67b.pretentiousDistSqToTwist (Erdos67b.restrictToNat (zOmInt z)) χ t X := by
  rw [Erdos67b.pretentiousDistSqToTwist, Erdos67b.pretentiousDistSq]
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hGsub
    (fun p hp _ => pretentiousTerm_nonneg_prime hz χ t (Erdos67b.mem_primesUpTo.1 hp).1))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp : p.Prime := (Erdos67b.mem_primesUpTo.1 (hGsub hp)).1
  rw [pretentiousTerm_class_eq z χ t hpp (hGq p hp), div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (one_sub_re_primePhase_ge hz hpp.pos (hGgood p hp))
    (by positivity)

open scoped Classical in
/-- The primes `≤ X` in the residue class `1 (mod q)`. -/
noncomputable def classPrimes (q X : ℕ) : Finset ℕ :=
  (Erdos67b.primesUpTo X).filter (fun p => (p : ZMod q) = 1)

/-- **The Range-1 inequality.**  If every prime `p ≤ X` satisfies `|t|·log p ≤ T`, then the
pretentious distance from `ζ^Ω` to `χ·n^{it}` is at least `(1 − cos ε)` times the class-`1
(mod q)` prime mass, less an `X`-INDEPENDENT constant.  The constant depends only on `T` and
`z`; the mass grows like `(1/φ(q))·log log X`.  This is the whole of the archimedean
certificate below the `T/log X` threshold. -/
theorem range_one_mass_bound {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {T : ℝ} (X : ℕ)
    (hT : ∀ p ∈ Erdos67b.primesUpTo X, |t| * Real.log p ≤ T) :
    (1 - Real.cos (resEps z))
        * ((∑ p ∈ classPrimes q X, (p : ℝ)⁻¹)
            - (2 * windowCount T z + 1 : ℕ) * windowMassBound)
      ≤ Erdos67b.pretentiousDistSqToTwist (Erdos67b.restrictToNat (zOmInt z)) χ t X := by
  classical
  have heps : 0 < resEps z := resEps_pos hz hz1
  set C := classPrimes q X with hC
  set R := C.filter (fun p => |(primePhase z t p).arg| < resEps z) with hR
  set G := C.filter (fun p => ¬ |(primePhase z t p).arg| < resEps z) with hG
  have hCsub : C ⊆ Erdos67b.primesUpTo X := by
    rw [hC, classPrimes]; exact Finset.filter_subset _ _
  have hprime : ∀ p ∈ C, p.Prime := fun p hp => (Erdos67b.mem_primesUpTo.1 (hCsub hp)).1
  have hsplit : ∑ p ∈ R, (p : ℝ)⁻¹ + ∑ p ∈ G, (p : ℝ)⁻¹ = ∑ p ∈ C, (p : ℝ)⁻¹ :=
    Finset.sum_filter_add_sum_filter_not C _ _
  -- the resonant part is a constant
  have hRbound : ∑ p ∈ R, (p : ℝ)⁻¹ ≤ (2 * windowCount T z + 1 : ℕ) * windowMassBound := by
    rcases eq_or_ne t 0 with rfl | ht
    · have hempty : R = ∅ := by
        rw [hR]
        refine Finset.filter_false_of_mem fun p hp => ?_
        have hph : primePhase z 0 p = z := by
          rw [primePhase, archPhase, Complex.ofReal_zero, mul_zero, neg_zero,
            Complex.cpow_zero, mul_one]
        rw [hph]
        have : 2 * resEps z ≤ |z.arg| := by rw [resEps]; linarith
        push_neg
        linarith
      rw [hempty, Finset.sum_empty]
      have : (0 : ℝ) ≤ windowMassBound := by
        rw [windowMassBound]
        have := Erdos67b.PrimeEstimates.mertensBound_nonneg
        have h6 : (0 : ℝ) ≤ Real.log 6 := Real.log_nonneg (by norm_num)
        linarith
      positivity
    · refine resonant_mass_le hz ht heps
        (fun p hp => hprime p (Finset.mem_filter.1 hp).1) (fun p hp => (Finset.mem_filter.1 hp).2)
        (fun p hp => hT p (hCsub (Finset.mem_filter.1 hp).1))
  -- the good part delivers
  have hGgood : ∀ p ∈ G, resEps z ≤ |(primePhase z t p).arg| := by
    intro p hp
    have := (Finset.mem_filter.1 hp).2
    linarith [not_lt.1 this]
  have hmain := pretentiousDistSq_ge_sum_good hz χ t X
    (G := G) (fun p hp => hCsub (Finset.mem_filter.1 hp).1)
    (fun p hp => (by
      have := (Finset.mem_filter.1 hp).1
      rw [hC, classPrimes, Finset.mem_filter] at this
      exact this.2)) hGgood
  have hcos : 0 ≤ 1 - Real.cos (resEps z) := by
    have := Real.cos_le_one (resEps z); linarith
  refine le_trans ?_ hmain
  apply mul_le_mul_of_nonneg_left _ hcos
  linarith


/-! ## Range 1: Mertens in the class makes the mass grow without bound

`range_one_mass_bound` subtracts an `X`-independent constant from the class-`1 (mod q)` prime
mass.  Mertens in the progression (`G4.MertensAP.mertensRate_residueClass`) says that mass is
`≥ c·log log X − C`, so for `X` large the difference beats any prescribed `A`.  The resulting
`range_one_certificate` is exactly Elliott's hypothesis for `ζ^Ω` in the low-frequency range
`|t| ≤ T / log X`, uniformly in the Dirichlet character.
-/

/-- The Mertens index set (primes `< X`) sits inside `classPrimes q X` (primes `≤ X`), so the
Mertens lower bound transfers in the useful direction. -/
theorem sumInvPrimesIn_le_classPrimes (q X : ℕ) :
    G4.MertensAP.sumInvPrimesIn (fun p => (p : ZMod q) = 1) X
      ≤ ∑ p ∈ classPrimes q X, (p : ℝ)⁻¹ := by
  classical
  rw [G4.MertensAP.sumInvPrimesIn]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => by positivity)
  intro p hp
  obtain ⟨hpb, hpq⟩ := Finset.mem_filter.1 hp
  have hpp : p.Prime := Nat.prime_of_mem_primesBelow hpb
  have hplt : p < X := Nat.lt_of_mem_primesBelow hpb
  rw [classPrimes, Finset.mem_filter, Erdos67b.mem_primesUpTo]
  exact ⟨⟨hpp, hplt.le⟩, hpq⟩

/-- `1 − cos ε > 0` for the resonance half-width of a non-trivial `z`. -/
theorem one_sub_cos_resEps_pos {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    0 < 1 - Real.cos (resEps z) := by
  have h : Real.cos (resEps z) < Real.cos 0 :=
    Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl
      (le_trans (resEps_le_pi_div_two z) (by linarith [Real.pi_pos])) (resEps_pos hz hz1)
  rw [Real.cos_zero] at h
  linarith

/-- **The Range-1 certificate.**  For every target level `A` and every frequency budget `T`
there is an `X₀` beyond which `ζ^Ω` is `A`-far from *every* twist `χ(n)·n^{it}` whose frequency
satisfies `|t|·log X ≤ T`.  Uniform in `χ`: the proof only ever uses `χ(p) = 1` on the class
`p ≡ 1 (mod q)`. -/
theorem range_one_certificate {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (A T : ℝ)
    (q : ℕ) [NeZero q] :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      |t| * Real.log X ≤ T →
      A ≤ Erdos67b.pretentiousDistSqToTwist (Erdos67b.restrictToNat (zOmInt z)) χ t X := by
  classical
  obtain ⟨c, C, hc, hM⟩ := G4.MertensAP.mertensRate_residueClass
    (q := q) (a := (1 : ZMod q)) isUnit_one
  set ε := resEps z with hε
  have hcos : 0 < 1 - Real.cos ε := one_sub_cos_resEps_pos hz hz1
  set K := (2 * windowCount T z + 1 : ℕ) * windowMassBound with hK
  -- the level of class mass we need
  set L := A / (1 - Real.cos ε) + K + C with hL
  -- choose `X₀` so that `c · log log X ≥ L` for all `X ≥ X₀`
  have htend : Filter.Tendsto (fun n : ℕ => c * Real.log (Real.log n)) Filter.atTop
      Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hc
      ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
        tendsto_natCast_atTop_atTop)
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1
    ((htend.eventually_ge_atTop L).and (Filter.eventually_ge_atTop 2))
  refine ⟨X₀, fun X hX χ t hTle => ?_⟩
  obtain ⟨hLX, hX2⟩ := hX₀ X hX
  -- the hypothesis of `range_one_mass_bound`
  have hT : ∀ p ∈ Erdos67b.primesUpTo X, |t| * Real.log p ≤ T := by
    intro p hp
    obtain ⟨hpp, hpX⟩ := Erdos67b.mem_primesUpTo.1 hp
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg t)) hTle
    exact Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hpX)
  have hmain := range_one_mass_bound hz hz1 χ t X hT
  -- Mertens in the class, transferred to `classPrimes`
  have hmass : c * Real.log (Real.log X) - C
      ≤ ∑ p ∈ classPrimes q X, (p : ℝ)⁻¹ :=
    le_trans (hM X hX2) (sumInvPrimesIn_le_classPrimes q X)
  refine le_trans ?_ hmain
  have hdiv : A / (1 - Real.cos ε) + K ≤ ∑ p ∈ classPrimes q X, (p : ℝ)⁻¹ := by
    rw [hL] at hLX; linarith
  have hA : A = (1 - Real.cos ε) * (A / (1 - Real.cos ε)) := by field_simp
  rw [hA]
  refine mul_le_mul_of_nonneg_left ?_ hcos.le
  rw [hK] at hdiv
  linarith


/-! ## Range 1, uniformly over the moduli `q ≤ Q`

Elliott's hypothesis quantifies over all moduli `q ≤ A` at once, so the finitely many
thresholds `X₀(q)` must be merged.  Induction on `Q` does it: at each step one new modulus
joins, and `max` of the two thresholds works.
-/

theorem range_one_certificate_uniform {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (A T : ℝ) :
    ∀ Q : ℕ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ q : ℕ, 0 < q → q ≤ Q →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t| * Real.log X ≤ T →
      A ≤ Erdos67b.pretentiousDistSqToTwist (Erdos67b.restrictToNat (zOmInt z)) χ t X := by
  intro Q
  induction Q with
  | zero => exact ⟨0, fun X _ q hq hq0 => absurd (Nat.le_zero.1 hq0) hq.ne'⟩
  | succ Q ih =>
      obtain ⟨X₁, hX₁⟩ := ih
      haveI : NeZero (Q + 1) := ⟨Nat.succ_ne_zero Q⟩
      obtain ⟨X₂, hX₂⟩ := range_one_certificate hz hz1 A T (Q + 1)
      refine ⟨max X₁ X₂, fun X hX q hq hqQ χ t hTle => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hqQ) with h | h
      · exact hX₁ X (le_trans (le_max_left _ _) hX) q hq (Nat.lt_succ_iff.1 h) χ t hTle
      · subst h; exact hX₂ X (le_trans (le_max_right _ _) hX) χ t hTle

/-! ## Range 2: named once, and the assembly

`TwistedPrimeSumSaving` is the classical saving in the twisted prime sum above the frequency
threshold `T/log X`.  Equivalently `log|L(1 + 1/log X + it, χ)| ≤ log log X − A`: it IS the
Vinogradov–Korobov log-derivative bound, and it is the SAME analytic input the Erdős-67b
dependency itself isolates as `Erdos67b.PolynomialHeightPrimeCorrelationBound`.  The
2026-09-25 review recorded why no elementary route reaches it: resonance counting past
`|t| ≳ (log X)^K` needs primes in intervals of length `p/|t|`.  It is a NAMED OPEN INPUT, not
a lemma to attack.

The frequency ceiling `|t| ≤ A·X` is not cosmetic: by simultaneous approximation there are
arbitrarily large `t` with `t·log p` near `0 (mod 2π)` for every `p ≤ X` at once, and for
those the saving is false.  Elliott's hypothesis asks for exactly the bounded range. -/
def TwistedPrimeSumSaving (A : ℕ) (T : ℝ) : Prop :=
  ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ q : ℕ, 0 < q → q ≤ A →
    ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      T / Real.log X ≤ |t| → |t| ≤ (A : ℝ) * X →
      ‖twistPrimeSum χ t X‖ ≤ Erdos67b.PrimeEstimates.primeReciprocals X - A

/-- **Range 2 closes in two lines** against the named saving. -/
theorem range_two_certificate {z : ℂ} (hz : ‖z‖ = 1) {A : ℕ} {T : ℝ}
    (hsave : TwistedPrimeSumSaving A T) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ q : ℕ, 0 < q → q ≤ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
        T / Real.log X ≤ |t| → |t| ≤ (A : ℝ) * X →
        (A : ℝ) ≤ Erdos67b.pretentiousDistSqToTwist (Erdos67b.restrictToNat (zOmInt z)) χ t X := by
  obtain ⟨X₀, hX₀⟩ := hsave
  exact ⟨X₀, fun X hX q hq hqA χ t h1 h2 =>
    le_trans (by linarith [hX₀ X hX q hq hqA χ t h1 h2])
      (pretentiousDistSqToTwist_zOm_ge hz χ t X)⟩

/-- **The archimedean non-pretentiousness certificate for `ζ^Ω`.**  Granting only the named
Range-2 saving, `ζ^Ω` satisfies Elliott's hypothesis at level `A`: it is `A`-far from every
Dirichlet–Archimedean twist `χ(n)·n^{it}` with modulus `q ≤ A` and frequency `|t| ≤ A·X`,
for all large `X`.  Range 1 (`|t| ≤ T/log X`) is proved outright; Range 2 is the named
Vinogradov–Korobov input. -/
theorem nonPretentious_zOm {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) {A : ℕ} {T : ℝ}
    (hsave : TwistedPrimeSumSaving A T) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ q : ℕ, 0 < q → q ≤ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t| ≤ (A : ℝ) * X →
        (A : ℝ) ≤ Erdos67b.pretentiousDistSqToTwist (Erdos67b.restrictToNat (zOmInt z)) χ t X := by
  obtain ⟨X₁, hX₁⟩ := range_one_certificate_uniform hz hz1 (A : ℝ) T A
  obtain ⟨X₂, hX₂⟩ := range_two_certificate hz hsave
  refine ⟨max 2 (max X₁ X₂), fun X hX q hq hqA χ t ht => ?_⟩
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hlog : 0 < Real.log X :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hX2)
  rcases le_or_gt (|t| * Real.log X) T with h | h
  · exact hX₁ X (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX) q hq hqA χ t h
  · refine hX₂ X (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX) q hq hqA χ t
      ?_ ht
    rw [div_le_iff₀ hlog]
    linarith [h]


/-! ## The `D = 2` rung on exactly two named inputs

`initial_segment_bound_of_elliott` (`C3MrtRungTwo.lean`) consumes the non-pretentiousness of
`ζ^Ω` at the cutoffs `X = A^i`.  `nonPretentious_zOm` supplies it for all large `X`, so the
only thing to arrange is that the segment starts late enough: `A ≥ 2` gives `A^i ≥ 2^i > i`,
so `i > X₀` already forces `A^i > X₀`.
-/

/-- The Range-2 input, at every level `A` (the level grows with the cutoff exponent, so the
saving must be available for each of them, with its own frequency threshold `T`). -/
def TwistedPrimeSumSavingAllLevels : Prop :=
  ∀ A : ℕ, ∃ T : ℝ, TwistedPrimeSumSaving A T

/-- **The `D = 2` rung, conditional on exactly TWO named literature inputs.**  Granting
`Erdos67b.NonasymptoticLogElliott` (log-averaged Elliott, the dependency's own open bet) and
`TwistedPrimeSumSavingAllLevels` (Vinogradov–Korobov, the dependency's
`PolynomialHeightPrimeCorrelationBound`), the harmonic-weighted two-point correlation of
`ζ₀^Ω` and `ζ₁^Ω` along a nondegenerate affine pair is `o(log J)` on the initial segment.
Nothing else is assumed: the archimedean certificate is proved here. -/
theorem rung_two_of_named_inputs
    (helliott : Erdos67b.NonasymptoticLogElliott)
    (hsave : TwistedPrimeSumSavingAllLevels)
    {d e b₀ b₁ : ℕ} (hd : 0 < d) (he : 0 < e)
    (hdet : (e : ℤ) * (b₁ : ℤ) - (d : ℤ) * (b₀ : ℤ) ≠ 0)
    {z₀ z₁ : ℂ} (hz₀ : ‖z₀‖ = 1) (hz₁ : ‖z₁‖ = 1) (hz₀1 : z₀ ≠ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A₀ : ℕ, 2 ≤ A₀ ∧ ∀ A : ℕ, A₀ ≤ A → ∃ i₀ : ℕ, ∀ m : ℕ, i₀ ≤ m →
      ‖∑ j ∈ Finset.Ioc 0 (A ^ m),
          (Erdos67b.harmonicWeight j : ℂ) * zOmInt z₀ (Erdos67b.integerAffine e (b₀ : ℤ) j) *
            zOmInt z₁ (Erdos67b.integerAffine d (b₁ : ℤ) j)‖
        ≤ (1 + Real.log (A ^ i₀ : ℕ)) + (m : ℝ) * (ε * Real.log A) := by
  obtain ⟨A₀, hA₀2, hA₀⟩ :=
    initial_segment_bound_of_elliott helliott hd he hdet z₀ z₁ hz₀ hz₁ ε hε
  refine ⟨A₀, hA₀2, fun A hA => ?_⟩
  obtain ⟨T, hT⟩ := hsave A
  obtain ⟨X₀, hX₀⟩ := nonPretentious_zOm hz₀ hz₀1 hT
  refine ⟨X₀, fun m hm => hA₀ A hA X₀ (fun i hi q hq hqA χ t ht => ?_) m hm⟩
  have hA2 : 2 ≤ A := le_trans hA₀2 hA
  -- `A^i ≥ 2^i > i > X₀`
  have hpow : X₀ ≤ A ^ i := by
    have h1 : i < 2 ^ i := Nat.lt_two_pow_self
    have h2 : (2 : ℕ) ^ i ≤ A ^ i := Nat.pow_le_pow_left hA2 i
    omega
  exact hX₀ (A ^ i) hpow q hq hqA χ t (by exact_mod_cast ht)

end CastingOut

end NormalNumbers

-- axiom audit
#print axioms NormalNumbers.CastingOut.pretentiousDistSqToTwist_zOm_eq
#print axioms NormalNumbers.CastingOut.pretentiousDistSqToTwist_zOm_ge
#print axioms NormalNumbers.CastingOut.exists_window_of_resonant
#print axioms NormalNumbers.CastingOut.window_mass_le
#print axioms NormalNumbers.CastingOut.resonant_mass_le
#print axioms NormalNumbers.CastingOut.range_one_mass_bound
#print axioms NormalNumbers.CastingOut.range_one_certificate
#print axioms NormalNumbers.CastingOut.range_one_certificate_uniform
#print axioms NormalNumbers.CastingOut.range_two_certificate
#print axioms NormalNumbers.CastingOut.nonPretentious_zOm
#print axioms NormalNumbers.CastingOut.rung_two_of_named_inputs
