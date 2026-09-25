/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtNoExc
import NormalNumbers.C3MrtArchimedean

/-!
# Discharging `TTNonPretentious (zOmegaNat z)` — the archimedean certificate on TT's scale

`logToNatural_two_of_noExc` (lap 71) carries one hypothesis not yet supplied from the repo's
own inputs: TT's non-pretentiousness condition (3.3),

    `A · L ≤ exp (ttPretentiousSum (zOmegaNat z) X t)`   for all `|t| ≤ (log X)^{1/125}`.

## The correction this file forces (lap 72)

The lap-71 `NEXT` list asked for this with `1 ≤ L ≤ log X`, matching TT's own admissible range.
**That form is false**, and the reason is quantitative, not technical.  Writing `z = e^{iθ}`,

    `ttPretentiousSum (z^ω) X t = ∑_{p ≤ X²} (1 − cos(θ − t log p))/p`,

and at `t = 0` this is exactly `(1 − cos θ)·(log log X + O(1))`, so

    `exp(ttPretentiousSum) ≍ (log X)^{1 − cos θ}`.

For `θ` small `1 − cos θ < 1`, so `A·L ≤ exp(…)` **fails** for `L` as large as `log X`.  The
`L` that a unimodular `z ≠ 1` can support is a **small power of `log X`**, with exponent
`κ(z) > 0` and no more.  This is not a defect of the route: `L → ∞` is all the assembly needs
(the saving is `L^{-c}`, and `dyadic_window_bound_of_noExc` only ever uses `L = L(N) → ∞`),
so the fix is to carry `L ≤ (log X)^κ` through the chain — see `C3MrtNoExc`, whose `hnp`
hypotheses were weakened to this form in the same lap.

## What is proved here

* `ttPretentiousSum_eq_primes` / `ttPretentiousSum_ge` — TT's sum is the `q = 1` archimedean
  pretentious distance of `C3MrtArchimedean`, so the resonance machinery of laps 18–21 applies
  verbatim: off a resonance window of half-width `ε = |arg z|/2`, every prime contributes
  `(1 − cos ε)/p`.
* `UniformResonantMass` — **the one named analytic input**, and the only thing between this
  file and an unconditional `TTNonPretentious`.  It asks that the resonant primes carry
  reciprocal mass at most `(ε/π)(log log Y + log(2+|t|)) + O(1)`, uniformly in `t`.  This is
  the exact heuristic value: the resonance windows `|t| log p ∈ (γ_m − ε, γ_m + ε)`,
  `γ_m = |arg z − 2πm| ≈ 2πm`, have `log log`-lengths `≈ 2ε/γ_m`, and `∑_{m ≤ K} 2ε/(2πm) ≈
  (ε/π) log K` with `K ≈ |t| log Y`.
* `ttNonPretentious_of_uniformResonantMass` — the payoff: for `‖z‖ = 1`, `z ≠ 1` there is
  `κ(z) > 0` with `TTNonPretentious (zOmegaNat z) X L` for every `X ≥ 3` and `1 ≤ L ≤
  (log X)^κ`.  Explicitly `κ = (1 − cos ε)(1 − (126/125)(ε/π))`, positive because `ε ≤ π/2`.

## Why the existing Range-1/Range-2 split is not enough, and why `TwistedPrimeSumSaving` is not
what is missing

`resonant_mass_le` bounds the resonant mass by `(2·windowCount T z + 1)·windowMassBound` with
`windowCount T z ≈ T/2π`, which is `X`-independent only when `|t| log p ≤ T` for a FIXED `T`,
i.e. `|t| ≲ T/log X`.  TT need `|t|` up to `(log X)^{1/125}`, where the number of windows is
`≈ |t| log X`; the uniform per-window bound `windowMassBound` is then far too lossy.  The
missing ingredient is the *sharp* per-window mass `log((γ+ε)/(γ−ε)) ≈ 2ε/γ`, which needs a
Mertens estimate with a decaying error, or Brun–Titchmarsh — not a zero-free region.  In
particular `TwistedPrimeSumSaving` (Vinogradov–Korobov) is **not** the missing input here, and
is not attacked: the saving it provides is a constant, whereas TT's `L → ∞` needs a saving
growing like `κ log log X`.
-/

open Finset Real

namespace NormalNumbers

namespace CastingOut

open scoped Classical in
/-- The reciprocal mass of the primes `≤ Y` that resonate with the twist `z·p^{−it}`, i.e.
those with `|arg(z p^{−it})| < ε = |arg z|/2`. -/
noncomputable def resonantMass (z : ℂ) (t : ℝ) (Y : ℕ) : ℝ :=
  ∑ p ∈ (Erdos67b.primesUpTo Y).filter (fun p => |(primePhase z t p).arg| < resEps z),
    (p : ℝ)⁻¹

/-! ## TT's sum is the archimedean pretentious distance -/

/-- On a prime, `z^ω` takes the constant value `z`. -/
theorem zOmegaNat_prime {z : ℂ} {p : ℕ} (hp : p.Prime) : zOmegaNat z p = z := by
  rw [zOmegaNat_apply, show p = p ^ 1 by ring, omegaNat_prime_pow hp le_rfl, pow_one]

/-- The summand of `ttPretentiousSum` at a prime is the archimedean phase term. -/
theorem ttPretentiousSum_term (z : ℂ) {p : ℕ} (hp : p.Prime) (t : ℝ) :
    (1 - (zOmegaNat z p * Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ))).re) / (p : ℝ)
      = (1 - (primePhase z t p).re) / (p : ℝ) := by
  congr 2
  rw [zOmegaNat_prime hp, primePhase, archPhase_eq_exp hp.pos]
  congr 2
  push_cast
  ring

/-- **TT's pretentious sum, over the primes.** -/
theorem ttPretentiousSum_eq_primes (z : ℂ) (X t : ℝ) :
    ttPretentiousSum (zOmegaNat z) X t
      = ∑ p ∈ Erdos67b.primesUpTo ⌈X ^ 2⌉₊, (1 - (primePhase z t p).re) / (p : ℝ) := by
  rw [ttPretentiousSum, Erdos67b.primesUpTo]
  refine Finset.sum_congr rfl fun p hp => ?_
  exact ttPretentiousSum_term z (Finset.mem_filter.1 hp).2 t

/-- Every summand is nonnegative. -/
theorem ttPretentiousTerm_nonneg {z : ℂ} (hz : ‖z‖ = 1) {p : ℕ} (hp : p.Prime) (t : ℝ) :
    0 ≤ (1 - (primePhase z t p).re) / (p : ℝ) := by
  have h : (primePhase z t p).re ≤ 1 := by
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_primePhase hz hp.pos t]
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  positivity

/-- **The good primes deliver**, on TT's index set: the pretentious sum is at least
`(1 − cos ε)` times the non-resonant prime mass. -/
theorem ttPretentiousSum_ge {z : ℂ} (hz : ‖z‖ = 1) (X t : ℝ) :
    (1 - Real.cos (resEps z))
        * (Erdos67b.PrimeEstimates.primeReciprocals ⌈X ^ 2⌉₊ - resonantMass z t ⌈X ^ 2⌉₊)
      ≤ ttPretentiousSum (zOmegaNat z) X t := by
  classical
  set Y : ℕ := ⌈X ^ 2⌉₊ with hY
  set P : Finset ℕ := Erdos67b.primesUpTo Y with hP
  set res : ℕ → Prop := fun p => |(primePhase z t p).arg| < resEps z with hres
  have hmass : Erdos67b.PrimeEstimates.primeReciprocals Y = ∑ p ∈ P, (p : ℝ)⁻¹ := by
    rw [hP, primesUpTo_eq_primesLE]
    rfl
  have hsplit : ∑ p ∈ P.filter res, (p : ℝ)⁻¹ + ∑ p ∈ P.filter (fun p => ¬ res p), (p : ℝ)⁻¹
      = ∑ p ∈ P, (p : ℝ)⁻¹ := Finset.sum_filter_add_sum_filter_not P _ _
  have hgood : (1 - Real.cos (resEps z)) * ∑ p ∈ P.filter (fun p => ¬ res p), (p : ℝ)⁻¹
      ≤ ttPretentiousSum (zOmegaNat z) X t := by
    rw [ttPretentiousSum_eq_primes z X t, ← hP, Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum (g := fun p => (1 - (primePhase z t p).re) / (p : ℝ))
        ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p hp _ => ttPretentiousTerm_nonneg hz (Erdos67b.mem_primesUpTo.1 hp).1 t))
    intro p hp
    obtain ⟨hpP, hpg⟩ := Finset.mem_filter.1 hp
    have hpp : p.Prime := (Erdos67b.mem_primesUpTo.1 hpP).1
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (one_sub_re_primePhase_ge hz hpp.pos (not_lt.1 hpg)) (by positivity)
  have hrm : resonantMass z t Y = ∑ p ∈ P.filter res, (p : ℝ)⁻¹ := rfl
  rw [hmass, hrm]
  calc (1 - Real.cos (resEps z))
        * ((∑ p ∈ P, (p : ℝ)⁻¹) - ∑ p ∈ P.filter res, (p : ℝ)⁻¹)
      = (1 - Real.cos (resEps z)) * ∑ p ∈ P.filter (fun p => ¬ res p), (p : ℝ)⁻¹ := by
        rw [← hsplit]; ring
    _ ≤ ttPretentiousSum (zOmegaNat z) X t := hgood

/-! ## The named analytic input -/

/-- **The uniform resonant-mass bound** — the one analytic input of this file.

For a unimodular `z ≠ 1` with `ε = |arg z|/2`, the primes `p ≤ Y` whose twist `z p^{−it}` lies
within `ε` of `1` carry reciprocal mass at most `(ε/π)(log log Y + log(2+|t|)) + O_z(1)`,
uniformly in `t`.

This is the sharp form of `resonant_mass_le`: the resonance windows are
`|t| log p ∈ (γ_m − ε, γ_m + ε)` with `γ_m = |arg z − 2πm| ≥ 2ε`, of `log log`-length
`log((γ_m+ε)/(γ_m−ε)) ≤ 2ε/(γ_m − ε)`, and `γ_m ≥ 2π|m| − π`, so the total is
`≤ ε/π · log K + O(1)` with `K ≈ |t| log Y / 2π` the number of windows meeting `[2, Y]`.
`resonant_mass_le` proves exactly this with the lossy per-window bound `windowMassBound` in
place of `2ε/(γ_m − ε)`, which suffices only for `O(1)` windows. -/
def UniformResonantMass : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → z ≠ 1 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (Y : ℕ), 2 ≤ Y →
    resonantMass z t Y
      ≤ (resEps z / π) * (Real.log (Real.log Y) + Real.log (2 + |t|)) + C

/-! ## The payoff -/

/-- The exponent the certificate supports: `κ(z) = (1 − cos ε)(1 − (126/125)(ε/π))`, with
`ε = |arg z|/2 ∈ (0, π/2]`.  Positive exactly when `z ≠ 1`. -/
noncomputable def ttExponent (z : ℂ) : ℝ :=
  (1 - Real.cos (resEps z)) * (1 - (126 / 125) * (resEps z / π))

theorem ttExponent_pos {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) : 0 < ttExponent z := by
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have h1 : 0 < 1 - Real.cos (resEps z) := one_sub_cos_resEps_pos hz hz1
  have h2 : resEps z ≤ π / 2 := resEps_le_pi_div_two z
  have h3 : resEps z / π ≤ 1 / 2 := by
    rw [div_le_iff₀ hpi]
    linarith
  have : 0 < 1 - (126 / 125 : ℝ) * (resEps z / π) := by nlinarith
  exact mul_pos h1 this

/-- **TT's hypothesis (3.3), discharged for `z^ω`.**  Given the uniform resonant-mass bound,
a unimodular `z ≠ 1` is non-pretentious in Tao–Teräväinen's sense at every `X ≥ 3`, for every
`L` up to the power `(log X)^{κ(z)}`. -/
theorem ttNonPretentious_of_uniformResonantMass (hURM : UniformResonantMass)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) {κ : ℝ} (hκ : κ ≤ ttExponent z) :
    ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat z) X L := by
  obtain ⟨C, hC0, hC⟩ := hURM z hz hz1
  set ε := resEps z with hε
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hε0 : 0 < ε := resEps_pos hz hz1
  have hεπ : ε ≤ π / 2 := resEps_le_pi_div_two z
  have hεπ' : ε / π ≤ 1 / 2 := by
    rw [div_le_iff₀ hpi]; linarith
  have hcos : 0 < 1 - Real.cos ε := one_sub_cos_resEps_pos hz hz1
  set C₁ : ℝ := (1 - Real.cos ε)
      * (C + Erdos67b.PrimeEstimates.mertensBound + (ε / π) * Real.log 4) with hC₁
  refine fun X L hX hL1 hLX => ⟨Real.exp (-C₁), Real.exp_pos _, fun t ht => ?_⟩
  -- basic size facts
  have hX0 : (0 : ℝ) < X := by linarith
  have hlogX : (1 : ℝ) ≤ Real.log X := by
    have : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) hX
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      have := Real.add_one_le_exp (1 : ℝ)
      nlinarith [Real.exp_one_lt_d9, Real.log_le_log (by positivity : (0:ℝ) < Real.exp 1)
        (le_of_lt (by nlinarith [Real.exp_one_lt_d9] : Real.exp 1 < 3)), Real.log_exp (1:ℝ)]
    linarith
  set Y : ℕ := ⌈X ^ 2⌉₊ with hY
  have hXY : X ^ 2 ≤ (Y : ℝ) := Nat.le_ceil _
  have hY2 : 2 ≤ Y := by
    have : (2 : ℝ) ≤ X ^ 2 := by nlinarith
    have : (2 : ℝ) ≤ (Y : ℝ) := le_trans this hXY
    exact_mod_cast this
  have hYpos : (0 : ℝ) < (Y : ℝ) := by positivity
  have hlogY : 2 * Real.log X ≤ Real.log Y := by
    have := Real.log_le_log (by positivity) hXY
    rwa [Real.log_pow] at this
    
  have hlogYpos : (0 : ℝ) < Real.log Y := by linarith
  have hloglog : Real.log (Real.log X) ≤ Real.log (Real.log Y) := by
    refine Real.log_le_log (by linarith) (by linarith)
  have hllX : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hlogX
  -- the `t` range
  have ht4 : Real.log (2 + |t|) ≤ Real.log 4 + (1 / 125) * Real.log (Real.log X) := by
    have hexp : Real.log X ^ ((1:ℝ)/125) = Real.exp ((1/125) * Real.log (Real.log X)) := by
      rw [Real.rpow_def_of_pos (by linarith)]; ring_nf
    have hu1 : (1 : ℝ) ≤ Real.log X ^ ((1:ℝ)/125) := Real.one_le_rpow hlogX (by norm_num)
    have h24 : 2 + |t| ≤ 4 * Real.log X ^ ((1:ℝ)/125) := by linarith
    calc Real.log (2 + |t|) ≤ Real.log (4 * Real.log X ^ ((1:ℝ)/125)) :=
          Real.log_le_log (by positivity) h24
      _ = Real.log 4 + (1/125) * Real.log (Real.log X) := by
          rw [Real.log_mul (by norm_num) (by positivity), hexp, Real.log_exp]
  -- the resonance bound
  have hres := hC t Y hY2
  have hmass : Real.log (Real.log Y) - Erdos67b.PrimeEstimates.mertensBound
      ≤ Erdos67b.PrimeEstimates.primeReciprocals Y := by
    have := Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le hY2
    have := abs_le.1 this
    linarith [this.1]
  have hlower : ttExponent z * Real.log (Real.log X) - C₁
      ≤ ttPretentiousSum (zOmegaNat z) X t := by
    refine le_trans ?_ (ttPretentiousSum_ge hz X t)
    rw [← hε, ← hY]
    have hkey : ttExponent z * Real.log (Real.log X) - C₁
        ≤ (1 - Real.cos ε)
            * ((Real.log (Real.log Y) - Erdos67b.PrimeEstimates.mertensBound)
                - ((ε / π) * (Real.log (Real.log Y) + Real.log (2 + |t|)) + C)) := by
      rw [hC₁, ttExponent, ← hε]
      have hcoef : (1 - (126/125 : ℝ) * (ε / π)) * Real.log (Real.log X)
          ≤ (Real.log (Real.log Y) - Erdos67b.PrimeEstimates.mertensBound)
              - ((ε / π) * (Real.log (Real.log Y) + Real.log (2 + |t|)) + C)
            + (C + Erdos67b.PrimeEstimates.mertensBound + (ε / π) * Real.log 4) := by
        have h1 : (0 : ℝ) ≤ 1 - ε / π := by linarith
        have h2 : (ε / π) * Real.log (2 + |t|)
            ≤ (ε / π) * (Real.log 4 + (1/125) * Real.log (Real.log X)) := by
          have : (0:ℝ) ≤ ε / π := by positivity
          exact mul_le_mul_of_nonneg_left ht4 this
        nlinarith [mul_le_mul_of_nonneg_left hloglog h1]
      nlinarith [hcos.le]
    refine le_trans hkey (mul_le_mul_of_nonneg_left ?_ hcos.le)
    linarith [hmass, hres]
  -- exponentiate
  have hfinal : Real.exp (-C₁) * L ≤ Real.exp (ttPretentiousSum (zOmegaNat z) X t) := by
    refine le_trans ?_ (Real.exp_le_exp.2 hlower)
    rw [Real.exp_sub, mul_comm]
    have hLle : L ≤ Real.exp (ttExponent z * Real.log (Real.log X)) := by
      refine le_trans hLX ?_
      rw [Real.rpow_def_of_pos (by linarith)]
      exact Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right hκ hllX])
    have : (0:ℝ) < Real.exp C₁ := Real.exp_pos _
    rw [div_eq_mul_inv, ← Real.exp_neg] at *
    nlinarith [Real.exp_pos (-C₁), hLle]
  exact hfinal

end CastingOut

end NormalNumbers
