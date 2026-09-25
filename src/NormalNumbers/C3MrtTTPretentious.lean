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
/-- The reciprocal mass of the primes `≤ Y` that resonate with the twist `z·p^{−it}` to within
a window half-width `δ`, i.e. those with `|arg(z p^{−it})| < δ`.

The half-width is a free parameter, not `resEps z`: the certificate needs
`(1 − cos δ)(1 − O(δ/π)) > 0`, and the covering that proves the mass bound can lose a factor
`2` in the `δ/π`, which is fatal at `δ = π/2` (i.e. `z = −1`) but harmless at any `δ ≤ 1/4`. -/
noncomputable def resonantMass (z : ℂ) (t : ℝ) (Y : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ (Erdos67b.primesUpTo Y).filter (fun p => |(primePhase z t p).arg| < δ), (p : ℝ)⁻¹

/-- Off a window of half-width `δ ≤ π` the full `1 − cos δ` is collected.  (`δ = resEps z` is
`one_sub_re_primePhase_ge`.) -/
theorem one_sub_re_primePhase_ge_width {z : ℂ} (hz : ‖z‖ = 1) {p : ℕ} (hp : 0 < p) {t δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδπ : δ ≤ π) (hgood : δ ≤ |(primePhase z t p).arg|) :
    1 - Real.cos δ ≤ 1 - (primePhase z t p).re := by
  have hre : (primePhase z t p).re = Real.cos ((primePhase z t p).arg) := by
    rw [Complex.cos_arg (primePhase_ne_zero hz hp t), norm_primePhase hz hp t, div_one]
  have hcos : Real.cos |(primePhase z t p).arg| ≤ Real.cos δ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hδ0 (Complex.abs_arg_le_pi _) hgood
  rw [Real.cos_abs] at hcos
  rw [hre]
  linarith

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
theorem ttPretentiousSum_ge {z : ℂ} (hz : ‖z‖ = 1) (X t : ℝ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδπ : δ ≤ π) :
    (1 - Real.cos δ)
        * (Erdos67b.PrimeEstimates.primeReciprocals ⌈X ^ 2⌉₊ - resonantMass z t ⌈X ^ 2⌉₊ δ)
      ≤ ttPretentiousSum (zOmegaNat z) X t := by
  classical
  set Y : ℕ := ⌈X ^ 2⌉₊ with hY
  set P : Finset ℕ := Erdos67b.primesUpTo Y with hP
  set res : ℕ → Prop := fun p => |(primePhase z t p).arg| < δ with hres
  have hmass : Erdos67b.PrimeEstimates.primeReciprocals Y = ∑ p ∈ P, (p : ℝ)⁻¹ := by
    rw [hP, primesUpTo_eq_primesLE]
    rfl
  have hsplit : ∑ p ∈ P.filter res, (p : ℝ)⁻¹ + ∑ p ∈ P.filter (fun p => ¬ res p), (p : ℝ)⁻¹
      = ∑ p ∈ P, (p : ℝ)⁻¹ := Finset.sum_filter_add_sum_filter_not P _ _
  have hgood : (1 - Real.cos δ) * ∑ p ∈ P.filter (fun p => ¬ res p), (p : ℝ)⁻¹
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
      (one_sub_re_primePhase_ge_width hz hpp.pos hδ0 hδπ (not_lt.1 hpg)) (by positivity)
  have hrm : resonantMass z t Y δ = ∑ p ∈ P.filter res, (p : ℝ)⁻¹ := rfl
  rw [hmass, hrm]
  calc (1 - Real.cos δ)
        * ((∑ p ∈ P, (p : ℝ)⁻¹) - ∑ p ∈ P.filter res, (p : ℝ)⁻¹)
      = (1 - Real.cos δ) * ∑ p ∈ P.filter (fun p => ¬ res p), (p : ℝ)⁻¹ := by
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
  ∀ (z : ℂ) (δ : ℝ), ‖z‖ = 1 → 0 < δ → δ ≤ resEps z → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : ℝ) (Y : ℕ), 2 ≤ Y →
      resonantMass z t Y δ
        ≤ 100 * δ * (Real.log (Real.log Y) + Real.log (2 + |t|)) + C

/-! ## The payoff -/

/-- The exponent the certificate supports: `κ(z) = (1 − cos ε)(1 − (126/125)(ε/π))`, with
`ε = |arg z|/2 ∈ (0, π/2]`.  Positive exactly when `z ≠ 1`. -/
noncomputable def ttEps (z : ℂ) : ℝ := min (resEps z) (1 / 256)

theorem ttEps_pos {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) : 0 < ttEps z :=
  lt_min (resEps_pos hz hz1) (by norm_num)

theorem ttEps_le {z : ℂ} : ttEps z ≤ resEps z := min_le_left _ _

theorem ttEps_le_quarter {z : ℂ} : ttEps z ≤ 1 / 256 := min_le_right _ _

noncomputable def ttExponent (z : ℂ) : ℝ :=
  (1 - Real.cos (ttEps z)) * (1 - (126 / 125) * (100 * ttEps z))

theorem ttExponent_pos {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) : 0 < ttExponent z := by
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hq : ttEps z ≤ 1 / 256 := ttEps_le_quarter
  have hp0 : 0 < ttEps z := ttEps_pos hz hz1
  have h1 : 0 < 1 - Real.cos (ttEps z) := by
    have h : Real.cos (ttEps z) < Real.cos 0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) hp0
    rw [Real.cos_zero] at h; linarith
  have : 0 < 1 - (126 / 125 : ℝ) * (100 * ttEps z) := by nlinarith
  exact mul_pos h1 this

/-- **The archimedean lower bound, extracted** (lap 104).  The *content* of the resonance
certificate: for a unimodular `z ≠ 1` the pretentious sum exceeds `κ(z) log log X` up to an
absolute constant, uniformly over the narrow twist range `|t| ≤ (log X)^{1/125}`.

This is the reusable form.  `ttNonPretentious_of_uniformResonantMass` is the (now vacuous, lap
102) TT (3.3) corollary; `C3MrtArchFaithful.narrowTwistSmall_of_uniformResonantMass` is the
faithful consumer, which needs the bound and not the corollary. -/
theorem ttPretentiousSum_lower_of_uniformResonantMass (hURM : UniformResonantMass)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ X : ℝ, 3 ≤ X → ∀ t : ℝ, |t| ≤ Real.log X ^ ((1 : ℝ) / 125) →
      ttExponent z * Real.log (Real.log X) - C₁ ≤ ttPretentiousSum (zOmegaNat z) X t := by
  set ε := ttEps z with hε
  have hε0 : 0 < ε := ttEps_pos hz hz1
  have hq : ε ≤ 1 / 256 := ttEps_le_quarter
  obtain ⟨C, hC0, hC⟩ := hURM z ε hz hε0 ttEps_le
  have hpi3 : (3 : ℝ) < π := Real.pi_gt_three
  have hpi : (0 : ℝ) < π := by linarith
  have hεπ' : 100 * ε ≤ 1 / 2 := by linarith
  have hcos : 0 < 1 - Real.cos ε := by
    have h : Real.cos ε < Real.cos 0 :=
      Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) hε0
    rw [Real.cos_zero] at h; linarith
  set C₁ : ℝ := (1 - Real.cos ε)
      * (C + Erdos67b.PrimeEstimates.mertensBound + (100 * ε) * Real.log 4) with hC₁
  have hmert0 : 0 ≤ Erdos67b.PrimeEstimates.mertensBound :=
    Erdos67b.PrimeEstimates.mertensBound_nonneg
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨C₁, by rw [hC₁]; positivity, fun X hX t ht => ?_⟩
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
    refine le_trans ?_ (ttPretentiousSum_ge hz X t hε0.le (by linarith))
    rw [← hY]
    have hkey : ttExponent z * Real.log (Real.log X) - C₁
        ≤ (1 - Real.cos ε)
            * ((Real.log (Real.log Y) - Erdos67b.PrimeEstimates.mertensBound)
                - ((100 * ε) * (Real.log (Real.log Y) + Real.log (2 + |t|)) + C)) := by
      rw [hC₁, ttExponent, ← hε]
      have hcoef : (1 - (126/125 : ℝ) * (100 * ε)) * Real.log (Real.log X)
          ≤ (Real.log (Real.log Y) - Erdos67b.PrimeEstimates.mertensBound)
              - ((100 * ε) * (Real.log (Real.log Y) + Real.log (2 + |t|)) + C)
            + (C + Erdos67b.PrimeEstimates.mertensBound + (100 * ε) * Real.log 4) := by
        have h1 : (0 : ℝ) ≤ 1 - 100 * ε := by linarith
        have h2 : (100 * ε) * Real.log (2 + |t|)
            ≤ (100 * ε) * (Real.log 4 + (1/125) * Real.log (Real.log X)) := by
          have : (0:ℝ) ≤ 100 * ε := by positivity
          exact mul_le_mul_of_nonneg_left ht4 this
        nlinarith [mul_le_mul_of_nonneg_left hloglog h1]
      nlinarith [hcos.le]
    refine le_trans hkey (mul_le_mul_of_nonneg_left ?_ hcos.le)
    linarith [hmass, hres]
  exact hlower

/-- **TT's hypothesis (3.3), discharged for `z^ω`.**  Given the uniform resonant-mass bound, a
unimodular `z ≠ 1` is non-pretentious in Tao–Teräväinen's *old* (lap-102 vacuous) sense at every
`X ≥ 3`, for every `L` up to `(log X)^{κ(z)}`.  Kept for the ledger; the content is
`ttPretentiousSum_lower_of_uniformResonantMass`. -/
theorem ttNonPretentious_of_uniformResonantMass (hURM : UniformResonantMass)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) {κ : ℝ} (hκ : κ ≤ ttExponent z) :
    ∀ X L : ℝ, 3 ≤ X → 1 ≤ L → L ≤ Real.log X ^ κ →
      TTNonPretentious (zOmegaNat z) X L := by
  obtain ⟨C₁, hC₁0, hlow⟩ := ttPretentiousSum_lower_of_uniformResonantMass hURM hz hz1
  refine fun X L hX hL1 hLX => ⟨Real.exp (-C₁), Real.exp_pos _, fun t ht => ?_⟩
  have hlogX : (1 : ℝ) ≤ Real.log X := by
    have h1 : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) hX
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ 3 by
        nlinarith [Real.exp_one_lt_d9])
      rwa [Real.log_exp] at h
    linarith
  have hll : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hlogX
  have hLexp : L ≤ Real.exp (ttExponent z * Real.log (Real.log X)) := by
    refine le_trans hLX ?_
    rw [Real.rpow_def_of_pos (by linarith)]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hκ hll])
  calc Real.exp (-C₁) * L
      ≤ Real.exp (-C₁) * Real.exp (ttExponent z * Real.log (Real.log X)) :=
        mul_le_mul_of_nonneg_left hLexp (Real.exp_pos _).le
    _ = Real.exp (ttExponent z * Real.log (Real.log X) - C₁) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (ttPretentiousSum (zOmegaNat z) X t) :=
        Real.exp_le_exp.mpr (hlow X hX t ht)

theorem ttExponent_le_one {z : ℂ} (hz : ‖z‖ = 1) : ttExponent z ≤ 1 := by
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hε0 : 0 ≤ ttEps z := le_min (resEps_nonneg z) (by norm_num)
  have hq : ttEps z ≤ 1 / 256 := ttEps_le_quarter
  have hcos : 0 ≤ Real.cos (ttEps z) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have h2 : (0 : ℝ) ≤ (126 / 125 : ℝ) * (100 * ttEps z) := by positivity
  have h3 : Real.cos (ttEps z) ≤ 1 := Real.cos_le_one _
  rw [ttExponent]
  nlinarith

/-! ## The `D = 2` transfer, on the two named inputs -/

/-- **The `K = 2` natural-density transfer, modulo two named inputs.**  Combining lap 71's
`logToNatural_two_of_noExc` with the archimedean certificate of this file: for a unimodular
`z 0 ≠ 1`, the two-point `ζ^ω` correlation along any arithmetic progression has natural
density `0`, given

* `TwoPointNaturalCorrelationNoExc` — TT Theorem 3.1(ii) with the exceptional set of scales
  removed (the named open problem of lap 71), and
* `UniformResonantMass` — the sharp resonance-window mass bound of this file.

No other hypothesis: `z 0 ≠ 1` now supplies TT's (3.3) outright. -/
theorem logToNatural_two_of_noExc_of_ne_one (h : TwoPointNaturalCorrelationNoExc)
    (hURM : UniformResonantMass) (z : ℕ → ℂ) (hz : ∀ i, ‖z i‖ = 1) (hz0 : z 0 ≠ 1)
    {M : ℕ} (hM : 0 < M) (r : ℕ) :
    Filter.Tendsto (fun J : ℕ =>
        (∑ m ∈ Finset.range J, ∏ i : Fin 2, z i ^ omegaNat (M * m + r + (i : ℕ) + 1)) / (J : ℂ))
      Filter.atTop (nhds 0) :=
  logToNatural_two_of_noExc h z hz (ttExponent_pos (hz 0) hz0) (ttExponent_le_one (hz 0))
    (ttNonPretentious_of_uniformResonantMass hURM (hz 0) hz0 le_rfl) hM r

/-- **`LogToNaturalCorrelationNZ 2`, on the two named inputs.**  The `D = 2` barrier of
`C3MrtNatural` — in the `z 0 ≠ 1` form every consumer actually uses — now follows from TT
Theorem 3.1(ii) with the exceptional set removed, plus the uniform resonant-mass bound.

This is the wiring lap 71 left open: `depthAvg_tendsto_of_transfer_nz` consumes it directly. -/
theorem logToNaturalCorrelationNZ_two_of_noExc (h : TwoPointNaturalCorrelationNoExc)
    (hURM : UniformResonantMass) : LogToNaturalCorrelationNZ 2 :=
  fun z hz hz0 _M r hM _ => logToNatural_two_of_noExc_of_ne_one h hURM z hz hz0 hM r

/-- **The `D = 2` depth rung, natural density, on the two named inputs.**  The endpoint of the
`D = 2` layer: with `ProgressionLogRung 2` in hand (the log-averaged rung, proved on the
merely-multiplicative anchor in `C3MrtMultChase`), the twisted two-point depth average tends
to `0` — conditional on exactly the named open problem and the resonance mass bound. -/
theorem depthAvg_two_tendsto_of_named (h : TwoPointNaturalCorrelationNoExc)
    (hURM : UniformResonantMass) {b Q : ℕ} (hQ : 0 < Q) (P j : ℕ) (hh : ℤ)
    (hζ : depthRoot b hh 0 ≠ 1) (hrung : ProgressionLogRung 2) :
    Filter.Tendsto (fun N : ℕ => depthAvg b P Q j hh 2 N) Filter.atTop (nhds 0) :=
  depthAvg_tendsto_of_transfer_nz hQ P j hh hζ hrung (logToNaturalCorrelationNZ_two_of_noExc h hURM)

end CastingOut

end NormalNumbers
