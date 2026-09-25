/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.C3MrtFaithfulInput

/-!
# The faithful archimedean supply, decomposed

Lap 103 reduced the C3/MRT headline to two faithful inputs, `KPointNoExcAtWith A` and
`ArchSupply (TTNonPretentiousAt A) b`.  This file attacks the second one.

## The structural finding

For `g = zOmegaNat z` with `‖z‖ = 1` the faithful pretentious sum splits **exactly**:

    ttPretentiousSumChar (zOmegaNat z) X χ t
      = ∑_{p ≤ X²} 1/p − Re( z · ∑_{p ≤ X²} conj(χ(p)) p^{-it} / p )
      ≥ (log log X² − mertensBound) − ‖twistedPrimeSum X χ t‖         (`ttPretentiousSumChar_ge`)

so the whole obligation is a bound `‖twistedPrimeSum‖ ≤ (1 − κ) log log X + O(1)`, uniformly over
Dirichlet characters of modulus `q ≤ (log X)^{1/125}` and twists `|t| ≤ X²`.

**And it must be proved in two genuinely different ranges.**  The resonance machinery of
`C3MrtTTPretentious` (`UniformResonantMass` → `ttNonPretentious_of_uniformResonantMass`) bounds
the resonant mass by `(ε/π)(log log Y + log(2+|t|)) + O(1)`; the `log(2+|t|)` term is harmless
only while `|t| ≤ (log X)^{1/125}` (that is exactly where `ht4` is used there).  At `|t|` up to
`X²` it is `≍ log X`, which swamps `log log X`: **the resonance route cannot cover the wide
range.**  The wide range instead wants the *smallness* of the twisted prime sum
`∑_{p ≤ Y} conj(χ(p)) p^{-it}/p = O(1)` for `|t|` large, i.e. a prime-number-theorem input for
`L(s, χ)` with a zero-free region (Vinogradov–Korobov territory), not a resonance count.

That is the decomposition recorded below: `NarrowTwistLower` (the resonance range, already
essentially available) + `WideTwistSmall` (the new analytic debt) ⇒ `FaithfulArchLower` ⇒
`ArchSupply (TTNonPretentiousAt (exp (−C))) b` ⇒ `ConjC3` on faithful inputs.
-/

open Filter Topology Finset

namespace NormalNumbers

namespace CastingOut

/-- The twisted prime sum `∑_{p ≤ X²} conj(χ(p)) p^{-it} / p`, the only thing standing between
the faithful pretentious sum and Mertens. -/
noncomputable def twistedPrimeSum (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ p ∈ (Finset.range (⌈X ^ 2⌉₊ + 1)).filter Nat.Prime,
    (starRingEnd ℂ) (χ (p : ZMod q)) *
      Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ)) / (p : ℂ)

/-- **The exact split.**  For a unimodular `z`, the faithful pretentious sum is the prime
reciprocal mass minus the real part of `z` times the twisted prime sum. -/
theorem ttPretentiousSumChar_eq {z : ℂ} (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ttPretentiousSumChar (zOmegaNat z) X χ t
      = (∑ p ∈ (Finset.range (⌈X ^ 2⌉₊ + 1)).filter Nat.Prime, ((p : ℝ))⁻¹)
        - (z * twistedPrimeSum X χ t).re := by
  classical
  rw [ttPretentiousSumChar, twistedPrimeSum, Finset.mul_sum, Complex.re_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hpz : ((p : ℂ)) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr hpp.pos.ne'
  rw [zOmegaNat_prime hpp]
  have hre : (z * ((starRingEnd ℂ) (χ (p : ZMod q)) *
        Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ)) / (p : ℂ))).re
      = (z * (starRingEnd ℂ) (χ (p : ZMod q)) *
          Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ))).re / (p : ℝ) := by
    rw [mul_div_assoc']
    rw [show ((p : ℂ)) = ((p : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.div_ofReal_re]
    ring_nf
  rw [hre, sub_div]
  ring_nf

/-- **The obligation, isolated.**  Everything above `Real.log (Real.log (X²))` is Mertens; the
open part is the size of `Re(z · twistedPrimeSum)`.

The `Re` is essential and the naive `‖twistedPrimeSum‖` form is FALSE: at `t = 0`, `χ = 1` the
twisted sum *is* the full mass `∑_{p≤X²} 1/p ≈ log log X`, and what makes the pretentious sum
large there is not its size but its *direction* — `z` is bounded away from `1`.  That is exactly
the resonance mechanism of `C3MrtTTPretentious`, and it is why the narrow range must be stated
with `Re` (`NarrowTwistSmall`) while the wide range may be stated with the norm
(`WideTwistSmall`, converted by `re_le_norm`). -/
theorem ttPretentiousSumChar_ge {z : ℂ} {X : ℝ} (hX : 3 ≤ X) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    Real.log (Real.log (⌈X ^ 2⌉₊ : ℝ)) - Erdos67b.PrimeEstimates.mertensBound
        - (z * twistedPrimeSum X χ t).re
      ≤ ttPretentiousSumChar (zOmegaNat z) X χ t := by
  classical
  set Y : ℕ := ⌈X ^ 2⌉₊ with hY
  have hXY : X ^ 2 ≤ (Y : ℝ) := Nat.le_ceil _
  have hY2 : 2 ≤ Y := by
    have h1 : (2 : ℝ) ≤ X ^ 2 := by nlinarith
    have : (2 : ℝ) ≤ (Y : ℝ) := le_trans h1 hXY
    exact_mod_cast this
  have hmass : Real.log (Real.log (Y : ℝ)) - Erdos67b.PrimeEstimates.mertensBound
      ≤ ∑ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, ((p : ℝ))⁻¹ := by
    have h := abs_le.1 (Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le hY2)
    have hrw : Erdos67b.PrimeEstimates.primeReciprocals Y
        = ∑ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, ((p : ℝ))⁻¹ := by
      rfl
    rw [← hrw]
    linarith [h.1]
  rw [ttPretentiousSumChar_eq X χ t]
  linarith

/-! ## The two ranges, named -/

/-- **The whole faithful archimedean obligation, in one line.**  A lower bound
`κ · log log X − C` on the faithful pretentious sum of `zOmegaNat (depthRoot b h' 0)`, uniform
over the characters and twists TT quantify over.  `C` must not depend on `h'` (the implied
constant `A = exp(−C)` of TT (3.3) is absolute); `κ` may. -/
def FaithfulArchLower (b : ℕ) (C : ℝ) : Prop :=
  ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') → ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧
    ∀ X : ℝ, 3 ≤ X → ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      (q : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) → ∀ t : ℝ, |t| ≤ X ^ 2 →
        κ * Real.log (Real.log X) - C
          ≤ ttPretentiousSumChar (zOmegaNat (depthRoot b h' 0)) X χ t

/-- The exponentiation step, once: a `κ log log X − C` lower bound on the faithful pretentious
sum is TT (3.3) with the absolute constant `A = exp(−C)`. -/
theorem ttNonPretentiousAt_of_lower {z : ℂ} {C κ : ℝ} (_hκ : 0 < κ)
    (hlow : ∀ X : ℝ, 3 ≤ X → ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      (q : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) → ∀ t : ℝ, |t| ≤ X ^ 2 →
        κ * Real.log (Real.log X) - C ≤ ttPretentiousSumChar (zOmegaNat z) X χ t)
    {X L : ℝ} (hX : 3 ≤ X) (_hL1 : 1 ≤ L) (hLX : L ≤ Real.log X ^ κ) :
    TTNonPretentiousAt (Real.exp (-C)) (zOmegaNat z) X L := by
  intro q χ hq t ht
  have hlogX : (1 : ℝ) ≤ Real.log X := by
    have h3 : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) hX
    have : (1 : ℝ) ≤ Real.log 3 := by
      have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ 3 by
        nlinarith [Real.exp_one_lt_d9])
      rwa [Real.log_exp] at h
    linarith
  have hll : (0 : ℝ) ≤ Real.log (Real.log X) := Real.log_nonneg hlogX
  have hLexp : L ≤ Real.exp (κ * Real.log (Real.log X)) := by
    refine le_trans hLX ?_
    rw [Real.rpow_def_of_pos (by linarith)]
    exact le_of_eq (by ring_nf)
  have hlow' := hlow X hX q χ hq t ht
  calc Real.exp (-C) * L
      ≤ Real.exp (-C) * Real.exp (κ * Real.log (Real.log X)) :=
        mul_le_mul_of_nonneg_left hLexp (Real.exp_pos _).le
    _ = Real.exp (κ * Real.log (Real.log X) - C) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (ttPretentiousSumChar (zOmegaNat z) X χ t) := Real.exp_le_exp.mpr hlow'

/-- **The faithful archimedean supply from the lower bound.** -/
theorem archSupply_of_faithfulArchLower {b : ℕ} {C : ℝ} (h : FaithfulArchLower b C) :
    ArchSupply (TTNonPretentiousAt (Real.exp (-C))) b := by
  intro h' hnd
  obtain ⟨κ, hκ, hκ1, hlow⟩ := h h' hnd
  exact ⟨κ, hκ, hκ1, fun X L hX hL1 hLX => ttNonPretentiousAt_of_lower hκ hlow hX hL1 hLX⟩

/-- **`ConjC3` from the faithful correlation input and the faithful archimedean lower bound.**
The headline with both inputs in their honest, non-vacuous form. -/
theorem conjC3_of_geom_input_lower {C c₀ θ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1)
    (m : ℕ)
    (hin : ∀ b : ℕ, 3 ≤ b → ∀ K,
      KPointNoExcAtWith (Real.exp (-C)) (cKgeom c₀ θ b) (CstKdeg m) K)
    (hlow : ∀ b : ℕ, 3 ≤ b → FaithfulArchLower b C) :
    ConjC3 :=
  conjC3_of_geom_input_at hc₀ hθ0 hθ m hin
    fun b hb => archSupply_of_faithfulArchLower (hlow b hb)

/-! ### The split of `FaithfulArchLower` into the two twist ranges -/

/-- **The narrow range** `|t| ≤ (log X)^{1/125}`: the resonance range, where the mechanism of
`C3MrtTTPretentious` applies (its `log(2 + |t|)` loss is affordable there).  Stated for the
twisted prime sum, so that it composes with `ttPretentiousSumChar_ge`. -/
def NarrowTwistSmall (z : ℂ) (κ C : ℝ) : Prop :=
  ∀ X : ℝ, 3 ≤ X → ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
    (q : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) →
    ∀ t : ℝ, |t| ≤ Real.log X ^ ((1 : ℝ) / 125) →
      (z * twistedPrimeSum X χ t).re ≤ (1 - κ) * Real.log (Real.log X) + C

/-- **The wide range** `(log X)^{1/125} < |t| ≤ X²`: here the twisted prime sum is small for a
different reason — cancellation in `∑_{p ≤ Y} conj(χ(p)) p^{-it}/p`, i.e. a zero-free region for
`L(s, χ)`.  This is the new analytic debt created by stating TT (3.3) faithfully; the resonance
count provably cannot supply it (module doc-comment). -/
def WideTwistSmall (κ C : ℝ) : Prop :=
  ∀ X : ℝ, 3 ≤ X → ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
    (q : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) →
    ∀ t : ℝ, Real.log X ^ ((1 : ℝ) / 125) < |t| → |t| ≤ X ^ 2 →
      ‖twistedPrimeSum X χ t‖ ≤ (1 - κ) * Real.log (Real.log X) + C

/-- **The split, assembled.**  Both ranges give the same shape of bound on the twisted prime
sum, and `ttPretentiousSumChar_ge` converts it into `FaithfulArchLower` — using
`log log X² ≥ log log X`. -/
theorem faithfulArchLower_of_twist_small {b : ℕ} {κ C : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hnar : ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') → NarrowTwistSmall (depthRoot b h' 0) κ C)
    (hwide : WideTwistSmall κ C) :
    FaithfulArchLower b (C + Erdos67b.PrimeEstimates.mertensBound) := by
  intro h' hnd
  refine ⟨κ, hκ, hκ1, fun X hX q χ hq t ht => ?_⟩
  have hz : ‖depthRoot b h' 0‖ = 1 := norm_ee_real _
  have hlogX : (1 : ℝ) ≤ Real.log X := by
    have h3 : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) hX
    have : (1 : ℝ) ≤ Real.log 3 := by
      have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ 3 by
        nlinarith [Real.exp_one_lt_d9])
      rwa [Real.log_exp] at h
    linarith
  have hXY : X ^ 2 ≤ ((⌈X ^ 2⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hllmono : Real.log (Real.log X) ≤ Real.log (Real.log ((⌈X ^ 2⌉₊ : ℕ) : ℝ)) := by
    have h1 : Real.log X ≤ Real.log ((⌈X ^ 2⌉₊ : ℕ) : ℝ) := by
      refine Real.log_le_log (by linarith) ?_
      nlinarith
    exact Real.log_le_log (by linarith) h1
  have hts : (depthRoot b h' 0 * twistedPrimeSum X χ t).re
      ≤ (1 - κ) * Real.log (Real.log X) + C := by
    rcases le_or_gt |t| (Real.log X ^ ((1 : ℝ) / 125)) with hnar' | hwide'
    · exact hnar h' hnd X hX q χ hq t hnar'
    · refine le_trans ?_ (hwide X hX q χ hq t hwide' ht)
      refine le_trans (Complex.re_le_norm _) ?_
      rw [norm_mul, hz, one_mul]
  have hkey := ttPretentiousSumChar_ge (z := depthRoot b h' 0) hX χ t
  nlinarith [hkey, hts, hllmono]

#print axioms ttPretentiousSumChar_eq
#print axioms ttPretentiousSumChar_ge
#print axioms archSupply_of_faithfulArchLower
#print axioms conjC3_of_geom_input_lower
#print axioms faithfulArchLower_of_twist_small

end CastingOut

end NormalNumbers
