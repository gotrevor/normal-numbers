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


/-! ### The narrow range at the trivial character, DISCHARGED

`NarrowTwistSmall` asks for the bound at every modulus `q ≤ (log X)^{1/125}`.  At `q = 1` it is a
theorem, on the same single analytic input (`UniformResonantMass`) the route already carried:
the resonance certificate's *content*
(`ttPretentiousSum_lower_of_uniformResonantMass`, extracted this lap) is exactly a lower bound on
the pretentious sum, and `ttPretentiousSumChar_eq` converts it into the required upper bound on
`Re(z · T)`.  The open part of the narrow range is therefore precisely the **characters**. -/

/-- The `q = 1` case of `NarrowTwistSmall`. -/
def NarrowTwistSmallTriv (z : ℂ) (κ C : ℝ) : Prop :=
  ∀ X : ℝ, 3 ≤ X → ∀ t : ℝ, |t| ≤ Real.log X ^ ((1 : ℝ) / 125) →
    (z * twistedPrimeSum X (1 : DirichletCharacter ℂ 1) t).re
      ≤ (1 - κ) * Real.log (Real.log X) + C

theorem log_ceil_sq_le {X : ℝ} (hX : 3 ≤ X) :
    Real.log ((⌈X ^ 2⌉₊ : ℕ) : ℝ) ≤ 3 * Real.log X := by
  have hlog2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) (by linarith)
  have hceil : ((⌈X ^ 2⌉₊ : ℕ) : ℝ) ≤ X ^ 2 + 1 := by
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ X ^ 2 by positivity)
    linarith
  have h2X : X ^ 2 + 1 ≤ 2 * X ^ 2 := by nlinarith
  calc Real.log ((⌈X ^ 2⌉₊ : ℕ) : ℝ) ≤ Real.log (2 * X ^ 2) :=
        Real.log_le_log (by positivity) (le_trans hceil h2X)
    _ = Real.log 2 + 2 * Real.log X := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
    _ ≤ 3 * Real.log X := by linarith

/-- **The narrow range, at the trivial character, from the route's existing analytic input.**
`κ = ttExponent z > 0` for a unimodular `z ≠ 1`. -/
theorem narrowTwistSmallTriv_of_uniformResonantMass (hURM : UniformResonantMass)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ C : ℝ, NarrowTwistSmallTriv z (ttExponent z) C := by
  obtain ⟨C₁, hC₁0, hlow⟩ := ttPretentiousSum_lower_of_uniformResonantMass hURM hz hz1
  refine ⟨Real.log 3 + Erdos67b.PrimeEstimates.mertensBound + C₁, fun X hX t ht => ?_⟩
  set Y : ℕ := ⌈X ^ 2⌉₊ with hY
  have hlogX : (1 : ℝ) ≤ Real.log X := by
    have h1 : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) hX
    have h3 : (1 : ℝ) ≤ Real.log 3 := by
      have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ 3 by
        nlinarith [Real.exp_one_lt_d9])
      rwa [Real.log_exp] at h
    linarith
  have hXY : X ^ 2 ≤ (Y : ℝ) := Nat.le_ceil _
  have hY2 : 2 ≤ Y := by
    have h1 : (2 : ℝ) ≤ X ^ 2 := by nlinarith
    have : (2 : ℝ) ≤ (Y : ℝ) := le_trans h1 hXY
    exact_mod_cast this
  -- Mertens, upper side
  have hmassle : ∑ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, ((p : ℝ))⁻¹
      ≤ Real.log (Real.log (Y : ℝ)) + Erdos67b.PrimeEstimates.mertensBound := by
    have h := abs_le.1 (Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le hY2)
    have hrw : Erdos67b.PrimeEstimates.primeReciprocals Y
        = ∑ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, ((p : ℝ))⁻¹ := rfl
    rw [← hrw]; linarith [h.2]
  -- log log Y ≤ log log X + log 3
  have hllY : Real.log (Real.log (Y : ℝ)) ≤ Real.log 3 + Real.log (Real.log X) := by
    have h1 : Real.log (Y : ℝ) ≤ 3 * Real.log X := log_ceil_sq_le hX
    calc Real.log (Real.log (Y : ℝ)) ≤ Real.log (3 * Real.log X) :=
          Real.log_le_log (by
            have : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY2
            have := Real.log_le_log (by norm_num : (0:ℝ) < 2) this
            have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
            linarith) h1
      _ = Real.log 3 + Real.log (Real.log X) := by
          rw [Real.log_mul (by norm_num) (by linarith)]
  -- the split, at the trivial character
  have hsplit := ttPretentiousSumChar_eq (z := z) X (1 : DirichletCharacter ℂ 1) t
  rw [ttPretentiousSumChar_one] at hsplit
  have hlow' := hlow X hX t ht
  rw [hsplit] at hlow'
  linarith [hmassle, hllY]

/-- The character-indexed narrow bound restricted to `q = 1` — the shape
`faithfulArchLower_of_twist_small` consumes.  The remaining gap in the narrow range is exactly
`q > 1`: TT's infimum runs over all moduli `q ≤ (log X)^{1/125}`, and the resonance windows must
then be counted per residue class mod `q`. -/
theorem narrowTwistSmall_triv_of_narrow {z : ℂ} {κ C : ℝ} (h : NarrowTwistSmall z κ C) :
    NarrowTwistSmallTriv z κ C :=
  fun X hX t ht => h X hX 1 (1 : DirichletCharacter ℂ 1)
    (by
      have hlogX : (1 : ℝ) ≤ Real.log X := by
        have h1 : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) hX
        have h3 : (1 : ℝ) ≤ Real.log 3 := by
          have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ 3 by
            nlinarith [Real.exp_one_lt_d9])
          rwa [Real.log_exp] at h
        linarith
      simpa using Real.one_le_rpow hlogX (by norm_num : (0:ℝ) ≤ 1 / 125)) t ht


/-! ### The narrow range at PRINCIPAL characters, reduced to `q = 1`

TT's infimum runs over all moduli `q ≤ (log X)^{1/125}`.  The principal character mod `q` is
not a new case: `χ₀(p) = 1` except at the finitely many `p ∣ q`, so its twisted prime sum
differs from the trivial one by at most `∑_{p ∣ q} 1/p ≤ log log q + mertensBound`, and
`log q ≤ (1/125) log log X` makes that `≤ log log log X` — absorbed into any positive fraction
of `log log X`.  So the genuinely open part of the narrow range is the **non-principal**
characters, where the expected mechanism is different anyway (`∑_{p≤Y} χ(p)p^{-it}/p` is
`O(log log(q(2+|t|)))` by the non-vanishing of `L(1+it, χ)`, which is *smaller* than the
principal case, not larger). -/

/-- `∑_{p ≤ Y, p ∣ q} 1/p ≤ log log q + mertensBound` for `q ≥ 2`: the bad primes of a modulus
carry at most the full reciprocal mass below `q`. -/
theorem sum_inv_primes_dvd_le {q Y : ℕ} (hq : 2 ≤ q) :
    ∑ p ∈ (Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ∣ q), ((p : ℝ))⁻¹
      ≤ Real.log (Real.log (q : ℝ)) + Erdos67b.PrimeEstimates.mertensBound := by
  classical
  have hsub : (Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ∣ q)
      ⊆ (Finset.range (q + 1)).filter Nat.Prime := by
    intro p hp
    obtain ⟨-, hpp, hpd⟩ := Finset.mem_filter.mp hp
    have hple : p ≤ q := Nat.le_of_dvd (by omega) hpd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp⟩
  have hle : ∑ p ∈ (Finset.range (Y + 1)).filter (fun p => Nat.Prime p ∧ p ∣ q), ((p : ℝ))⁻¹
      ≤ ∑ p ∈ (Finset.range (q + 1)).filter Nat.Prime, ((p : ℝ))⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
  have h := abs_le.1 (Erdos67b.PrimeEstimates.abs_primeReciprocals_sub_log_log_le hq)
  have hrw : Erdos67b.PrimeEstimates.primeReciprocals q
      = ∑ p ∈ (Finset.range (q + 1)).filter Nat.Prime, ((p : ℝ))⁻¹ := rfl
  rw [← hrw] at hle
  linarith [h.2]

/-- The principal-character twisted prime sum differs from the trivial one only on `p ∣ q`. -/
theorem norm_twistedPrimeSum_principal_sub {X : ℝ} {q : ℕ} (hq : 0 < q) (t : ℝ) :
    ‖twistedPrimeSum X (1 : DirichletCharacter ℂ 1) t - twistedPrimeSum X (1 : DirichletCharacter ℂ q) t‖
      ≤ ∑ p ∈ (Finset.range (⌈X ^ 2⌉₊ + 1)).filter (fun p => Nat.Prime p ∧ p ∣ q),
          ((p : ℝ))⁻¹ := by
  classical
  set F : Finset ℕ := (Finset.range (⌈X ^ 2⌉₊ + 1)).filter Nat.Prime with hF
  have hterm : ∀ p ∈ F,
      (starRingEnd ℂ) ((1 : DirichletCharacter ℂ 1) ((p : ℕ) : ZMod 1)) *
          Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ)) / (p : ℂ)
        - (starRingEnd ℂ) ((1 : DirichletCharacter ℂ q) ((p : ℕ) : ZMod q)) *
          Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ)) / (p : ℂ)
      = if p ∣ q then
          Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ)) / (p : ℂ) else 0 := by
    intro p hp
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have h1 : (starRingEnd ℂ) ((1 : DirichletCharacter ℂ 1) ((p : ℕ) : ZMod 1)) = 1 := by
      rw [Subsingleton.elim ((p : ℕ) : ZMod 1) 1, map_one, map_one]
    by_cases hd : p ∣ q
    · have hnu : ¬ IsUnit ((p : ℕ) : ZMod q) := by
        rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hpp]
        exact fun h => h hd
      rw [h1, MulChar.map_nonunit _ hnu]
      simp [hd]
    · have hu : IsUnit ((p : ℕ) : ZMod q) := by
        rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hpp]
        exact hd
      rw [h1, MulChar.one_apply hu]
      simp [hd]
  rw [twistedPrimeSum, twistedPrimeSum, ← hF, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  have hfil : F.filter (fun p => p ∣ q)
      = (Finset.range (⌈X ^ 2⌉₊ + 1)).filter (fun p => Nat.Prime p ∧ p ∣ q) := by
    rw [hF, Finset.filter_filter]
  rw [hfil]
  refine le_trans (norm_sum_le _ _) (le_of_eq (Finset.sum_congr rfl ?_))
  · intro p hp
    have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    rw [norm_div, Complex.norm_exp]
    have hre : (-(t : ℂ) * Complex.I * (Real.log p : ℂ)).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre, Real.exp_zero, Complex.norm_natCast, one_div]


/-- `log log X > 0` for `X ≥ 3`, the standing size fact. -/
theorem logloglog_pos {X : ℝ} (hX : 3 ≤ X) : 0 < Real.log (Real.log X) := by
  have h1 : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have h3 : (1 : ℝ) < Real.log 3 := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ 2.72 by
      nlinarith [Real.exp_one_lt_d9])
    rw [Real.log_exp] at h
    have : Real.log 2.72 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith
  exact Real.log_pos (by linarith)

/-- **The principal characters of the narrow range, reduced to `q = 1`.**  The loss is
`log log q + mertensBound ≤ log log log X + O(1)`, absorbed by halving the saving. -/
theorem narrowTwist_principal_of_triv {z : ℂ} {κ C : ℝ} (hz : ‖z‖ = 1) (hκ : 0 < κ)
    (h : NarrowTwistSmallTriv z κ C) :
    ∀ X : ℝ, 3 ≤ X → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) →
      ∀ t : ℝ, |t| ≤ Real.log X ^ ((1 : ℝ) / 125) →
        (z * twistedPrimeSum X (1 : DirichletCharacter ℂ q) t).re
          ≤ (1 - κ / 2) * Real.log (Real.log X)
            + (C + Erdos67b.PrimeEstimates.mertensBound + 1 + |Real.log (κ / 2)|) := by
  intro X hX q hq hqX t ht
  set u : ℝ := Real.log (Real.log X) with hu
  have hu0 : 0 < u := logloglog_pos hX
  have hmert0 : 0 ≤ Erdos67b.PrimeEstimates.mertensBound :=
    Erdos67b.PrimeEstimates.mertensBound_nonneg
  have habs : (0 : ℝ) ≤ |Real.log (κ / 2)| := abs_nonneg _
  have hq0R : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have htriv := h X hX t ht
  rw [← hu] at htriv
  by_cases hq1 : q = 1
  · -- `q = 1`: the same sum
    subst hq1
    nlinarith
  · -- `q ≥ 2`
    have hq2' : 2 ≤ q := by omega
    have hlogq : Real.log (q : ℝ) ≤ u / 125 := by
      have h1 : Real.log (q : ℝ) ≤ Real.log (Real.log X ^ ((1 : ℝ) / 125)) :=
        Real.log_le_log hq0R hqX
      have hlogX1 : (1 : ℝ) < Real.log X := by
        have he : Real.log (Real.exp 1) < Real.log 3 :=
          Real.log_lt_log (Real.exp_pos 1) (by nlinarith [Real.exp_one_lt_d9])
        rw [Real.log_exp] at he
        have h3 : Real.log 3 ≤ Real.log X := Real.log_le_log (by norm_num) hX
        linarith
      rw [Real.log_rpow (by linarith)] at h1
      rw [hu]
      linarith
    have hlogq0 : 0 < Real.log (q : ℝ) := by
      refine Real.log_pos ?_
      have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2'
      linarith
    have hllq : Real.log (Real.log (q : ℝ)) ≤ Real.log u := by
      refine Real.log_le_log hlogq0 (by linarith)
    -- `log u ≤ (κ/2) u − 1 − log(κ/2)`
    have hsub : Real.log ((κ / 2) * u) ≤ (κ / 2) * u - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hsplit : Real.log ((κ / 2) * u) = Real.log (κ / 2) + Real.log u :=
      Real.log_mul (by positivity) (by positivity)
    have hlu : Real.log u ≤ (κ / 2) * u - 1 - Real.log (κ / 2) := by
      rw [hsplit] at hsub; linarith
    have habs : -Real.log (κ / 2) ≤ |Real.log (κ / 2)| := neg_le_abs _
    -- the difference of the two twisted sums
    have hdiff := norm_twistedPrimeSum_principal_sub (X := X) (q := q) hq t
    have hbad := sum_inv_primes_dvd_le (q := q) (Y := ⌈X ^ 2⌉₊) hq2'
    have hre : (z * twistedPrimeSum X (1 : DirichletCharacter ℂ q) t).re
        ≤ (z * twistedPrimeSum X (1 : DirichletCharacter ℂ 1) t).re
          + ‖twistedPrimeSum X (1 : DirichletCharacter ℂ 1) t
              - twistedPrimeSum X (1 : DirichletCharacter ℂ q) t‖ := by
      have heq : (z * twistedPrimeSum X (1 : DirichletCharacter ℂ q) t).re
          - (z * twistedPrimeSum X (1 : DirichletCharacter ℂ 1) t).re
          = (z * (twistedPrimeSum X (1 : DirichletCharacter ℂ q) t
              - twistedPrimeSum X (1 : DirichletCharacter ℂ 1) t)).re := by
        rw [mul_sub, Complex.sub_re]
      have hle : (z * (twistedPrimeSum X (1 : DirichletCharacter ℂ q) t
            - twistedPrimeSum X (1 : DirichletCharacter ℂ 1) t)).re
          ≤ ‖twistedPrimeSum X (1 : DirichletCharacter ℂ 1) t
              - twistedPrimeSum X (1 : DirichletCharacter ℂ q) t‖ := by
        refine le_trans (Complex.re_le_norm _) ?_
        rw [norm_mul, hz, one_mul, norm_sub_rev]
      linarith [heq, hle]
    have hgoal : (z * twistedPrimeSum X (1 : DirichletCharacter ℂ q) t).re
        ≤ (1 - κ / 2) * u + (C + Erdos67b.PrimeEstimates.mertensBound + 1
            + |Real.log (κ / 2)|) := by nlinarith [hre, hdiff, hbad, hllq, hlu, habs, htriv]
    rw [hu] at hgoal
    exact hgoal

/-- **The non-principal characters of the narrow range** — the residual debt, named.  Expected to
be *easier* than the principal case: `∑_{p≤Y} χ(p)p^{-it}/p = O(log log(q(2+|t|)))` by the
non-vanishing of `L(1+it, χ)` on the 1-line, and `q, |t| ≤ (log X)^{1/125}` makes that
`O(log log log X)`. -/
def NonPrincipalTwistSmall (κ C : ℝ) : Prop :=
  ∀ X : ℝ, 3 ≤ X → ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    (q : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) →
    ∀ t : ℝ, |t| ≤ Real.log X ^ ((1 : ℝ) / 125) →
      ‖twistedPrimeSum X χ t‖ ≤ (1 - κ) * Real.log (Real.log X) + C

/-- The `q = 0` characters carry no primes at all: in `ZMod 0 = ℤ` no prime is a unit, so the
principal character vanishes on every prime and the twisted sum is `0`. -/
theorem twistedPrimeSum_zero_modulus (X : ℝ) (t : ℝ) :
    twistedPrimeSum X (1 : DirichletCharacter ℂ 0) t = 0 := by
  rw [twistedPrimeSum]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hnu : ¬ IsUnit ((p : ℕ) : ZMod 0) := by
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_zero_right]
    exact hpp.ne_one
  rw [MulChar.map_nonunit _ hnu, map_zero, zero_mul, zero_div]

/-- **The narrow range, assembled from the `q = 1` theorem and the non-principal debt.** -/
theorem narrowTwistSmall_of_triv_of_nonPrincipal {z : ℂ} {κ C : ℝ} (hz : ‖z‖ = 1) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hC : 0 ≤ C) (htriv : NarrowTwistSmallTriv z κ C) (hnp : NonPrincipalTwistSmall κ C) :
    NarrowTwistSmall z (κ / 2)
      (C + Erdos67b.PrimeEstimates.mertensBound + 1 + |Real.log (κ / 2)|) := by
  intro X hX q χ hqX t ht
  have hu0 : 0 < Real.log (Real.log X) := logloglog_pos hX
  have hmert0 : 0 ≤ Erdos67b.PrimeEstimates.mertensBound :=
    Erdos67b.PrimeEstimates.mertensBound_nonneg
  have habs : (0 : ℝ) ≤ |Real.log (κ / 2)| := abs_nonneg _
  have hznorm : ∀ T : ℂ, (z * T).re ≤ ‖T‖ := by
    intro T
    refine le_trans (Complex.re_le_norm _) ?_
    rw [norm_mul, hz, one_mul]
  rcases eq_or_ne χ 1 with rfl | hne
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · rw [twistedPrimeSum_zero_modulus X t, mul_zero, Complex.zero_re]
      nlinarith
    · exact le_trans (narrowTwist_principal_of_triv hz hκ htriv X hX q hq hqX t ht) (by linarith)
  · have h2 := hnp X hX q χ hne hqX t ht
    have h1 := hznorm (twistedPrimeSum X χ t)
    nlinarith


/-! ### Uniformity in the twist `h'`

`ArchSupply (TTNonPretentiousAt A) b` fixes ONE constant `A` across every primitive twist `h'`,
so the saving `κ` and the constant must be uniform in `h'`.  They are: `depthRoot b h' 0 =
ee(h'/b)` and `b ∤ h'`, so the angle is `2π k/b` with `1 ≤ k ≤ b−1` and
`|arg| ≥ 2π/b` — a bound depending on `b` alone.  (This obligation was invisible while the
hypothesis was vacuous.) -/

/-- `cos(2πk/b) ≤ cos(2π/b)` for `1 ≤ k ≤ b−1`: on the circle the angle sits at distance at
least `2π/b` from `0`. -/
theorem cos_two_pi_mul_div_le {b k : ℕ} (hb : 2 ≤ b) (hk1 : 1 ≤ k) (hkb : k ≤ b - 1) :
    Real.cos (2 * Real.pi * (k : ℝ) / (b : ℝ)) ≤ Real.cos (2 * Real.pi / (b : ℝ)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hk1' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hkb' : (k : ℝ) ≤ (b : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ b := by omega
    have : (k : ℝ) ≤ ((b - 1 : ℕ) : ℝ) := by exact_mod_cast hkb
    rwa [Nat.cast_sub h1, Nat.cast_one] at this
  have hlow : 2 * Real.pi / (b : ℝ) ≤ 2 * Real.pi * (k : ℝ) / (b : ℝ) := by
    rw [div_le_div_iff_of_pos_right hb0]
    nlinarith
  have hhigh : 2 * Real.pi * (k : ℝ) / (b : ℝ) ≤ 2 * Real.pi - 2 * Real.pi / (b : ℝ) := by
    rw [div_le_iff₀ hb0]
    have hdiv : 2 * Real.pi / (b : ℝ) * (b : ℝ) = 2 * Real.pi := by field_simp
    nlinarith [hkb', hpi, hb0]
  have hbpi : 2 * Real.pi / (b : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hb0]; nlinarith
  have h0 : (0 : ℝ) ≤ 2 * Real.pi / (b : ℝ) := by positivity
  rcases le_or_gt (2 * Real.pi * (k : ℝ) / (b : ℝ)) Real.pi with hle | hgt
  · exact Real.cos_le_cos_of_nonneg_of_le_pi h0 hle hlow
  · rw [← Real.cos_two_pi_sub (2 * Real.pi * (k : ℝ) / (b : ℝ))]
    exact Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith) (by linarith)

/-- `Re (ee r) = cos (2π r)` for real `r`. -/
theorem ee_re_real (r : ℝ) : (ee ((r : ℝ) : ℂ)).re = Real.cos (2 * Real.pi * r) := by
  rw [ee, show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((r : ℝ) : ℂ)
      = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

/-- **The angle of a primitive depth root is at least `2π/b`** — uniformly in the twist `h'`,
which is exactly the uniformity `ArchSupply (TTNonPretentiousAt A) b` needs. -/
theorem resEps_depthRoot_ge {b : ℕ} (hb : 2 ≤ b) {h' : ℤ} (hnd : ¬ ((b : ℤ) ∣ h')) :
    Real.pi / (b : ℝ) ≤ resEps (depthRoot b h' 0) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have hb2 : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbz : (0 : ℤ) < (b : ℤ) := by exact_mod_cast (by omega : 0 < b)
  set k : ℕ := (h' % (b : ℤ)).toNat with hk
  have hmod0 : 0 ≤ h' % (b : ℤ) := Int.emod_nonneg _ hbz.ne'
  have hmodlt : h' % (b : ℤ) < (b : ℤ) := Int.emod_lt_of_pos _ hbz
  have hmodne : h' % (b : ℤ) ≠ 0 := fun hcon => hnd (Int.dvd_of_emod_eq_zero hcon)
  have hkz : (k : ℤ) = h' % (b : ℤ) := Int.toNat_of_nonneg hmod0
  have hk1 : 1 ≤ k := by omega
  have hkb : k ≤ b - 1 := by omega
  have hsplit : (h' : ℝ) / (b : ℝ) = (k : ℝ) / (b : ℝ) + ((h' / (b : ℤ) : ℤ) : ℝ) := by
    have hid : (b : ℤ) * (h' / (b : ℤ)) + h' % (b : ℤ) = h' := Int.mul_ediv_add_emod h' (b : ℤ)
    have hidk : (b : ℤ) * (h' / (b : ℤ)) + (k : ℤ) = h' := by rw [hkz]; exact hid
    have hR : (b : ℝ) * ((h' / (b : ℤ) : ℤ) : ℝ) + (k : ℝ) = (h' : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hidk
    field_simp
    linarith
  have hre : (depthRoot b h' 0).re = Real.cos (2 * Real.pi * (k : ℝ) / (b : ℝ)) := by
    rw [depthRoot, show ((h' : ℝ) / (b : ℝ) ^ (0 + 1)) = (h' : ℝ) / (b : ℝ) by norm_num,
      ee_re_real, hsplit,
      show 2 * Real.pi * ((k : ℝ) / (b : ℝ) + ((h' / (b : ℤ) : ℤ) : ℝ))
        = 2 * Real.pi * (k : ℝ) / (b : ℝ) + ((h' / (b : ℤ) : ℤ) : ℝ) * (2 * Real.pi) by ring]
    exact Real.cos_add_int_mul_two_pi _ _
  have hznorm : ‖depthRoot b h' 0‖ = 1 := norm_ee_real _
  have hz0 : depthRoot b h' 0 ≠ 0 := by
    intro hcon; rw [hcon] at hznorm; simp at hznorm
  have hcosarg : Real.cos (depthRoot b h' 0).arg = (depthRoot b h' 0).re := by
    rw [Complex.cos_arg hz0, hznorm, div_one]
  by_contra hcon
  push_neg at hcon
  rw [resEps] at hcon
  have hring : 2 * (Real.pi / (b : ℝ)) = 2 * Real.pi / (b : ℝ) := by ring
  have habs : |(depthRoot b h' 0).arg| < 2 * Real.pi / (b : ℝ) := by linarith [hring]
  have hbpi : 2 * Real.pi / (b : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hb0]; nlinarith
  have hstrict : Real.cos (2 * Real.pi / (b : ℝ)) < Real.cos |(depthRoot b h' 0).arg| :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hbpi habs
  rw [Real.cos_abs, hcosarg, hre] at hstrict
  exact absurd (cos_two_pi_mul_div_le hb hk1 hkb) (not_le.mpr hstrict)


/-- **The uniform saving.**  `κ(b) := (1/10)·min(π/b, 1/256)²` is a positive lower bound for
`ttExponent (depthRoot b h' 0)` valid for EVERY primitive twist `h'` — the uniformity
`FaithfulArchLower b C` needs on the exponent side. -/
noncomputable def kappaDepth (b : ℕ) : ℝ := (1 / 10) * (min (Real.pi / (b : ℝ)) (1 / 256)) ^ 2

theorem kappaDepth_pos {b : ℕ} (hb : 2 ≤ b) : 0 < kappaDepth b := by
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  have h : 0 < min (Real.pi / (b : ℝ)) (1 / 256 : ℝ) :=
    lt_min (by positivity) (by norm_num)
  rw [kappaDepth]; positivity

theorem ttExponent_depthRoot_ge {b : ℕ} (hb : 2 ≤ b) {h' : ℤ} (hnd : ¬ ((b : ℤ) ∣ h')) :
    kappaDepth b ≤ ttExponent (depthRoot b h' 0) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi2 : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2, Real.pi_gt_three]
  have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
  set z : ℂ := depthRoot b h' 0 with hzdef
  set ε : ℝ := ttEps z with hε
  set e : ℝ := min (Real.pi / (b : ℝ)) (1 / 256 : ℝ) with he
  have he0 : 0 < e := lt_min (by positivity) (by norm_num)
  have hres : Real.pi / (b : ℝ) ≤ resEps z := resEps_depthRoot_ge hb hnd
  have hεe : e ≤ ε := by
    rw [hε, ttEps, he]
    exact min_le_min hres le_rfl
  have hε0 : 0 < ε := lt_of_lt_of_le he0 hεe
  have hεq : ε ≤ 1 / 256 := ttEps_le_quarter
  have hcos : (2 / Real.pi ^ 2) * ε ^ 2 ≤ 1 - Real.cos ε := by
    have hle : |ε| ≤ Real.pi := by
      rw [abs_of_pos hε0]
      nlinarith [Real.pi_gt_three]
    have h := Real.cos_le_one_sub_mul_cos_sq (x := ε) hle
    linarith
  have hfac : (3 : ℝ) / 5 ≤ 1 - (126 / 125 : ℝ) * (100 * ε) := by nlinarith
  have hsq : e ^ 2 ≤ ε ^ 2 := by nlinarith
  have hc0 : (0 : ℝ) ≤ 1 - Real.cos ε := by nlinarith [Real.cos_le_one ε]
  have hkey : (2 / Real.pi ^ 2) * e ^ 2 * (3 / 5) ≤ (1 - Real.cos ε) * (1 - (126 / 125) * (100 * ε)) := by
    have h1 : (2 / Real.pi ^ 2) * e ^ 2 ≤ 1 - Real.cos ε := by
      have : (2 / Real.pi ^ 2) * e ^ 2 ≤ (2 / Real.pi ^ 2) * ε ^ 2 := by
        have : (0 : ℝ) < 2 / Real.pi ^ 2 := by positivity
        nlinarith
      linarith
    nlinarith [hc0, he0]
  have hnum : kappaDepth b ≤ (2 / Real.pi ^ 2) * e ^ 2 * (3 / 5) := by
    have h1 : (1 / 10 : ℝ) ≤ 6 / (5 * Real.pi ^ 2) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    have h2 : (2 / Real.pi ^ 2) * e ^ 2 * (3 / 5) = (6 / (5 * Real.pi ^ 2)) * e ^ 2 := by
      field_simp; ring
    rw [kappaDepth, ← he, h2]
    nlinarith [sq_nonneg e, h1]
  rw [ttExponent, ← hε]
  linarith


/-! ### Decoupling the non-principal narrow debt from `X`

`NonPrincipalTwistSmall κ C` mentions `X` on both sides, which hides what it actually needs.
The textbook bound behind it — `∑_{p ≤ Y} χ̄(p)p^{-it}/p = log L(1+it, χ) + O(1)`, with
`|log L(1+it,χ)| ≤ log log(q(2+|t|)) + O(1)` from the non-vanishing of `L` on the 1-line — is
uniform in the *length* `Y`: the right-hand side involves only the conductor `q` and the twist
`t`.  `NonPrincipalLocalBound` is that statement, with **no `X` on the right**, and the reduction
below shows it is enough, with the generous saving `κ = 1/2`.

Why `1/2` is free: `q, |t| ≤ (log X)^{1/125}` forces `3 + q(2+|t|) ≤ 6 (log X)²`, so the local
bound is `≤ log(log 6 + 2 log log X) + B`, and `log w ≤ w/8 + log 8 − 1` turns the outer
logarithm into `(log log X)/2 + O(1)`.  Nothing about the exponent `1/125` is used beyond
`1/125 ≤ 1`: any polynomial range of conductors and twists would do.  This is the honest
statement of the debt — a bound on a Dirichlet L-function, not on anything `X`-dependent. -/

/-- **The non-principal narrow debt, localised.**  A bound on the twisted prime sum for
non-principal `χ` whose right-hand side depends only on the conductor `q` and the twist `t` —
not on the length of the sum.  This is `|log L(1+it, χ)| ≪ log log(q(2+|t|))`. -/
def NonPrincipalLocalBound (B : ℝ) : Prop :=
  ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ X t : ℝ, 3 ≤ X →
    ‖twistedPrimeSum X χ t‖ ≤ Real.log (Real.log (3 + (q : ℝ) * (2 + |t|))) + B

theorem one_lt_log_of_three_le {X : ℝ} (hX : 3 ≤ X) : 1 < Real.log X := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  nlinarith [Real.exp_one_lt_d9]

theorem log_six_le_two : Real.log 6 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_one_gt_d9, h2]

theorem log_eight_sub_one_le : Real.log 8 - 1 ≤ 11 / 10 := by
  have h : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
  nlinarith [Real.log_two_lt_d9]

/-- `log w ≤ w/8 + log 8 − 1` — the tangent-line bound at `w = 8`, which is what converts the
outer logarithm of `log 6 + 2 log log X` into a `(log log X)/2`. -/
theorem log_le_div_eight {w : ℝ} (hw : 0 < w) : Real.log w ≤ w / 8 + Real.log 8 - 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < w / 8 by positivity)
  rw [Real.log_div hw.ne' (by norm_num)] at h
  linarith

/-- **The reduction.**  The localised L-function bound gives the narrow non-principal range with
saving `κ = 1/2`, i.e. far more than the `κ` the chain needs.  So the only thing the
non-principal narrow range still owes is a bound with **no `X` in it**. -/
theorem nonPrincipalTwistSmall_of_localBound {B : ℝ} (h : NonPrincipalLocalBound B) :
    NonPrincipalTwistSmall (1 / 2) (B + 2) := by
  intro X hX q χ hne hqX t ht
  set u : ℝ := Real.log X with hu
  have hu1 : 1 < u := one_lt_log_of_three_le hX
  have hv0 : 0 < Real.log u := Real.log_pos hu1
  -- the `1/125` powers are at most `u`
  have hpow : u ^ ((1 : ℝ) / 125) ≤ u := by
    have := Real.rpow_le_rpow_of_exponent_le hu1.le (show (1:ℝ)/125 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  have hq : (q : ℝ) ≤ u := le_trans hqX hpow
  have htu : |t| ≤ u := le_trans ht hpow
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have ht0 : (0 : ℝ) ≤ |t| := abs_nonneg t
  set A : ℝ := 3 + (q : ℝ) * (2 + |t|) with hA
  have hA3 : (3 : ℝ) ≤ A := by simp only [hA]; nlinarith
  have hAle : A ≤ 6 * u ^ 2 := by
    simp only [hA]
    nlinarith [mul_le_mul_of_nonneg_right hq (by linarith : (0:ℝ) ≤ 2 + |t|),
      mul_le_mul_of_nonneg_left htu (by linarith : (0:ℝ) ≤ u)]
  -- outer: `log (log A) ≤ (log u)/2 + 2`
  have hlogA : Real.log A ≤ Real.log 6 + 2 * Real.log u := by
    have h1 : Real.log A ≤ Real.log (6 * u ^ 2) :=
      Real.log_le_log (by linarith) hAle
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    <;> push_cast <;> ring_nf
  have hlogA0 : 0 < Real.log A := Real.log_pos (by linarith)
  have hinner : 0 < Real.log 6 + 2 * Real.log u := lt_of_lt_of_le hlogA0 hlogA
  have houter : Real.log (Real.log A) ≤ Real.log (Real.log 6 + 2 * Real.log u) :=
    Real.log_le_log hlogA0 hlogA
  have htan := log_le_div_eight hinner
  have hfin : Real.log (Real.log A) ≤ (1 / 2) * Real.log u + 2 := by
    nlinarith [log_six_le_two, log_eight_sub_one_le, hv0]
  have hmain := h q χ hne X t hX
  simp only [← hA] at hmain
  nlinarith

/-- The narrow range in full, from the `q = 1` theorem and the **localised** non-principal
bound: no `X`-dependent hypothesis is left in the narrow range. -/
theorem narrowTwistSmall_of_triv_of_localBound {z : ℂ} {B : ℝ} (hz : ‖z‖ = 1)
    (hB : 0 ≤ B) (htriv : NarrowTwistSmallTriv z (1 / 2) (B + 2))
    (hloc : NonPrincipalLocalBound B) :
    NarrowTwistSmall z (1 / 4)
      (B + 2 + Erdos67b.PrimeEstimates.mertensBound + 1 + |Real.log ((1:ℝ) / 4)|) := by
  have h := narrowTwistSmall_of_triv_of_nonPrincipal hz (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1:ℝ)/2 ≤ 1) (by linarith) htriv
    (nonPrincipalTwistSmall_of_localBound hloc)
  have e : (1 : ℝ) / 2 / 2 = 1 / 4 := by norm_num
  rw [e] at h
  exact h

/-! ### Monotonicity, and the narrow range on ONE analytic debt

The three narrow-range `Prop`s all read `… ≤ (1 − κ)·log log X + C`, so each is monotone **down**
in the saving `κ` and **up** in the constant `C` (using `log log X > 0` for `X ≥ 3`).  That is
what lets the `q = 1` theorem's saving `ttExponent z` be combined with the localised bound's
saving `1/2`: take the minimum. -/

theorem narrowTwistSmallTriv_mono {z : ℂ} {κ κ' C C' : ℝ} (hκ : κ' ≤ κ) (hC : C ≤ C')
    (h : NarrowTwistSmallTriv z κ C) : NarrowTwistSmallTriv z κ' C' := by
  intro X hX t ht
  have h0 : 0 < Real.log (Real.log X) := logloglog_pos hX
  nlinarith [h X hX t ht]

theorem nonPrincipalTwistSmall_mono {κ κ' C C' : ℝ} (hκ : κ' ≤ κ) (hC : C ≤ C')
    (h : NonPrincipalTwistSmall κ C) : NonPrincipalTwistSmall κ' C' := by
  intro X hX q χ hne hqX t ht
  have h0 : 0 < Real.log (Real.log X) := logloglog_pos hX
  nlinarith [h X hX q χ hne hqX t ht]

/-- **The narrow range rests on exactly two things.**  `UniformResonantMass` (the route's
pre-existing analytic input, which handles `q = 1`) and `NonPrincipalLocalBound` (a bound on
`log L(1+it, χ)` with no `X` in it).  The saving is `min(ttExponent z, 1/2)/2`, positive for any
unimodular `z ≠ 1`. -/
theorem narrowTwistSmall_of_urm_of_localBound (hURM : UniformResonantMass)
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) {B : ℝ} (hB : 0 ≤ B)
    (hloc : NonPrincipalLocalBound B) :
    ∃ C : ℝ, NarrowTwistSmall z (min (ttExponent z) (1 / 2) / 2) C := by
  obtain ⟨C₀, htriv0⟩ := narrowTwistSmallTriv_of_uniformResonantMass hURM hz hz1
  set κ : ℝ := min (ttExponent z) (1 / 2) with hκdef
  have hκ0 : 0 < κ := lt_min (ttExponent_pos hz hz1) (by norm_num)
  have hκ1 : κ ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  set C : ℝ := max C₀ (B + 2) with hCdef
  have htriv : NarrowTwistSmallTriv z κ C :=
    narrowTwistSmallTriv_mono (min_le_left _ _) (le_max_left _ _) htriv0
  have hnp : NonPrincipalTwistSmall κ C :=
    nonPrincipalTwistSmall_mono (min_le_right _ _) (le_max_right _ _)
      (nonPrincipalTwistSmall_of_localBound hloc)
  have hC0 : 0 ≤ C := le_trans (by linarith) (le_max_right C₀ (B + 2))
  exact ⟨_, narrowTwistSmall_of_triv_of_nonPrincipal hz hκ0 hκ1 hC0 htriv hnp⟩

theorem narrowTwistSmall_mono {z : ℂ} {κ κ' C C' : ℝ} (hκ : κ' ≤ κ) (hC : C ≤ C')
    (h : NarrowTwistSmall z κ C) : NarrowTwistSmall z κ' C' := by
  intro X hX q χ hq t ht
  have h0 : 0 < Real.log (Real.log X) := logloglog_pos hX
  nlinarith [h X hX q χ hq t ht]

/-- `depthRoot b h' 0` depends on `h'` only through `h' % b`: `ee` is `1`-periodic. -/
theorem depthRoot_zero_emod {b : ℕ} (hb : 0 < b) (h' : ℤ) :
    depthRoot b h' 0 = depthRoot b (h' % (b : ℤ)) 0 := by
  have hb0 : ((b : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hsplit : (h' : ℝ) / (b : ℝ)
      = ((h' % (b : ℤ) : ℤ) : ℝ) / (b : ℝ) + ((h' / (b : ℤ) : ℤ) : ℝ) := by
    have hid : (b : ℤ) * (h' / (b : ℤ)) + h' % (b : ℤ) = h' := Int.mul_ediv_add_emod h' (b : ℤ)
    have hR : (b : ℝ) * ((h' / (b : ℤ) : ℤ) : ℝ) + ((h' % (b : ℤ) : ℤ) : ℝ) = (h' : ℝ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hid
    field_simp
    linarith
  rw [depthRoot, depthRoot,
    show ((h' : ℝ) / (b : ℝ) ^ (0 + 1)) = (h' : ℝ) / (b : ℝ) by norm_num,
    show (((h' % (b : ℤ) : ℤ) : ℝ) / (b : ℝ) ^ (0 + 1))
      = ((h' % (b : ℤ) : ℤ) : ℝ) / (b : ℝ) by norm_num,
    show ((((h' : ℝ) / (b : ℝ) : ℝ)) : ℂ)
      = ((((h' % (b : ℤ) : ℤ) : ℝ) / (b : ℝ) : ℝ) : ℂ) + ((((h' / (b : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) by
      rw [hsplit]; push_cast; ring,
    ee_add, ee_intCast_eq_one, mul_one]

/-- **The narrow bound is uniform in the twist `h'`.**  `FaithfulArchLower` needs ONE constant
`C` across all primitive `h'` (TT's implied constant is absolute).  That is free from
periodicity: `depthRoot b h' 0` takes at most `b` values, so a pointwise family of constants has
a maximum. -/
theorem exists_uniform_narrow_const {b : ℕ} (hb : 2 ≤ b) {κ : ℝ}
    (hpt : ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') → ∃ C : ℝ, NarrowTwistSmall (depthRoot b h' 0) κ C) :
    ∃ C : ℝ, ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') → NarrowTwistSmall (depthRoot b h' 0) κ C := by
  classical
  have hb0 : 0 < b := by omega
  set P : ℕ → Prop := fun r => ∃ C : ℝ, NarrowTwistSmall (depthRoot b (r : ℤ) 0) κ C with hP
  set F : ℕ → ℝ := fun r => if hr : P r then hr.choose else 0 with hF
  have hne : (Finset.range b).Nonempty := ⟨0, Finset.mem_range.mpr hb0⟩
  refine ⟨(Finset.range b).sup' hne F, fun h' hnd => ?_⟩
  set r : ℕ := (h' % (b : ℤ)).toNat with hr
  have hmodnn : 0 ≤ h' % (b : ℤ) := Int.emod_nonneg h' (by exact_mod_cast hb0.ne')
  have hrz : ((r : ℕ) : ℤ) = h' % (b : ℤ) := Int.toNat_of_nonneg hmodnn
  have hrlt : r < b := by
    have := Int.emod_lt_of_pos h' (show (0 : ℤ) < (b : ℤ) by exact_mod_cast hb0)
    omega
  have heq : depthRoot b h' 0 = depthRoot b (r : ℤ) 0 := by
    rw [depthRoot_zero_emod hb0 h', hrz]
  have hPr : P r := by
    obtain ⟨C, hC⟩ := hpt h' hnd
    exact ⟨C, by rwa [heq] at hC⟩
  have hFr : NarrowTwistSmall (depthRoot b (r : ℤ) 0) κ (F r) := by
    simp only [hF, dif_pos hPr]
    exact hPr.choose_spec
  have hle : F r ≤ (Finset.range b).sup' hne F :=
    Finset.le_sup' F (Finset.mem_range.mpr hrlt)
  rw [heq]
  exact narrowTwistSmall_mono le_rfl hle hFr

/-- **`FaithfulArchLower` on the reduced debt set.**  The faithful archimedean supply for base
`b` now rests on exactly three things: `UniformResonantMass` (the route's pre-existing analytic
input, which covers `q = 1`), `NonPrincipalLocalBound` (an `X`-free bound on `log L(1+it, χ)`)
and `WideTwistSmall` (the wide twist range).  The twist-uniformity of the constant is a theorem
(`exists_uniform_narrow_const`), not a hypothesis. -/
theorem faithfulArchLower_of_urm_of_localBound {b : ℕ} (hb : 2 ≤ b)
    (hURM : UniformResonantMass) {B : ℝ} (hB : 0 ≤ B)
    (hloc : NonPrincipalLocalBound B)
    (hwide : ∀ κ C : ℝ, 0 < κ → WideTwistSmall κ C) :
    ∃ C : ℝ, FaithfulArchLower b (C + Erdos67b.PrimeEstimates.mertensBound) := by
  have hkp := kappaDepth_pos hb
  have hmin0 : 0 ≤ min (Real.pi / (b : ℝ)) ((1 : ℝ) / 256) :=
    le_min (by positivity) (by norm_num)
  have hminle : min (Real.pi / (b : ℝ)) ((1 : ℝ) / 256) ≤ 1 / 256 := min_le_right _ _
  have hkhalf : kappaDepth b ≤ 1 / 2 := by
    rw [kappaDepth]; nlinarith
  set κ : ℝ := kappaDepth b / 2 with hκdef
  have hκ0 : 0 < κ := by simp only [hκdef]; linarith
  have hκ1 : κ ≤ 1 := by simp only [hκdef]; linarith
  have hpt : ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') →
      ∃ C : ℝ, NarrowTwistSmall (depthRoot b h' 0) κ C := by
    intro h' hnd
    have hz : ‖depthRoot b h' 0‖ = 1 := norm_ee_real _
    have hz1 : depthRoot b h' 0 ≠ 1 := by
      intro hone
      have hge := resEps_depthRoot_ge hb hnd
      rw [hone] at hge
      simp only [resEps, Complex.arg_one, abs_zero] at hge
      have : 0 < Real.pi / (b : ℝ) := by positivity
      linarith
    obtain ⟨C, hC⟩ := narrowTwistSmall_of_urm_of_localBound hURM hz hz1 hB hloc
    refine ⟨C, narrowTwistSmall_mono ?_ le_rfl hC⟩
    have h1 : kappaDepth b ≤ ttExponent (depthRoot b h' 0) := ttExponent_depthRoot_ge hb hnd
    have : kappaDepth b ≤ min (ttExponent (depthRoot b h' 0)) (1 / 2) := le_min h1 hkhalf
    simp only [hκdef]; linarith
  obtain ⟨C0, hC0⟩ := exists_uniform_narrow_const hb hpt
  exact ⟨C0, faithfulArchLower_of_twist_small hκ0 hκ1 hC0 (hwide κ C0 hκ0)⟩

#print axioms depthRoot_zero_emod
#print axioms exists_uniform_narrow_const
#print axioms faithfulArchLower_of_urm_of_localBound

/-! ### The headline on the reduced debt set

`conjC3_of_geom_input_lower` asks for ONE constant `C` across all bases `b ≥ 3`, and the reduced
narrow-range supply cannot give that: its constant comes from `UniformResonantMass` at window
half-width `δ ≤ resEps (depthRoot b h' 0)`, which is `≍ π/b`, so it necessarily degrades with
`b`.  **That is not a defect of the reduction** — `ConjC3` is a statement about each base
separately (`conjC3_of_weylLambertTwist`), so the correlation input may be assumed with a
base-dependent implied constant.  The theorem below is the honest shape: `ConjC3` from the
`K`-point input *at every positive implied constant* plus the three analytic debts. -/

/-- **`ConjC3` from the faithful correlation input and the REDUCED archimedean debt set.**
The archimedean side is now exactly three named statements — `UniformResonantMass` (already the
route's input, covering `q = 1`), `NonPrincipalLocalBound` (an `X`-free bound on
`log L(1+it, χ)` for non-principal `χ`) and `WideTwistSmall` (the wide twist range) — with the
twist-uniformity of the implied constant proved, not assumed. -/
theorem conjC3_of_geom_input_reduced {c₀ θ B : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1)
    (m : ℕ)
    (hin : ∀ A : ℝ, 0 < A → ∀ b : ℕ, 3 ≤ b → ∀ K,
      KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K)
    (hURM : UniformResonantMass) (hB : 0 ≤ B) (hloc : NonPrincipalLocalBound B)
    (hwide : ∀ κ C : ℝ, 0 < κ → WideTwistSmall κ C) :
    ConjC3 := by
  refine conjC3_of_weylLambertTwist fun b hb => ?_
  obtain ⟨C, hC⟩ := faithfulArchLower_of_urm_of_localBound (by omega : 2 ≤ b) hURM hB hloc hwide
  exact weylLambertTwist_of_geom_input_at hb hc₀ hθ0 hθ m
    (hin _ (Real.exp_pos _) b hb) (archSupply_of_faithfulArchLower hC)

#print axioms conjC3_of_geom_input_reduced


/-! ### Both remaining debts are ONE statement

After the previous section the archimedean side rests on three things.  Two of them —
`NonPrincipalLocalBound` (narrow range, `χ ≠ 1`) and `WideTwistSmall` (wide range, any `χ`) — are
bounds on the *same* object `‖twistedPrimeSum X χ t‖`, differing only in which corner of the
`(χ, t)` box they cover.  Together they are exactly: **the twisted prime sum has a saving
everywhere except the principal-character narrow corner**, which is the corner
`UniformResonantMass` already handles.  So the honest ledger is `UniformResonantMass` + ONE named
bound.

Why the corner cannot be absorbed too: at `χ = 1`, `t = 0` the twisted prime sum *is*
`∑_{p ≤ X²} 1/p = log log X + O(1)`, so no `κ > 0` saving holds there — the resonance count,
which uses the multiplier `z` and not cancellation among primes, is genuinely needed for it.

Why this statement is not cheaper than it looks: it subsumes prime equidistribution in
progressions with uniformity in the modulus.  Taking `t = 0` and `χ` non-principal, a saving
`κ log log X` on `∑_{p ≤ Y} χ̄(p)/p` uniformly for `q ≤ (log X)^{1/125}` is Siegel–Walfisz-strength;
mathlib's `DirichletCharacter.LFunction_ne_zero_of_one_le_re` is qualitative and supplies no rate,
so this is a genuine debt and is disclosed as one. -/

/-- **The one remaining archimedean debt.**  A saving on the twisted prime sum off the
principal-character narrow corner: for `χ ≠ 1` (any admissible twist), or for any `χ` with a wide
twist.  `UniformResonantMass` covers the excluded corner. -/
def TwistedPrimeSumSmall (κ C : ℝ) : Prop :=
  ∀ X : ℝ, 3 ≤ X → ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
    (q : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) →
    ∀ t : ℝ, |t| ≤ X ^ 2 → (χ ≠ 1 ∨ Real.log X ^ ((1 : ℝ) / 125) < |t|) →
      ‖twistedPrimeSum X χ t‖ ≤ (1 - κ) * Real.log (Real.log X) + C

theorem narrow_twist_le_sq {X t : ℝ} (hX : 3 ≤ X) (ht : |t| ≤ Real.log X ^ ((1 : ℝ) / 125)) :
    |t| ≤ X ^ 2 := by
  have hX0 : (0 : ℝ) < X := by linarith
  have h1 : Real.log X ≤ X := by
    have := Real.log_le_sub_one_of_pos hX0; linarith
  have hlog1 : 1 < Real.log X := one_lt_log_of_three_le hX
  have h2 : Real.log X ^ ((1 : ℝ) / 125) ≤ Real.log X := by
    have := Real.rpow_le_rpow_of_exponent_le hlog1.le (show (1:ℝ)/125 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at this
  nlinarith

theorem nonPrincipalTwistSmall_of_saving {κ C : ℝ} (h : TwistedPrimeSumSmall κ C) :
    NonPrincipalTwistSmall κ C := fun X hX q χ hne hqX t ht =>
  h X hX q χ hqX t (narrow_twist_le_sq hX ht) (Or.inl hne)

theorem wideTwistSmall_of_saving {κ C : ℝ} (h : TwistedPrimeSumSmall κ C) :
    WideTwistSmall κ C := fun X hX q χ hqX t hwide ht =>
  h X hX q χ hqX t ht (Or.inr hwide)

/-- **`FaithfulArchLower` on TWO inputs.**  `UniformResonantMass` (the principal-character narrow
corner, already the route's input) and `TwistedPrimeSumSmall` (everything else).  The
`h'`-uniformity of the constant is discharged by `exists_uniform_narrow_const`. -/
theorem faithfulArchLower_of_urm_of_saving {b : ℕ} (hb : 2 ≤ b) (hURM : UniformResonantMass)
    {κ₀ C₀ : ℝ} (hκ₀ : 0 < κ₀) (hC₀ : 0 ≤ C₀) (hsav : TwistedPrimeSumSmall κ₀ C₀) :
    ∃ C : ℝ, FaithfulArchLower b (C + Erdos67b.PrimeEstimates.mertensBound) := by
  have hkp := kappaDepth_pos hb
  have hmin0 : 0 ≤ min (Real.pi / (b : ℝ)) ((1 : ℝ) / 256) :=
    le_min (by positivity) (by norm_num)
  have hminle : min (Real.pi / (b : ℝ)) ((1 : ℝ) / 256) ≤ 1 / 256 := min_le_right _ _
  have hk1 : kappaDepth b ≤ 1 := by rw [kappaDepth]; nlinarith
  set κ : ℝ := min (kappaDepth b) κ₀ / 2 with hκdef
  have hκ0 : 0 < κ := by
    have : 0 < min (kappaDepth b) κ₀ := lt_min hkp hκ₀
    simp only [hκdef]; linarith
  have hκ1 : κ ≤ 1 := by
    have : min (kappaDepth b) κ₀ ≤ kappaDepth b := min_le_left _ _
    simp only [hκdef]; linarith
  have hpt : ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') →
      ∃ C : ℝ, NarrowTwistSmall (depthRoot b h' 0) κ C := by
    intro h' hnd
    have hz : ‖depthRoot b h' 0‖ = 1 := norm_ee_real _
    have hz1 : depthRoot b h' 0 ≠ 1 := by
      intro hone
      have hge := resEps_depthRoot_ge hb hnd
      rw [hone] at hge
      simp only [resEps, Complex.arg_one, abs_zero] at hge
      have : 0 < Real.pi / (b : ℝ) := by positivity
      linarith
    obtain ⟨Ct, htriv0⟩ := narrowTwistSmallTriv_of_uniformResonantMass hURM hz hz1
    set κ' : ℝ := min (kappaDepth b) κ₀ with hκ'
    have hκ'0 : 0 < κ' := lt_min hkp hκ₀
    have hκ'1 : κ' ≤ 1 := le_trans (min_le_left _ _) hk1
    set C : ℝ := max Ct C₀ with hC
    have hC0 : 0 ≤ C := le_trans hC₀ (le_max_right Ct C₀)
    have htriv : NarrowTwistSmallTriv (depthRoot b h' 0) κ' C := by
      refine narrowTwistSmallTriv_mono ?_ (le_max_left _ _) htriv0
      exact le_trans (min_le_left _ _) (ttExponent_depthRoot_ge hb hnd)
    have hnp : NonPrincipalTwistSmall κ' C :=
      nonPrincipalTwistSmall_mono (min_le_right _ _) (le_max_right _ _)
        (nonPrincipalTwistSmall_of_saving hsav)
    exact ⟨_, narrowTwistSmall_of_triv_of_nonPrincipal hz hκ'0 hκ'1 hC0 htriv hnp⟩
  obtain ⟨C1, hC1⟩ := exists_uniform_narrow_const hb hpt
  refine ⟨max C1 C₀, faithfulArchLower_of_twist_small hκ0 hκ1
    (fun h' hnd => narrowTwistSmall_mono le_rfl (le_max_left _ _) (hC1 h' hnd)) ?_⟩
  refine fun X hX q χ hqX t hwide ht => ?_
  have h0 : 0 < Real.log (Real.log X) := logloglog_pos hX
  have hmain := wideTwistSmall_of_saving hsav X hX q χ hqX t hwide ht
  have hκle : κ ≤ κ₀ := by
    have : min (kappaDepth b) κ₀ ≤ κ₀ := min_le_right _ _
    simp only [hκdef]; linarith
  have hCle : C₀ ≤ max C1 C₀ := le_max_right _ _
  nlinarith

/-- **`ConjC3` on TWO archimedean inputs plus the faithful correlation input.**  This is the
tightest honest statement of the C3/MRT reduction to date: `UniformResonantMass` was already the
route's analytic input before the defect was found, so the *entire* cost of stating TT (3.3)
faithfully is the single named bound `TwistedPrimeSumSmall`. -/
theorem conjC3_of_geom_input_saving {c₀ θ κ₀ C₀ : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1)
    (m : ℕ)
    (hin : ∀ A : ℝ, 0 < A → ∀ b : ℕ, 3 ≤ b → ∀ K,
      KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K)
    (hURM : UniformResonantMass) (hκ₀ : 0 < κ₀) (hC₀ : 0 ≤ C₀)
    (hsav : TwistedPrimeSumSmall κ₀ C₀) :
    ConjC3 := by
  refine conjC3_of_weylLambertTwist fun b hb => ?_
  obtain ⟨C, hC⟩ := faithfulArchLower_of_urm_of_saving (by omega : 2 ≤ b) hURM hκ₀ hC₀ hsav
  exact weylLambertTwist_of_geom_input_at hb hc₀ hθ0 hθ m
    (hin _ (Real.exp_pos _) b hb) (archSupply_of_faithfulArchLower hC)

/-- The excluded corner is genuinely excluded: at `χ = 1`, `t = 0` the twisted prime sum equals
the full prime reciprocal mass, so `TwistedPrimeSumSmall` would be FALSE if the corner were
included.  (Guard: the statement above is not an accidental over-reach.) -/
theorem twistedPrimeSum_principal_zero (X : ℝ) :
    twistedPrimeSum X (1 : DirichletCharacter ℂ 1) 0
      = ((Finset.range (⌈X ^ 2⌉₊ + 1)).filter Nat.Prime).sum (fun p => ((p : ℂ))⁻¹) := by
  rw [twistedPrimeSum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h1 : (starRingEnd ℂ) ((1 : DirichletCharacter ℂ 1) ((p : ℕ) : ZMod 1)) = 1 := by
    rw [Subsingleton.elim ((p : ℕ) : ZMod 1) 1, map_one, map_one]
  rw [h1, one_mul]
  norm_num

#print axioms nonPrincipalTwistSmall_of_saving
#print axioms wideTwistSmall_of_saving
#print axioms faithfulArchLower_of_urm_of_saving
#print axioms conjC3_of_geom_input_saving
#print axioms twistedPrimeSum_principal_zero


/-! ### Eliminating the multiplier `z` — the `b`-th power reduction

The archimedean obligation carries two unknowns: the depth root `z` (a `b`-th root of unity `≠ 1`)
and the pair `(χ, t)`.  The multiplier can be removed outright.  For unimodular `w`,

    1 − w^b = (1 − w)(1 + w + ⋯ + w^{b−1})    ⟹    ‖1 − w^b‖ ≤ b‖1 − w‖,

and `‖1 − u‖² = 2 − 2 Re u` on the unit circle, so `1 − Re(w^b) ≤ b²(1 − Re w)`.  Applying this
with `w = z χ̄(p) p^{−it}` and using `z^b = 1` kills `z`:

    ttPretentiousSumChar 1 X (χ^b) (b t) ≤ b² · ttPretentiousSumChar (zOmegaNat z) X χ t.

So the whole archimedean debt reduces to: **the constant function `1` is non-pretentious to
`χ^b(n) n^{ibt}`**, i.e. the case `z = 1` of the same problem, with the character raised to the
`b`-th power and the twist scaled.  The degenerate case is exactly `χ^b = 1` and `t = 0`, where
the right-hand side is `0` and the inequality says nothing — and that is the case where `χ` has
order dividing `b`, i.e. `χ` takes `b`-th-root-of-unity values.  Recorded in `PENDING_WORK`: for
`χ` of order `d ≥ 3` a Brun–Titchmarsh upper bound on the bad coset gives `2/d ≤ 2/3 < 1`, which
is a saving; `d = 2` (real `χ`, `z = −1`, `b` even) is the Siegel-zero case and is the genuine
hard core. -/

theorem normSq_one_sub_of_norm_one {u : ℂ} (hu : ‖u‖ = 1) :
    Complex.normSq (1 - u) = 2 - 2 * u.re := by
  have h2 : Complex.normSq u = 1 := by
    rw [Complex.normSq_eq_norm_sq, hu]; norm_num
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im] at h2 ⊢
  nlinarith [h2]

/-- `‖1 − w^b‖ ≤ b‖1 − w‖` for `‖w‖ ≤ 1`, from the geometric factorisation. -/
theorem norm_one_sub_pow_le {w : ℂ} (hw : ‖w‖ ≤ 1) (b : ℕ) :
    ‖1 - w ^ b‖ ≤ (b : ℝ) * ‖1 - w‖ := by
  have hfac : 1 - w ^ b = (∑ i ∈ Finset.range b, w ^ i) * (1 - w) :=
    (geom_sum_mul_neg w b).symm
  rw [hfac, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine le_trans (norm_sum_le _ _) ?_
  have hb : ∀ i ∈ Finset.range b, ‖w ^ i‖ ≤ (1 : ℝ) := by
    intro i _
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hw
  refine le_trans (Finset.sum_le_sum hb) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- **The pointwise `b`-th power inequality.**  `1 − Re(w^b) ≤ b²(1 − Re w)` on the unit
circle. -/
theorem one_sub_re_pow_le {w : ℂ} (hw : ‖w‖ = 1) (b : ℕ) :
    1 - (w ^ b).re ≤ (b : ℝ) ^ 2 * (1 - w.re) := by
  have hwb : ‖w ^ b‖ = 1 := by rw [norm_pow, hw, one_pow]
  have h1 : Complex.normSq (1 - w ^ b) = 2 - 2 * (w ^ b).re := normSq_one_sub_of_norm_one hwb
  have h2 : Complex.normSq (1 - w) = 2 - 2 * w.re := normSq_one_sub_of_norm_one hw
  have hn := norm_one_sub_pow_le hw.le b
  have hsq : ‖1 - w ^ b‖ ^ 2 ≤ ((b : ℝ) * ‖1 - w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, h1, h2] at hsq
  linarith

/-- **The `z`-free reduction.**  For a `b`-th root of unity `z`, the faithful pretentious sum of
`zOmegaNat z` at `(χ, t)` dominates `b^{-2}` times the pretentious sum of the CONSTANT function
`1` at `(χ^b, b t)`.  The multiplier `z` has disappeared. -/
theorem ttPretentiousSumChar_pow_le {b : ℕ} (hb : 0 < b) {z : ℂ} (hz : ‖z‖ = 1)
    (hzb : z ^ b = 1) (X t : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ttPretentiousSumChar (fun _ => (1 : ℂ)) X (χ ^ b) ((b : ℝ) * t)
      ≤ (b : ℝ) ^ 2 * ttPretentiousSumChar (zOmegaNat z) X χ t := by
  classical
  rw [ttPretentiousSumChar, ttPretentiousSumChar, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have hpp : Nat.Prime p := (Finset.mem_filter.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  rw [zOmegaNat_prime hpp]
  have hbone : (1 : ℝ) ≤ (b : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    nlinarith
  set e1 : ℂ := Complex.exp (-(t : ℂ) * Complex.I * (Real.log p : ℂ)) with he1
  set E : ℂ := Complex.exp (-(((b : ℝ) * t : ℝ) : ℂ) * Complex.I * (Real.log p : ℂ)) with hE
  set w : ℂ := z * (starRingEnd ℂ) (χ (p : ZMod q)) * e1 with hw
  have hEpow : E = e1 ^ b := by
    rw [hE, he1, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hchi : (starRingEnd ℂ) ((χ ^ b) (p : ZMod q))
      = ((starRingEnd ℂ) (χ (p : ZMod q))) ^ b := by
    rw [MulChar.pow_apply' _ hb.ne', map_pow]
  have hnum : 1 - ((1 : ℂ) * (starRingEnd ℂ) ((χ ^ b) (p : ZMod q)) * E).re
      ≤ (b : ℝ) ^ 2 * (1 - w.re) := by
    rcases eq_or_ne (χ (p : ZMod q)) 0 with h0 | hne
    · have hL : ((1 : ℂ) * (starRingEnd ℂ) ((χ ^ b) (p : ZMod q)) * E).re = 0 := by
        rw [hchi, h0]; simp [hb.ne']
      have hR : w.re = 0 := by rw [hw, h0]; simp
      rw [hL, hR]; linarith
    · have hqu : IsUnit ((p : ℕ) : ZMod q) := by
        by_contra hc
        exact hne (MulChar.map_nonunit _ hc)
      have hnorm : ‖χ ((p : ℕ) : ZMod q)‖ = 1 := by
        have h := DirichletCharacter.unit_norm_eq_one χ hqu.unit
        rwa [IsUnit.unit_spec] at h
      have hnorme1 : ‖e1‖ = 1 := by
        have he1' : e1 = Complex.exp (((-t * Real.log p : ℝ) : ℂ) * Complex.I) := by
          rw [he1]; push_cast; ring_nf
        rw [he1', Complex.norm_exp_ofReal_mul_I]
      have hnormw : ‖w‖ = 1 := by
        rw [hw, norm_mul, norm_mul, hz, RCLike.norm_conj, hnorm, hnorme1]; ring
      have hpow : (1 : ℂ) * (starRingEnd ℂ) ((χ ^ b) (p : ZMod q)) * E = w ^ b := by
        rw [one_mul, hchi, hEpow, hw, mul_pow, mul_pow, hzb, one_mul]
      rw [hpow]
      exact one_sub_re_pow_le hnormw b
  rw [mul_div_assoc']
  gcongr

#print axioms one_sub_re_pow_le
#print axioms ttPretentiousSumChar_pow_le


/-- `depthRoot b h' 0` is a `b`-th root of unity: `ee(h'/b)^b = ee(h') = 1`. -/
theorem depthRoot_pow_eq_one {b : ℕ} (hb : 0 < b) (h' : ℤ) :
    depthRoot b h' 0 ^ b = 1 := by
  have hb0 : ((b : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  rw [depthRoot, ee, ← Complex.exp_nat_mul]
  rw [show (b : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (((h' : ℝ) / (b : ℝ) ^ (0 + 1) : ℝ) : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I * ((h' : ℝ) : ℂ) by
    have hbc : ((b : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
    push_cast
    field_simp]
  exact (ee_intCast_eq_one h' : ee (((h' : ℝ) : ℂ)) = 1)

/-- **The `z`-free archimedean debt.**  The CONSTANT function `1` is non-pretentious to
`ψ(n)n^{iτ}` whenever `(ψ, τ) ≠ (1, 0)`.  This is TT (3.3) at `g = 1`; the power reduction
(`ttPretentiousSumChar_pow_le`) transfers it to every `b`-th root of unity multiplier. -/
def OneNonPretentious (κ C : ℝ) : Prop :=
  ∀ X : ℝ, 3 ≤ X → ∀ (q : ℕ) (ψ : DirichletCharacter ℂ q) (τ : ℝ),
    (q : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) → (ψ ≠ 1 ∨ τ ≠ 0) →
      κ * Real.log (Real.log X) - C ≤ ttPretentiousSumChar (fun _ => (1 : ℂ)) X ψ τ

/-- **The degenerate corner the power reduction cannot reach**: `χ^b = 1` and `t = 0`, i.e. `χ`
has order dividing `b`, so it takes `b`-th-root-of-unity values — exactly the values the depth
root takes.  Here `ttPretentiousSumChar 1 X (χ^b) 0 = 0` and the reduction is vacuous, so the
multiplier `z` must be used.  For `χ` of order `d ≥ 3` a Brun–Titchmarsh upper bound on the bad
coset `{χ = z}` gives a `2/d ≤ 2/3` saving; `d = 2` (real `χ`, `z = −1`, `b` even) is the
Siegel-zero case and is the hard core of the whole archimedean debt. -/
def RootOrderCase (b : ℕ) (κ C : ℝ) : Prop :=
  ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') → ∀ X : ℝ, 3 ≤ X → ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
    (q : ℝ) ≤ Real.log X ^ ((1 : ℝ) / 125) → χ ^ b = 1 →
      κ * Real.log (Real.log X) - C
        ≤ ttPretentiousSumChar (zOmegaNat (depthRoot b h' 0)) X χ 0

/-- **`FaithfulArchLower` from the `z`-free debt plus the degenerate corner.**  The multiplier
`z = depthRoot b h' 0` is eliminated everywhere except on `{χ^b = 1, t = 0}`, so the archimedean
obligation splits into a statement with **no `b` and no `z` in it** (`OneNonPretentious`) and the
root-order corner (`RootOrderCase b`).  The `h'`-uniformity is automatic: both constants are
already independent of `h'`. -/
theorem faithfulArchLower_of_oneNonPretentious {b : ℕ} (hb : 2 ≤ b) {κ C κ' C' : ℝ}
    (hκ : 0 < κ) (hC : 0 ≤ C) (hκ' : 0 < κ') (hC' : 0 ≤ C')
    (hone : OneNonPretentious κ C) (hroot : RootOrderCase b κ' C') :
    FaithfulArchLower b (max C C' + 1) := by
  have hb0 : 0 < b := by omega
  have hbR : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb0
  have hbsq : (1 : ℝ) ≤ (b : ℝ) ^ 2 := by nlinarith
  intro h' hnd
  set z : ℂ := depthRoot b h' 0 with hzdef
  have hz : ‖z‖ = 1 := norm_ee_real _
  have hzb : z ^ b = 1 := depthRoot_pow_eq_one hb0 h'
  refine ⟨min (min κ κ') 1 / (b : ℝ) ^ 2, by positivity, ?_, fun X hX q χ hq t ht => ?_⟩
  · have h1 : min (min κ κ') 1 ≤ 1 := min_le_right _ _
    rw [div_le_one (by positivity)]
    linarith
  · set μ : ℝ := min (min κ κ') 1 with hμ
    have hμ0 : 0 < μ := lt_min (lt_min hκ hκ') (by norm_num)
    have hμκ : μ ≤ κ := le_trans (min_le_left _ _) (min_le_left _ _)
    have hμκ' : μ ≤ κ' := le_trans (min_le_left _ _) (min_le_right _ _)
    have hll : 0 < Real.log (Real.log X) := logloglog_pos hX
    have hCm : C ≤ max C C' := le_max_left _ _
    have hCm' : C' ≤ max C C' := le_max_right _ _
    by_cases hdeg : χ ^ b = 1 ∧ t = 0
    · -- the degenerate corner: use the multiplier
      obtain ⟨hχb, ht0⟩ := hdeg
      have h := hroot h' hnd X hX q χ hq hχb
      rw [ht0]
      have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
      have hle : μ / (b : ℝ) ^ 2 * Real.log (Real.log X) ≤ κ' * Real.log (Real.log X) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hb2]
        have h1 : μ * Real.log (Real.log X) ≤ κ' * Real.log (Real.log X) :=
          mul_le_mul_of_nonneg_right hμκ' hll.le
        have h2 : κ' * Real.log (Real.log X) * 1 ≤ κ' * Real.log (Real.log X) * (b : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hbsq (mul_nonneg hκ'.le hll.le)
        rw [mul_one] at h2
        linarith
      linarith [hle, h, hCm']
    · -- the generic case: the multiplier is eliminated
      have hor : (χ ^ b ≠ 1 ∨ ((b : ℝ) * t) ≠ 0) := by
        rcases Classical.em (χ ^ b = 1) with h1 | h1
        · refine Or.inr ?_
          have ht0 : t ≠ 0 := fun hc => hdeg ⟨h1, hc⟩
          have : ((b : ℝ)) ≠ 0 := by positivity
          exact mul_ne_zero this ht0
        · exact Or.inl h1
      have hlow := hone X hX q (χ ^ b) ((b : ℝ) * t) hq hor
      have hred := ttPretentiousSumChar_pow_le hb0 hz hzb X t χ
      have hstep : μ * Real.log (Real.log X) - (max C C' + 1)
          ≤ ttPretentiousSumChar (fun _ => (1 : ℂ)) X (χ ^ b) ((b : ℝ) * t) := by
        nlinarith
      have hdiv : μ / (b : ℝ) ^ 2 * Real.log (Real.log X) - (max C C' + 1)
          ≤ (1 / (b : ℝ) ^ 2)
            * (ttPretentiousSumChar (fun _ => (1 : ℂ)) X (χ ^ b) ((b : ℝ) * t)) := by
        have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
        rw [one_div, inv_mul_eq_div, le_div_iff₀ hb2]
        have hmul : μ * Real.log (Real.log X) - (max C C' + 1) * (b : ℝ) ^ 2
            ≤ μ * Real.log (Real.log X) - (max C C' + 1) := by nlinarith [hC, hC']
        have hexp : (μ / (b : ℝ) ^ 2 * Real.log (Real.log X) - (max C C' + 1)) * (b : ℝ) ^ 2
            = μ * Real.log (Real.log X) - (max C C' + 1) * (b : ℝ) ^ 2 := by
          field_simp
        rw [hexp]
        linarith
      have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
      have hfin : (1 / (b : ℝ) ^ 2)
          * (ttPretentiousSumChar (fun _ => (1 : ℂ)) X (χ ^ b) ((b : ℝ) * t))
            ≤ ttPretentiousSumChar (zOmegaNat z) X χ t := by
        rw [one_div, inv_mul_eq_div, div_le_iff₀ hb2]
        linarith [hred]
      linarith

#print axioms depthRoot_pow_eq_one
#print axioms faithfulArchLower_of_oneNonPretentious


/-- **`ConjC3` on the `z`-free archimedean debt.**  The archimedean side is now: TT (3.3) for the
CONSTANT function `1` (no base, no root of unity, no `h'`) plus the root-order corner
`RootOrderCase b`.  Note `OneNonPretentious` is *independent of the base* `b`, so a single
analytic statement serves every base at once — which the resonance route could not do
(its constant degrades like `π/b`). -/
theorem conjC3_of_geom_input_zfree {c₀ θ κ C κ' C' : ℝ} (hc₀ : 0 < c₀) (hθ0 : 0 < θ) (hθ : θ < 1)
    (m : ℕ)
    (hin : ∀ A : ℝ, 0 < A → ∀ b : ℕ, 3 ≤ b → ∀ K,
      KPointNoExcAtWith A (cKgeom c₀ θ b) (CstKdeg m) K)
    (hκ : 0 < κ) (hC : 0 ≤ C) (hκ' : 0 < κ') (hC' : 0 ≤ C')
    (hone : OneNonPretentious κ C)
    (hroot : ∀ b : ℕ, 3 ≤ b → RootOrderCase b κ' C') :
    ConjC3 := by
  refine conjC3_of_weylLambertTwist fun b hb => ?_
  have h := faithfulArchLower_of_oneNonPretentious (by omega : 2 ≤ b) hκ hC hκ' hC' hone
    (hroot b hb)
  exact weylLambertTwist_of_geom_input_at hb hc₀ hθ0 hθ m
    (hin _ (Real.exp_pos _) b hb) (archSupply_of_faithfulArchLower h)

#print axioms conjC3_of_geom_input_zfree


/-! ### The narrow debt drops from Siegel strength to the classical `L(1,χ) ≫ q^{-1/2}`

`NonPrincipalLocalBound` asked for a `log log (q(2+|t|))` bound — the sharp `log L(1+it,χ)`
estimate, which needs the non-vanishing of `L` on the 1-line with a rate.  That is far more than
the chain consumes.  In TT's range the conductor and twist satisfy
`q, |t| ≤ (log X)^{1/125}`, so

    log(q + 2) + log(2 + |t|) ≤ 2 log 3 + (2/125) · log log X,

which is a *fraction* `2/125` of `log log X`.  So a bound of size `log q + log(2+|t|)` — a whole
exponential weaker than `log log (q(2+|t|))` — already gives the saving, with
`κ = 1 − 2D/125` close to `1`.

**Why this matters for the ledger.**  At `t = 0` the `log`-sized bound is classical and
Siegel-free: `|∑_{p≤Y} χ(p)/p| ≤ log(1/L(1,χ)) + O(1) ≤ (1/2) log q + O(1)` using the elementary
`L(1,χ) ≫ q^{-1/2}`, no Siegel–Walfisz and no exceptional-character exclusion.  The `1/125` in
TT's `Q` is exactly what makes the crude bound sufficient.  The genuinely open part of the
archimedean debt is therefore the *twist* dependence at large `|t|`, not the conductor. -/

/-- **The weakened narrow debt**: a `log`-sized bound on the twisted prime sum, rather than the
`log log` bound of `NonPrincipalLocalBound`.  At `t = 0` this is the classical
`L(1,χ) ≫ q^{-1/2}`. -/
def CharPrimeSumLogQ (D : ℝ) : Prop :=
  ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ X t : ℝ, 3 ≤ X →
    |t| ≤ Real.log X ^ ((1 : ℝ) / 125) →
      ‖twistedPrimeSum X χ t‖ ≤ D * (Real.log ((q : ℝ) + 2) + Real.log (2 + |t|) + 1)

/-- `log(2 + r) ≤ log 3 + (1/125) log u` when `0 ≤ r ≤ u^{1/125}` and `1 < u`. -/
theorem log_two_add_le {r u : ℝ} (hr : 0 ≤ r) (hu : 1 < u) (hru : r ≤ u ^ ((1 : ℝ) / 125)) :
    Real.log (2 + r) ≤ Real.log 3 + (1 / 125) * Real.log u := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hp1 : (1 : ℝ) ≤ u ^ ((1 : ℝ) / 125) := Real.one_le_rpow hu.le (by norm_num)
  have hle : 2 + r ≤ 3 * u ^ ((1 : ℝ) / 125) := by nlinarith
  have h1 : Real.log (2 + r) ≤ Real.log (3 * u ^ ((1 : ℝ) / 125)) :=
    Real.log_le_log (by linarith) hle
  rwa [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hu0] at h1

/-- **The reduction.**  A `log`-sized bound suffices, with saving `κ = 1 − 2D/125`. -/
theorem nonPrincipalTwistSmall_of_logQBound {D : ℝ} (hD : 0 < D) (hD125 : 2 * D < 125)
    (h : CharPrimeSumLogQ D) :
    NonPrincipalTwistSmall (1 - 2 * D / 125) (D * (2 * Real.log 3 + 1)) := by
  intro X hX q χ hne hqX t ht
  have hu1 : 1 < Real.log X := one_lt_log_of_three_le hX
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have h1 : Real.log ((q : ℝ) + 2) ≤ Real.log 3 + (1 / 125) * Real.log (Real.log X) := by
    have := log_two_add_le hq0 hu1 hqX
    rwa [add_comm (2 : ℝ) ((q : ℝ))] at this
  have h2 : Real.log (2 + |t|) ≤ Real.log 3 + (1 / 125) * Real.log (Real.log X) :=
    log_two_add_le (abs_nonneg t) hu1 ht
  have hmain := h q χ hne X t hX ht
  have hstep : D * (Real.log ((q : ℝ) + 2) + Real.log (2 + |t|) + 1)
      ≤ (2 * D / 125) * Real.log (Real.log X) + D * (2 * Real.log 3 + 1) := by
    have hll : 0 < Real.log (Real.log X) := logloglog_pos hX
    have hsum : Real.log ((q : ℝ) + 2) + Real.log (2 + |t|) + 1
        ≤ (2 / 125) * Real.log (Real.log X) + (2 * Real.log 3 + 1) := by linarith
    have hmul : D * (Real.log ((q : ℝ) + 2) + Real.log (2 + |t|) + 1)
        ≤ D * ((2 / 125) * Real.log (Real.log X) + (2 * Real.log 3 + 1)) :=
      mul_le_mul_of_nonneg_left hsum hD.le
    have hexp : D * ((2 / 125) * Real.log (Real.log X) + (2 * Real.log 3 + 1))
        = (2 * D / 125) * Real.log (Real.log X) + D * (2 * Real.log 3 + 1) := by ring
    rw [hexp] at hmul
    linarith
  linarith

/-- **`FaithfulArchLower` on the WEAKENED narrow debt.**  `UniformResonantMass` (principal narrow
corner) + `CharPrimeSumLogQ` (non-principal narrow range, `log`-sized, classical at `t = 0`) +
`WideTwistSmall` (the wide twist range, the genuinely open part). -/
theorem faithfulArchLower_of_urm_of_logQ {b : ℕ} (hb : 2 ≤ b) (hURM : UniformResonantMass)
    {D : ℝ} (hD : 0 < D) (hD125 : 2 * D < 125) (hlog : CharPrimeSumLogQ D)
    (hwide : ∀ κ C : ℝ, 0 < κ → 0 ≤ C → WideTwistSmall κ C) :
    ∃ C : ℝ, FaithfulArchLower b (C + Erdos67b.PrimeEstimates.mertensBound) := by
  have hkp := kappaDepth_pos hb
  have hmin0 : 0 ≤ min (Real.pi / (b : ℝ)) ((1 : ℝ) / 256) :=
    le_min (by positivity) (by norm_num)
  have hminle : min (Real.pi / (b : ℝ)) ((1 : ℝ) / 256) ≤ 1 / 256 := min_le_right _ _
  have hk1 : kappaDepth b ≤ 1 := by rw [kappaDepth]; nlinarith
  set κ₀ : ℝ := 1 - 2 * D / 125 with hκ₀def
  have hκ₀ : 0 < κ₀ := by simp only [hκ₀def]; linarith
  set C₀ : ℝ := D * (2 * Real.log 3 + 1) with hC₀def
  have hC₀ : 0 ≤ C₀ := by
    have h3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    simp only [hC₀def]; positivity
  have hnp : NonPrincipalTwistSmall κ₀ C₀ := nonPrincipalTwistSmall_of_logQBound hD hD125 hlog
  set κ : ℝ := min (min (kappaDepth b) κ₀) 1 / 2 with hκdef
  have hm0 : 0 < min (min (kappaDepth b) κ₀) 1 := lt_min (lt_min hkp hκ₀) (by norm_num)
  have hκ0 : 0 < κ := by simp only [hκdef]; linarith
  have hκ1 : κ ≤ 1 := by
    have : min (min (kappaDepth b) κ₀) 1 ≤ 1 := min_le_right _ _
    simp only [hκdef]; linarith
  have hpt : ∀ h' : ℤ, ¬ ((b : ℤ) ∣ h') →
      ∃ C : ℝ, NarrowTwistSmall (depthRoot b h' 0) κ C := by
    intro h' hnd
    have hz : ‖depthRoot b h' 0‖ = 1 := norm_ee_real _
    have hz1 : depthRoot b h' 0 ≠ 1 := by
      intro hone
      have hge := resEps_depthRoot_ge hb hnd
      rw [hone] at hge
      simp only [resEps, Complex.arg_one, abs_zero] at hge
      have : 0 < Real.pi / (b : ℝ) := by positivity
      linarith
    obtain ⟨Ct, htriv0⟩ := narrowTwistSmallTriv_of_uniformResonantMass hURM hz hz1
    set κ' : ℝ := min (min (kappaDepth b) κ₀) 1 with hκ'
    have hκ'0 : 0 < κ' := hm0
    have hκ'1 : κ' ≤ 1 := min_le_right _ _
    set C : ℝ := max Ct C₀ with hC
    have hC0 : 0 ≤ C := le_trans hC₀ (le_max_right Ct C₀)
    have htriv : NarrowTwistSmallTriv (depthRoot b h' 0) κ' C := by
      refine narrowTwistSmallTriv_mono ?_ (le_max_left _ _) htriv0
      exact le_trans (le_trans (min_le_left _ _) (min_le_left _ _))
        (ttExponent_depthRoot_ge hb hnd)
    have hnp' : NonPrincipalTwistSmall κ' C :=
      nonPrincipalTwistSmall_mono (le_trans (min_le_left _ _) (min_le_right _ _))
        (le_max_right _ _) hnp
    exact ⟨_, narrowTwistSmall_of_triv_of_nonPrincipal hz hκ'0 hκ'1 hC0 htriv hnp'⟩
  obtain ⟨C1, hC1⟩ := exists_uniform_narrow_const hb hpt
  refine ⟨max C1 C₀, faithfulArchLower_of_twist_small hκ0 hκ1
    (fun h' hnd => narrowTwistSmall_mono le_rfl (le_max_left _ _) (hC1 h' hnd)) ?_⟩
  have hC1' : (0 : ℝ) ≤ max C1 C₀ := le_trans hC₀ (le_max_right _ _)
  exact hwide κ (max C1 C₀) hκ0 hC1'

#print axioms nonPrincipalTwistSmall_of_logQBound
#print axioms faithfulArchLower_of_urm_of_logQ


#print axioms ttPretentiousSumChar_eq
#print axioms ttPretentiousSumChar_ge
#print axioms archSupply_of_faithfulArchLower
#print axioms conjC3_of_geom_input_lower
#print axioms faithfulArchLower_of_twist_small
#print axioms narrowTwistSmallTriv_of_uniformResonantMass
#print axioms resEps_depthRoot_ge
#print axioms ttExponent_depthRoot_ge

end CastingOut

end NormalNumbers
