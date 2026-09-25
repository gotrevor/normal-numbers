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
