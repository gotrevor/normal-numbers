/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamSumsNormal

/-!
# Mahler shifts for prime-class Stoneham series

The identity `alpha_(B^c,c) = c * alpha_(B,c) - B^(-c)` moves a factor of `c` from the
base exponent into the coefficient.  Iterating it is the algebraic normalization used in the
dependent half of the one-prime-class theorem: prime-power factors of the exponents can be
removed at the cost of a finite base-`B` rational correction.
-/

namespace NormalNumbers.StonehamPrimeClass

open Finset

/-! ### Canonical exponent normalization -/

/-- Number of full `p^s` blocks in the `p`-part of an exponent. -/
def primeClassShiftCount (p s m : ℕ) : ℕ :=
  m.factorization p / s

/-- The exponent left after removing all full `p^s` blocks.  Its `p`-adic
valuation is the remainder modulo `s`, while its prime-to-`p` part is unchanged. -/
def primeClassReducedExponent (p s m : ℕ) : ℕ :=
  ordCompl[p] m * p ^ (m.factorization p % s)

/-- Canonical factorization of an exponent into its reduced part and full
`p^s` blocks. -/
lemma primeClassReducedExponent_mul_pow (p s m : ℕ) :
    primeClassReducedExponent p s m * (p ^ s) ^ primeClassShiftCount p s m = m := by
  rw [primeClassReducedExponent, primeClassShiftCount, ← pow_mul]
  calc
    ordCompl[p] m * p ^ (m.factorization p % s) * p ^ (s * (m.factorization p / s)) =
        ordCompl[p] m * p ^ m.factorization p := by
      rw [mul_assoc, ← pow_add, Nat.mod_add_div]
    _ = m := by
      rw [mul_comm]
      exact Nat.ordProj_mul_ordCompl_eq_self m p

/-- Removing full `p^s` blocks does not change the phase at a primitive
`ord_p(b)`-th root: the order divides `p - 1`, hence every power of `p` is
congruent to one modulo that order. -/
lemma primitiveRoot_pow_primeClassReducedExponent
    (p b s m : ℕ) (hp : p.Prime) (hbp : Nat.Coprime b p)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p))) :
    ζ ^ primeClassReducedExponent p s m = ζ ^ m := by
  letI : Fact p.Prime := ⟨hp⟩
  let d := orderOf (b : ZMod p)
  have hbne : (b : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hp.coprime_iff_not_dvd.mp hbp.symm
  have hd : d ∣ p - 1 := by
    dsimp [d]
    exact ZMod.orderOf_dvd_card_sub_one hbne
  have hd0 : d ≠ 0 := by
    dsimp [d]
    exact orderOf_ne_zero_iff.mpr ((ZMod.isUnit_iff_coprime b p).mpr hbp).isOfFinOrder
  have hpmod : p ≡ 1 [MOD d] := by
    exact (Nat.modEq_of_dvd' hp.one_lt.le hd).symm
  have hpowmod : p ^ m.factorization p ≡ p ^ (m.factorization p % s) [MOD d] := by
    calc
      p ^ m.factorization p ≡ 1 ^ m.factorization p [MOD d] := hpmod.pow _
      _ ≡ 1 ^ (m.factorization p % s) [MOD d] := by
        simpa only [one_pow] using (Nat.ModEq.refl (n := d) 1)
      _ ≡ p ^ (m.factorization p % s) [MOD d] := (hpmod.pow _).symm
  have hmod : m ≡ primeClassReducedExponent p s m [MOD d] := by
    simpa only [primeClassReducedExponent, mul_comm,
      Nat.ordProj_mul_ordCompl_eq_self] using hpowmod.mul_left (ordCompl[p] m)
  have hfin : IsOfFinOrder ζ := hζ.isOfFinOrder hd0
  rw [hfin.pow_eq_pow_iff_modEq]
  rw [← hζ.eq_orderOf]
  exact hmod.symm

/-- Pointwise phase invariance for a whole prime-class family. -/
lemma primitiveRoot_primeClassReducedPowers_eq
    (p b : ℕ) {r : ℕ} (s m : Fin r → ℕ)
    (hp : p.Prime) (hbp : Nat.Coprime b p)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p))) :
    (fun i => ζ ^ primeClassReducedExponent p (s i) (m i)) =
      (fun i => ζ ^ m i) := by
  funext i
  exact primitiveRoot_pow_primeClassReducedExponent p b (s i) (m i) hp hbp ζ hζ

/-- Canonical exponent reduction preserves exactly the linear-independence
criterion in Theorem T-B'. -/
lemma linearIndependent_primeClassReducedPowers_iff
    (p b : ℕ) {r : ℕ} (s m : Fin r → ℕ)
    (hp : p.Prime) (hbp : Nat.Coprime b p)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p))) :
    LinearIndependent ℚ (fun i => ζ ^ primeClassReducedExponent p (s i) (m i)) ↔
      LinearIndependent ℚ (fun i => ζ ^ m i) := by
  rw [primitiveRoot_primeClassReducedPowers_eq p b s m hp hbp ζ hζ]

/-- The one-step Mahler identity for a Stoneham series. -/
theorem stonehamAlpha_pow_base (B c : ℕ) (hB : 1 ≤ B) (hc : 2 ≤ c) :
    stonehamAlpha (B ^ c) c =
      (c : ℝ) * stonehamAlpha B c - 1 / (B : ℝ) ^ c := by
  let f : ℕ → ℝ := fun n =>
    1 / ((c : ℝ) ^ (n + 1) * (B : ℝ) ^ (c ^ (n + 1)))
  have hf : Summable f := by
    simpa only [f] using
      StonehamSumsNormal.summable_stonehamAlpha_term B c hB hc
  have hshift : stonehamAlpha (B ^ c) c = ∑' n, (c : ℝ) * f (n + 1) := by
    unfold stonehamAlpha
    apply tsum_congr
    intro n
    simp only [f]
    have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
    have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
    push_cast
    rw [← pow_mul]
    rw [show c * c ^ (n + 1) = c ^ (n + 1 + 1) by simp only [pow_succ]; ring]
    field_simp
    rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
  have hsplit : stonehamAlpha B c = f 0 + ∑' n, f (n + 1) := by
    simpa only [stonehamAlpha, f, sum_range_one, Nat.zero_add] using
      (hf.sum_add_tsum_nat_add 1).symm
  rw [hshift, tsum_mul_left]
  rw [hsplit]
  simp only [f, zero_add, pow_one]
  have hc0 : (c : ℝ) ≠ 0 := by exact_mod_cast (by omega : c ≠ 0)
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
  field_simp
  ring

/-- Iterating the Mahler identity removes an arbitrary power of the series parameter from the
base.  The displayed finite sum is the complete terminating correction. -/
theorem stonehamAlpha_pow_base_iterate (B c a : ℕ) (hB : 1 ≤ B) (hc : 2 ≤ c) :
    stonehamAlpha (B ^ (c ^ a)) c =
      (c : ℝ) ^ a * stonehamAlpha B c -
        ∑ t ∈ Icc 1 a, (c : ℝ) ^ (a - t) / (B : ℝ) ^ (c ^ t) := by
  induction a with
  | zero => simp
  | succ a ih =>
      have hBc : 1 ≤ B ^ (c ^ a) := one_le_pow₀ hB
      rw [show B ^ (c ^ (a + 1)) = (B ^ (c ^ a)) ^ c by
        rw [pow_succ, pow_mul]]
      rw [stonehamAlpha_pow_base (B ^ (c ^ a)) c hBc hc, ih]
      have hIcc : Icc 1 (a + 1) = insert (a + 1) (Icc 1 a) := by
        ext t
        simp only [mem_Icc, mem_insert]
        omega
      rw [hIcc, sum_insert (by simp)]
      simp only [Nat.sub_self, pow_zero]
      rw [mul_sub, pow_succ]
      have hsum :
          (c : ℝ) * ∑ t ∈ Icc 1 a, (c : ℝ) ^ (a - t) / (B : ℝ) ^ (c ^ t) =
            ∑ t ∈ Icc 1 a,
              (c : ℝ) ^ (a + 1 - t) / (B : ℝ) ^ (c ^ t) := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro t ht
        have ht_le : t ≤ a := (mem_Icc.mp ht).2
        rw [show a + 1 - t = (a - t) + 1 by omega, pow_succ]
        ring
      rw [hsum]
      simp only [Nat.cast_pow]
      rw [show ((B : ℝ) ^ (c ^ a)) ^ c = (B : ℝ) ^ (c ^ (a + 1)) by
        rw [pow_succ, pow_mul]]
      ring

/-- Exponent form of the iterated shift, matching the parameters of `primeClassFamily`.
Thus a factor `(p^s)^a` in an exponent contributes the nonzero coefficient `p^(s*a)` and a
finite terminating correction. -/
theorem stonehamAlpha_exponent_mul_pow (b c u a : ℕ) (hb : 1 ≤ b) (hc : 2 ≤ c) :
    stonehamAlpha (b ^ (u * c ^ a)) c =
      (c : ℝ) ^ a * stonehamAlpha (b ^ u) c -
        ∑ t ∈ Icc 1 a, (c : ℝ) ^ (a - t) / ((b : ℝ) ^ u) ^ (c ^ t) := by
  simpa only [pow_mul, Nat.cast_pow] using
    stonehamAlpha_pow_base_iterate (b ^ u) c a (one_le_pow₀ hb) hc

/-- The canonical prime-class normalization: every exponent is reduced to
`v_p(u) < s`, the removed full blocks become a nonzero coefficient, and the
remaining correction is a finite base-`b` rational sum. -/
theorem stonehamAlpha_primeClass_normalize
    (b p s m : ℕ) (hb : 1 ≤ b) (hp : p.Prime) (hs : 1 ≤ s) :
    stonehamAlpha (b ^ m) (p ^ s) =
      ((p ^ s : ℕ) : ℝ) ^ primeClassShiftCount p s m *
          stonehamAlpha (b ^ primeClassReducedExponent p s m) (p ^ s) -
        ∑ t ∈ Icc 1 (primeClassShiftCount p s m),
          ((p ^ s : ℕ) : ℝ) ^ (primeClassShiftCount p s m - t) /
            ((b : ℝ) ^ primeClassReducedExponent p s m) ^ ((p ^ s) ^ t) := by
  have hc : 2 ≤ p ^ s := by
    have := Nat.one_lt_pow (by omega : s ≠ 0) hp.one_lt
    omega
  conv_lhs =>
    rw [← primeClassReducedExponent_mul_pow p s m]
  exact stonehamAlpha_exponent_mul_pow b (p ^ s)
    (primeClassReducedExponent p s m) (primeClassShiftCount p s m) hb hc

end NormalNumbers.StonehamPrimeClass
