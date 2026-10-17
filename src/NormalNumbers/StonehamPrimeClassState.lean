/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.StonehamPrimeClassFinite
import NormalNumbers.StonehamPrimeClassMahler

/-!
# State preparation for one prime Stoneham class

This file packages the coefficient change used before the mixed-`s` state argument.  Removing
the full `p ^ s` blocks from an exponent multiplies the corresponding reduced Stoneham series by
a nonzero natural number.  Dividing an integral cyclotomic relation coefficient by that number
therefore gives a nonzero rational coefficient for the original family.  The difference between
the two linear combinations is one explicitly rational finite correction, so normality is
equivalent on the two sides.

The remaining state argument must also account for the geometric history attached to each
parameter `p ^ (s i)` and for inverse Teichmuller phases.  Those factors are deliberately not
folded into the Mahler coefficient defined here.
-/

namespace NormalNumbers.StonehamPrimeClass

open Finset Polynomial

/-- The nonzero multiplier contributed by canonical Mahler exponent reduction. -/
def primeClassMahlerMultiplier (p s m : ℕ) : ℕ :=
  (p ^ s) ^ primeClassShiftCount p s m

/-- Divide a cleared integral relation coefficient by the canonical Mahler multiplier. -/
noncomputable def primeClassInverseMahlerCoefficient
    {r : ℕ} (p : ℕ) (s m : Fin r → ℕ) (a : Fin r → ℤ) : Fin r → ℚ :=
  fun i ↦ (a i : ℚ) / primeClassMahlerMultiplier p (s i) (m i)

/-- The terminating correction in the canonical Mahler identity, recorded over `ℚ`. -/
noncomputable def primeClassMahlerCorrectionRat (b p s m : ℕ) : ℚ :=
  ∑ t ∈ Icc 1 (primeClassShiftCount p s m),
    ((p ^ s : ℕ) : ℚ) ^ (primeClassShiftCount p s m - t) /
      ((b : ℚ) ^ primeClassReducedExponent p s m) ^ ((p ^ s) ^ t)

/-- The single rational correction for a finite inverse-Mahler linear combination. -/
noncomputable def primeClassInverseMahlerCorrection
    {r : ℕ} (b p : ℕ) (s m : Fin r → ℕ) (a : Fin r → ℤ) : ℚ :=
  ∑ i, primeClassInverseMahlerCoefficient p s m a i *
    primeClassMahlerCorrectionRat b p (s i) (m i)

lemma primeClassMahlerMultiplier_pos
    (p s m : ℕ) (hp : p.Prime) : 0 < primeClassMahlerMultiplier p s m := by
  unfold primeClassMahlerMultiplier
  exact pow_pos (pow_pos hp.pos s) _

/-- The inverse coefficient cancels its Mahler multiplier exactly. -/
lemma primeClassInverseMahlerCoefficient_mul
    {r : ℕ} (p : ℕ) (s m : Fin r → ℕ) (a : Fin r → ℤ)
    (hp : p.Prime) (i : Fin r) :
    primeClassInverseMahlerCoefficient p s m a i *
        primeClassMahlerMultiplier p (s i) (m i) = (a i : ℚ) := by
  have hmul : (primeClassMahlerMultiplier p (s i) (m i) : ℚ) ≠ 0 := by
    exact_mod_cast (primeClassMahlerMultiplier_pos p (s i) (m i) hp).ne'
  simp [primeClassInverseMahlerCoefficient, hmul]

/-- A nonzero integral relation remains nonzero after inverse Mahler scaling. -/
lemma primeClassInverseMahlerCoefficient_ne_zero
    {r : ℕ} (p : ℕ) (s m : Fin r → ℕ) (a : Fin r → ℤ)
    (hp : p.Prime) (ha : a ≠ 0) :
    primeClassInverseMahlerCoefficient p s m a ≠ 0 := by
  intro hzero
  apply ha
  funext i
  have hi := congrFun hzero i
  simp only [Pi.zero_apply] at hi
  have hmul := primeClassInverseMahlerCoefficient_mul p s m a hp i
  rw [hi, zero_mul] at hmul
  exact_mod_cast hmul.symm

@[simp] lemma primeClassMahlerCorrectionRat_cast (b p s m : ℕ) :
    ((primeClassMahlerCorrectionRat b p s m : ℚ) : ℝ) =
      ∑ t ∈ Icc 1 (primeClassShiftCount p s m),
        ((p ^ s : ℕ) : ℝ) ^ (primeClassShiftCount p s m - t) /
          ((b : ℝ) ^ primeClassReducedExponent p s m) ^ ((p ^ s) ^ t) := by
  unfold primeClassMahlerCorrectionRat
  push_cast
  rfl

/-- Pointwise inverse-Mahler normalization, with the terminating correction kept rational. -/
lemma stonehamAlpha_inverseMahlerCoefficient
    (b p s m : ℕ) (a : ℤ) (hb : 2 ≤ b) (hp : p.Prime) (hs : 1 ≤ s) :
    ((a : ℚ) / primeClassMahlerMultiplier p s m : ℚ) *
        stonehamAlpha (b ^ m) (p ^ s) =
      (a : ℝ) * stonehamAlpha (b ^ primeClassReducedExponent p s m) (p ^ s) -
        (((a : ℚ) / primeClassMahlerMultiplier p s m) *
          primeClassMahlerCorrectionRat b p s m : ℚ) := by
  have hnorm := stonehamAlpha_primeClass_normalize b p s m (by omega) hp hs
  have hmulQ : ((a : ℚ) / primeClassMahlerMultiplier p s m) *
      primeClassMahlerMultiplier p s m = (a : ℚ) := by
    have hmul : (primeClassMahlerMultiplier p s m : ℚ) ≠ 0 := by
      exact_mod_cast (primeClassMahlerMultiplier_pos p s m hp).ne'
    field_simp
  have hmulR :
      (((a : ℚ) / primeClassMahlerMultiplier p s m : ℚ) : ℝ) *
          (primeClassMahlerMultiplier p s m : ℝ) = (a : ℝ) := by
    exact_mod_cast hmulQ
  have hmultCast : (primeClassMahlerMultiplier p s m : ℝ) =
      ((p ^ s : ℕ) : ℝ) ^ primeClassShiftCount p s m := by
    simp only [primeClassMahlerMultiplier, Nat.cast_pow]
  have hmulR' :
      (((a : ℚ) / primeClassMahlerMultiplier p s m : ℚ) : ℝ) *
          ((p ^ s : ℕ) : ℝ) ^ primeClassShiftCount p s m = (a : ℝ) := by
    rw [← hmultCast]
    exact hmulR
  have hcorr :
      ((((a : ℚ) / primeClassMahlerMultiplier p s m) *
          primeClassMahlerCorrectionRat b p s m : ℚ) : ℝ) =
        (((a : ℚ) / primeClassMahlerMultiplier p s m : ℚ) : ℝ) *
          ∑ t ∈ Icc 1 (primeClassShiftCount p s m),
            ((p ^ s : ℕ) : ℝ) ^ (primeClassShiftCount p s m - t) /
              ((b : ℝ) ^ primeClassReducedExponent p s m) ^ ((p ^ s) ^ t) := by
    rw [Rat.cast_mul, primeClassMahlerCorrectionRat_cast]
  rw [hnorm]
  rw [mul_sub, ← mul_assoc, hmulR', hcorr]

/-- Familywise inverse-Mahler normalization.  All finite corrections combine into one rational
number, which is harmless for normality. -/
theorem stonehamCombination_inverseMahler
    (b p : ℕ) {r : ℕ} (s m : Fin r → ℕ) (a : Fin r → ℤ)
    (hb : 2 ≤ b) (hp : p.Prime) (hs : ∀ i, 1 ≤ s i) :
    (∑ i, (primeClassInverseMahlerCoefficient p s m a i : ℝ) *
        stonehamAlpha (b ^ m i) (p ^ s i)) =
      (∑ i, (a i : ℝ) *
        stonehamAlpha (b ^ primeClassReducedExponent p (s i) (m i)) (p ^ s i)) -
        (primeClassInverseMahlerCorrection b p s m a : ℝ) := by
  rw [primeClassInverseMahlerCorrection, Rat.cast_sum]
  calc
    (∑ i, (primeClassInverseMahlerCoefficient p s m a i : ℝ) *
        stonehamAlpha (b ^ m i) (p ^ s i)) =
        ∑ i, ((a i : ℝ) *
          stonehamAlpha (b ^ primeClassReducedExponent p (s i) (m i)) (p ^ s i) -
          ((primeClassInverseMahlerCoefficient p s m a i *
            primeClassMahlerCorrectionRat b p (s i) (m i) : ℚ) : ℝ)) := by
      apply sum_congr rfl
      intro i hi
      simpa only [primeClassInverseMahlerCoefficient] using
        stonehamAlpha_inverseMahlerCoefficient b p (s i) (m i) (a i) hb hp (hs i)
    _ = (∑ i, (a i : ℝ) *
          stonehamAlpha (b ^ primeClassReducedExponent p (s i) (m i)) (p ^ s i)) -
        ∑ i, ((primeClassInverseMahlerCoefficient p s m a i *
          primeClassMahlerCorrectionRat b p (s i) (m i) : ℚ) : ℝ) :=
      by
        simpa only using (Finset.sum_sub_distrib (s := (Finset.univ : Finset (Fin r)))
          (fun i => (a i : ℝ) *
            stonehamAlpha (b ^ primeClassReducedExponent p (s i) (m i)) (p ^ s i))
          (fun i => ((primeClassInverseMahlerCoefficient p s m a i *
            primeClassMahlerCorrectionRat b p (s i) (m i) : ℚ) : ℝ)))

/-- The original rational combination is normal exactly when its reduced integral combination
is normal: the two differ by the rational correction above. -/
theorem isNormal_inverseMahlerCombination_iff
    (b p : ℕ) {r : ℕ} (s m : Fin r → ℕ) (a : Fin r → ℤ)
    (hb : 2 ≤ b) (hp : p.Prime) (hs : ∀ i, 1 ≤ s i) :
    IsNormal b (∑ i, (primeClassInverseMahlerCoefficient p s m a i : ℝ) *
        stonehamAlpha (b ^ m i) (p ^ s i)) ↔
      IsNormal b (∑ i, (a i : ℝ) *
        stonehamAlpha (b ^ primeClassReducedExponent p (s i) (m i)) (p ^ s i)) := by
  let x : ℝ := ∑ i, (primeClassInverseMahlerCoefficient p s m a i : ℝ) *
    stonehamAlpha (b ^ m i) (p ^ s i)
  let y : ℝ := ∑ i, (a i : ℝ) *
    stonehamAlpha (b ^ primeClassReducedExponent p (s i) (m i)) (p ^ s i)
  let R : ℚ := primeClassInverseMahlerCorrection b p s m a
  have hxy : x = y - (R : ℝ) := by
    simpa only [x, y, R] using stonehamCombination_inverseMahler b p s m a hb hp hs
  change IsNormal b x ↔ IsNormal b y
  constructor
  · intro hx
    have h := isNormal_rat_mul_add b hb x 1 R (by norm_num) hx
    convert h using 1
    rw [hxy]
    push_cast
    ring
  · intro hy
    have h := isNormal_rat_mul_add b hb y 1 (-R) (by norm_num) hy
    convert h using 1
    rw [hxy]
    push_cast
    ring

/-! ### Coefficients for an aligned mixed-`s` state -/

/-- After clearing to a top depth `s * K + δ`, the complete history of a `p^s`-series has
this geometric weight once every phase is replaced by its common Teichmuller phase. -/
def primeClassHistoryWeight (p s K δ : ℕ) : ℕ :=
  p ^ δ * ∑ j ∈ range K, (p ^ s) ^ j

/-- The extra integer factor which turns a mixed-`s` geometric history into a common relation
coefficient.  `D` is a common bound for the finitely many depth gaps `δ`. -/
def primeClassStateCoefficientScale (p s δ D : ℕ) : ℕ :=
  (p ^ s - 1) * p ^ (D - δ)

/-- The signed coefficient used in the cleared mixed-`s` state. -/
def primeClassStateCoefficient (p s δ D : ℕ) (a : ℤ) : ℤ :=
  a * primeClassStateCoefficientScale p s δ D

/-- Reindex a positive-depth history by its offset below the top. -/
lemma primeClass_sum_Icc_one_reflect {A : Type*} [AddCommMonoid A]
    (F : ℕ → A) (K : ℕ) :
    ∑ k ∈ Icc 1 K, F (K - k) = ∑ j ∈ range K, F j := by
  have hshift : ∀ (H : ℕ → A) (N : ℕ),
      ∑ k ∈ Icc 1 N, H k = ∑ j ∈ range N, H (j + 1) := by
    intro H N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [sum_Icc_succ_top (Nat.le_add_left 1 N), ih, sum_range_succ]
  rw [hshift]
  calc
    (∑ j ∈ range K, F (K - (j + 1))) =
        ∑ j ∈ range K, F (K - 1 - j) := by
          apply sum_congr rfl
          intro j hj
          congr 1
          omega
    _ = ∑ j ∈ range K, F j := sum_range_reflect F K

/-- The abstract history weight is exactly the numerator obtained by clearing a `p^(s*K)`
denominator to a top depth `s*K+δ`. -/
lemma primeClassHistoryWeight_eq_sum_Icc (p s K δ : ℕ) :
    primeClassHistoryWeight p s K δ =
      ∑ k ∈ Icc 1 K, p ^ (δ + s * (K - k)) := by
  unfold primeClassHistoryWeight
  calc
    p ^ δ * ∑ j ∈ range K, (p ^ s) ^ j =
        p ^ δ * ∑ k ∈ Icc 1 K, (p ^ s) ^ (K - k) := by
          rw [primeClass_sum_Icc_one_reflect]
    _ = ∑ k ∈ Icc 1 K, p ^ δ * (p ^ s) ^ (K - k) := by rw [mul_sum]
    _ = ∑ k ∈ Icc 1 K, p ^ (δ + s * (K - k)) := by
      apply sum_congr rfl
      intro k hk
      rw [pow_add, pow_mul]

/-- Exact evaluation of one complete geometric history. -/
lemma primeClassHistoryWeight_mul_sub_one
    (p s K δ : ℕ) (hp : p.Prime) :
    (p ^ s - 1) * primeClassHistoryWeight p s K δ =
      p ^ δ * (p ^ (s * K) - 1) := by
  have hps : 1 ≤ p ^ s := Nat.one_le_pow _ _ (Nat.one_le_iff_ne_zero.mpr hp.ne_zero)
  have hgeom := geom_sum_mul_of_one_le hps K
  unfold primeClassHistoryWeight
  calc
    (p ^ s - 1) * (p ^ δ * ∑ j ∈ range K, (p ^ s) ^ j) =
        p ^ δ * ((∑ j ∈ range K, (p ^ s) ^ j) * (p ^ s - 1)) := by ring
    _ = p ^ δ * ((p ^ s) ^ K - 1) := by rw [hgeom]
    _ = p ^ δ * (p ^ (s * K) - 1) := by rw [pow_mul]

/-- The gap-dependent scale cancels the geometric history up to the common factor `p^D`.
This is the coefficient correction, separate from inverse Mahler scaling, that the mixed-state
congruence must use. -/
lemma primeClassStateCoefficientScale_mul_historyWeight
    (p s K δ D : ℕ) (hp : p.Prime) (hδD : δ ≤ D) :
    primeClassStateCoefficientScale p s δ D * primeClassHistoryWeight p s K δ =
      p ^ D * (p ^ (s * K) - 1) := by
  rw [primeClassStateCoefficientScale]
  calc
    (p ^ s - 1) * p ^ (D - δ) * primeClassHistoryWeight p s K δ =
        p ^ (D - δ) * ((p ^ s - 1) * primeClassHistoryWeight p s K δ) := by ring
    _ = p ^ (D - δ) * (p ^ δ * (p ^ (s * K) - 1)) := by
      rw [primeClassHistoryWeight_mul_sub_one p s K δ hp]
    _ = p ^ D * (p ^ (s * K) - 1) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hδD]

lemma primeClassStateCoefficientScale_pos
    (p s δ D : ℕ) (hp : p.Prime) (hs : 1 ≤ s) :
    0 < primeClassStateCoefficientScale p s δ D := by
  unfold primeClassStateCoefficientScale
  have hpow : 1 < p ^ s := Nat.one_lt_pow (by omega : s ≠ 0) hp.one_lt
  exact mul_pos (by omega) (pow_pos hp.pos _)

/-- A nonzero cyclotomic relation coefficient stays nonzero after the aligned-history scaling. -/
lemma primeClassStateCoefficient_ne_zero
    (p s δ D : ℕ) (a : ℤ) (hp : p.Prime) (hs : 1 ≤ s) (ha : a ≠ 0) :
    primeClassStateCoefficient p s δ D a ≠ 0 := by
  unfold primeClassStateCoefficient
  exact mul_ne_zero ha (by
    exact_mod_cast (primeClassStateCoefficientScale_pos p s δ D hp hs).ne')

/-- Signed form of the aligned-history identity. -/
lemma primeClassStateCoefficient_mul_historyWeight
    (p s K δ D : ℕ) (a : ℤ) (hp : p.Prime) (hδD : δ ≤ D) :
    primeClassStateCoefficient p s δ D a * primeClassHistoryWeight p s K δ =
      a * (p : ℤ) ^ D * ((p : ℤ) ^ (s * K) - 1) := by
  have h := primeClassStateCoefficientScale_mul_historyWeight p s K δ D hp hδD
  have hpK : 1 ≤ p ^ (s * K) :=
    Nat.one_le_pow _ _ (Nat.one_le_iff_ne_zero.mpr hp.ne_zero)
  unfold primeClassStateCoefficient
  calc
    a * (primeClassStateCoefficientScale p s δ D : ℤ) *
        (primeClassHistoryWeight p s K δ : ℤ) =
        a * ((primeClassStateCoefficientScale p s δ D *
          primeClassHistoryWeight p s K δ : ℕ) : ℤ) := by push_cast; ring
    _ = a * ((p ^ D * (p ^ (s * K) - 1) : ℕ) : ℤ) := by rw [h]
    _ = a * (p : ℤ) ^ D * ((p : ℤ) ^ (s * K) - 1) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hpK, Nat.cast_pow, Nat.cast_one]
      ring

/-- The same signed identity in the literal cleared-history form used by `stonehamState`. -/
lemma primeClassStateCoefficient_mul_clearedHistory
    (p s K δ D : ℕ) (a : ℤ) (hp : p.Prime) (hδD : δ ≤ D) :
    primeClassStateCoefficient p s δ D a *
        (∑ k ∈ Icc 1 K, p ^ (δ + s * (K - k)) : ℕ) =
      a * (p : ℤ) ^ D * ((p : ℤ) ^ (s * K) - 1) := by
  rw [← primeClassHistoryWeight_eq_sum_Icc]
  exact primeClassStateCoefficient_mul_historyWeight p s K δ D a hp hδD

/-- Summing aligned histories reduces the whole mixed-`s` numerator to one relation modulo a
common power of `p`.  This is the algebraic core of the bounded-denominator direction: the new
top terms vanish because every `s i * K i` is deep enough, while the remaining terms are the
single inverse-phase relation supplied below. -/
lemma prime_pow_add_dvd_sum_alignedHistories
    (p D E : ℕ) (hp : p.Prime) {r : ℕ}
    (s K δ : Fin r → ℕ) (a z : Fin r → ℤ)
    (hδD : ∀ i, δ i ≤ D) (hdepth : ∀ i, E ≤ s i * K i)
    (hrel : (p : ℤ) ^ E ∣ ∑ i, a i * z i) :
    (p : ℤ) ^ (D + E) ∣
      ∑ i, primeClassStateCoefficient p (s i) (δ i) D (a i) *
        (primeClassHistoryWeight p (s i) (K i) (δ i) : ℤ) * z i := by
  have hterm : ∀ i,
      primeClassStateCoefficient p (s i) (δ i) D (a i) *
          (primeClassHistoryWeight p (s i) (K i) (δ i) : ℤ) * z i =
        (p : ℤ) ^ D *
          (a i * (p : ℤ) ^ (s i * K i) * z i - a i * z i) := by
    intro i
    rw [primeClassStateCoefficient_mul_historyWeight p (s i) (K i) (δ i) D
      (a i) hp (hδD i)]
    ring
  have hnew : (p : ℤ) ^ E ∣
      ∑ i, a i * (p : ℤ) ^ (s i * K i) * z i := by
    apply Finset.dvd_sum
    intro i hi
    exact ((pow_dvd_pow (p : ℤ) (hdepth i)).mul_left (a i)).mul_right (z i)
  have hinside : (p : ℤ) ^ E ∣
      (∑ i, a i * (p : ℤ) ^ (s i * K i) * z i) - ∑ i, a i * z i :=
    dvd_sub hnew hrel
  obtain ⟨t, ht⟩ := hinside
  refine ⟨t, ?_⟩
  rw [pow_add]
  calc
    ∑ i, primeClassStateCoefficient p (s i) (δ i) D (a i) *
          (primeClassHistoryWeight p (s i) (K i) (δ i) : ℤ) * z i =
        ∑ i, (p : ℤ) ^ D *
          (a i * (p : ℤ) ^ (s i * K i) * z i - a i * z i) := by
            apply sum_congr rfl
            intro i hi
            exact hterm i
    _ = (p : ℤ) ^ D *
        ((∑ i, a i * (p : ℤ) ^ (s i * K i) * z i) - ∑ i, a i * z i) := by
          rw [← mul_sum]
          rw [Finset.sum_sub_distrib]
    _ = (p : ℤ) ^ D * ((p : ℤ) ^ E * t) := by rw [ht]
    _ = (p : ℤ) ^ D * (p : ℤ) ^ E * t := by ring

/-! ### Identification with the rational Stoneham state -/

/-- The literal integer numerator obtained by clearing every `p^(s i * K i)` denominator to
one common prime depth `T`. -/
def primeClassClearedStateNumerator
    (b p T n : ℕ) {r : ℕ} (s u : Fin r → ℕ) (q : Fin r → ℤ) : ℤ :=
  ∑ i, q i * ∑ k ∈ Icc 1 (StonehamSumsNormal.stonehamK (fun j => p ^ s j) u i n),
    (b : ℤ) ^ (n - u i * (p ^ s i) ^ k) * (p : ℤ) ^ (T - s i * k)

/-- Clearing to a common prime depth gives exactly `primeClassClearedStateNumerator`.  This is
the bridge from the modular aligned-history calculation to the existing analytic
`stonehamState` interface. -/
lemma stonehamState_eq_primeClassClearedStateNumerator_div
    (b p T n : ℕ) {r : ℕ} (s u : Fin r → ℕ) (q : Fin r → ℤ)
    (hp : p.Prime)
    (hT : ∀ i, s i * StonehamSumsNormal.stonehamK (fun j => p ^ s j) u i n ≤ T) :
    StonehamSumsNormal.stonehamState b 1 (fun i => p ^ s i) u q n =
      (primeClassClearedStateNumerator b p T n s u q : ℚ) / (p : ℚ) ^ T := by
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [eq_div_iff (pow_ne_zero T hpQ)]
  unfold StonehamSumsNormal.stonehamState primeClassClearedStateNumerator
  simp only [Nat.cast_one, div_one, one_mul]
  push_cast
  rw [sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_assoc]
  congr 1
  rw [sum_mul]
  apply sum_congr rfl
  intro k hk
  have hkK : k ≤ StonehamSumsNormal.stonehamK (fun j => p ^ s j) u i n :=
    (mem_Icc.mp hk).2
  have hsk : s i * k ≤ T :=
    (Nat.mul_le_mul_left (s i) hkK).trans (hT i)
  rw [← pow_mul]
  rw [div_eq_mul_inv, pow_sub₀ (p : ℚ) hpQ hsk]
  ring

/-- A cyclotomic integral relation also vanishes at the inverse primitive root.  This is the
phase orientation occurring in the cleared Stoneham state. -/
lemma integerRelation_inverseRoot_eq_zero
    {d r : ℕ} (hd : d ≠ 0) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (m : Fin r → ℕ) (a : Fin r → ℤ)
    (hdiv : cyclotomic d ℤ ∣ integerRelationPolynomial m a) :
    ∑ i, (((a i : ℤ) : ℚ) : ℂ) * (ζ⁻¹) ^ m i = 0 := by
  have h := (cyclotomic_int_dvd_integerRelationPolynomial_iff hd hζ.inv m a).mp hdiv
  simpa only [aeval_relationPolynomial] using h

/-- A uniform natural exponent above every selected exponent. -/
def primeClassExponentCap {r : ℕ} (m : Fin r → ℕ) : ℕ :=
  ∑ i, m i

/-- Complementary exponents turn inverse powers into ordinary nonnegative powers after one
common unit factor. -/
def primeClassComplementExponent {r : ℕ} (m : Fin r → ℕ) (i : Fin r) : ℕ :=
  primeClassExponentCap m - m i

lemma primeClassExponent_le_cap {r : ℕ} (m : Fin r → ℕ) (i : Fin r) :
    m i ≤ primeClassExponentCap m := by
  unfold primeClassExponentCap
  exact single_le_sum (fun j _ => Nat.zero_le (m j)) (mem_univ i)

/-- The same integral relation vanishes on complementary exponents. -/
lemma integerRelation_complement_eq_zero
    {d r : ℕ} (hd : d ≠ 0) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (m : Fin r → ℕ) (a : Fin r → ℤ)
    (hdiv : cyclotomic d ℤ ∣ integerRelationPolynomial m a) :
    ∑ i, (((a i : ℤ) : ℚ) : ℂ) * ζ ^ primeClassComplementExponent m i = 0 := by
  have hinverse := integerRelation_inverseRoot_eq_zero hd hζ m a hdiv
  calc
    ∑ i, (((a i : ℤ) : ℚ) : ℂ) * ζ ^ primeClassComplementExponent m i =
        ζ ^ primeClassExponentCap m *
          ∑ i, (((a i : ℤ) : ℚ) : ℂ) * (ζ⁻¹) ^ m i := by
            rw [mul_sum]
            apply sum_congr rfl
            intro i hi
            rw [primeClassComplementExponent,
              pow_sub₀ ζ (hζ.ne_zero hd) (primeClassExponent_le_cap m i), inv_pow]
            ring
    _ = 0 := by rw [hinverse, mul_zero]

/-- Cyclotomic divisibility is preserved by replacing every exponent with its complement in a
common cap. -/
lemma cyclotomic_dvd_integerRelationPolynomial_complement
    {d r : ℕ} (hd : d ≠ 0) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (m : Fin r → ℕ) (a : Fin r → ℤ)
    (hdiv : cyclotomic d ℤ ∣ integerRelationPolynomial m a) :
    cyclotomic d ℤ ∣
      integerRelationPolynomial (primeClassComplementExponent m) a := by
  apply (cyclotomic_int_dvd_integerRelationPolynomial_iff hd hζ
    (primeClassComplementExponent m) a).mpr
  rw [aeval_relationPolynomial]
  exact integerRelation_complement_eq_zero hd hζ m a hdiv

/-- Finite Teichmuller evaluation of the complementary-exponent (inverse-phase) relation. -/
lemma prime_pow_dvd_integerRelation_eval_teichmuller_complement
    (p b K : ℕ) (hp : p.Prime) (hbp : Nat.Coprime b p)
    {r : ℕ} (m : Fin r → ℕ) (a : Fin r → ℤ)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hdiv : cyclotomic (orderOf (b : ZMod p)) ℤ ∣ integerRelationPolynomial m a) :
    (p : ℤ) ^ K ∣
      ∑ i, a i * ((b : ℤ) ^ (p ^ K)) ^ primeClassComplementExponent m i := by
  have hd : orderOf (b : ZMod p) ≠ 0 :=
    orderOf_ne_zero_iff.mpr ((ZMod.isUnit_iff_coprime b p).mpr hbp).isOfFinOrder
  exact prime_pow_dvd_integerRelation_eval_teichmuller p b K hp hbp
    (primeClassComplementExponent m) a
      (cyclotomic_dvd_integerRelationPolynomial_complement hd hζ m a hdiv)

/-- Dependence supplies the exact nonzero inverse-Mahler witness needed by the non-normal half,
together with one fixed integral relation that vanishes at every finite Teichmuller level. -/
theorem exists_inverseMahlerWitness_of_not_linearIndependent
    (b p : ℕ) (hp : p.Prime) (hb : 2 ≤ b) (hpb : Nat.Coprime p b)
    {r : ℕ} (s m : Fin r → ℕ) (hs : ∀ i, 1 ≤ s i)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ (orderOf (b : ZMod p)))
    (hdep : ¬ LinearIndependent ℚ (fun i ↦ ζ ^ m i)) :
    ∃ a : Fin r → ℤ, a ≠ 0 ∧
      primeClassInverseMahlerCoefficient p s m a ≠ 0 ∧
      (∑ i, (((a i : ℤ) : ℚ) : ℂ) * (ζ⁻¹) ^
        primeClassReducedExponent p (s i) (m i) = 0) ∧
      (∀ K, (p : ℤ) ^ K ∣
        ∑ i, a i * ((b : ℤ) ^ (p ^ K)) ^
          primeClassReducedExponent p (s i) (m i)) ∧
      (∀ K, (p : ℤ) ^ K ∣
        ∑ i, a i * ((b : ℤ) ^ (p ^ K)) ^
          primeClassComplementExponent
            (fun j ↦ primeClassReducedExponent p (s j) (m j)) i) ∧
      (IsNormal b (∑ i, (primeClassInverseMahlerCoefficient p s m a i : ℝ) *
          stonehamAlpha (b ^ m i) (p ^ s i)) ↔
        IsNormal b (∑ i, (a i : ℝ) *
          stonehamAlpha (b ^ primeClassReducedExponent p (s i) (m i)) (p ^ s i))) := by
  have hdepReduced : ¬ LinearIndependent ℚ
      (fun i ↦ ζ ^ primeClassReducedExponent p (s i) (m i)) := by
    intro hind
    apply hdep
    exact (linearIndependent_primeClassReducedPowers_iff p b s m hp hpb.symm ζ hζ).mp hind
  have hd : orderOf (b : ZMod p) ≠ 0 :=
    orderOf_ne_zero_iff.mpr ((ZMod.isUnit_iff_coprime b p).mpr hpb.symm).isOfFinOrder
  obtain ⟨a, ha, hdiv⟩ :=
    (not_linearIndependent_powers_iff_exists_integer_cyclotomic hd hζ
      (fun i ↦ primeClassReducedExponent p (s i) (m i))).mp hdepReduced
  have hinverse := integerRelation_inverseRoot_eq_zero hd hζ
    (fun i ↦ primeClassReducedExponent p (s i) (m i)) a hdiv
  have hfinite : ∀ K, (p : ℤ) ^ K ∣
      ∑ i, a i * ((b : ℤ) ^ (p ^ K)) ^
        primeClassReducedExponent p (s i) (m i) := fun K =>
    prime_pow_dvd_integerRelation_eval_teichmuller p b K hp hpb.symm
      (fun i ↦ primeClassReducedExponent p (s i) (m i)) a hdiv
  have hfiniteInverse : ∀ K, (p : ℤ) ^ K ∣
      ∑ i, a i * ((b : ℤ) ^ (p ^ K)) ^
        primeClassComplementExponent
          (fun j ↦ primeClassReducedExponent p (s j) (m j)) i := fun K =>
    prime_pow_dvd_integerRelation_eval_teichmuller_complement p b K hp hpb.symm
      (fun i ↦ primeClassReducedExponent p (s i) (m i)) a hζ hdiv
  exact ⟨a, ha, primeClassInverseMahlerCoefficient_ne_zero p s m a hp ha,
    hinverse, hfinite, hfiniteInverse,
    isNormal_inverseMahlerCombination_iff b p s m a hb hp hs⟩

end NormalNumbers.StonehamPrimeClass
