/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LiteratureVandehey
import NormalNumbers.VandeheyRenyi
import NormalNumbers.OccurrenceCountEquiv

/-!
# The Smith-normal-form reduction for Vandehey 2017, Theorem 1.1

`VandeheyUniformFreq` (`LiteratureVandehey.lean`) quantifies over *every* nonsingular
integer matrix.  This module reduces that to two leaves by a generation argument:

* every nonsingular integer `2 × 2` matrix is a product of `GL₂(ℤ)` matrices and the
  single scaling matrix `diag(p, 1)` for primes `p` (an elementary Smith/Hermite
  descent on `|det|`, proved here as `mobiusGen`), and
* the per-matrix statement "preserves CF-normality" (`MobiusCFN`) is **closed under
  composition** (`MobiusCFN.comp`).

The composition step is where the CF content of the reduction sits: to compose one must
know the intermediate point is off the second pole, and the only thing that rules a pole
out is that a CF-normal number is irrational — proved here from scratch
(`not_isCFNormal_of_not_irrational`), since a rational's Gauss orbit hits `0` in finitely
many steps and its digits are eventually the junk value `0`.

Finally `VandeheyUniformFreq` is *equivalent* to `vandehey_matrix_action`
(`vandeheyUniformFreq_of_matrix_action`): given preservation, the limit is `γ(I_v)`,
manifestly independent of `x`.  So the whole of Vandehey 1.1 rests on

1. `MobiusCFNGL2` — `GL₂(ℤ)` maps preserve CF-normality (Serret: the CF tails agree), and
2. `MobiusCFNPrime` — `x ↦ p·x` preserves CF-normality for prime `p` (the class automaton;
   `VandeheyTwo.tendsto_jointCount_classStep` is the equidistribution input).
-/

namespace NormalNumbers.Literature

open NormalNumbers Filter

/-! ## Rationals are not CF-normal -/

/-- The Gauss orbit of a rational in `[0,1)` reaches `0`: the Euclidean descent
`a/b ↦ (b % a)/a`. -/
lemma exists_gaussMap_iterate_div_eq_zero :
    ∀ b : ℕ, ∀ a : ℕ, a < b → ∃ n : ℕ, gaussMap^[n] ((a : ℝ) / (b : ℝ)) = 0 := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · exact ⟨0, by simp⟩
    · have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le a) hab
      have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
      have hb' : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
      have hx0 : ((a : ℝ) / (b : ℝ)) ≠ 0 := by positivity
      have hstep : gaussMap ((a : ℝ) / (b : ℝ)) = ((b % a : ℕ) : ℝ) / (a : ℝ) := by
        rw [gaussMap, if_neg hx0, inv_div, Int.fract_div_natCast_eq_div_natCast_mod]
      obtain ⟨n, hn⟩ := ih a hab (b % a) (Nat.mod_lt _ ha)
      exact ⟨n + 1, by rw [Function.iterate_succ_apply, hstep, hn]⟩

/-- Every rational's Gauss orbit reaches `0`. -/
lemma exists_gaussMap_iterate_eq_zero {y : ℝ} (hy : ¬ Irrational y) :
    ∃ n : ℕ, gaussMap^[n] y = 0 := by
  rcases eq_or_ne y 0 with rfl | hy0
  · exact ⟨0, rfl⟩
  · -- one Gauss step lands in `[0,1)`, still rational
    obtain ⟨q, rfl⟩ : ∃ q : ℚ, (q : ℝ) = y := by
      simpa [Irrational, not_not] using hy
    set r : ℚ := Int.fract q⁻¹ with hr
    have hstep : gaussMap (q : ℝ) = (r : ℝ) := by
      have hinv : ((q : ℝ))⁻¹ = ((q⁻¹ : ℚ) : ℝ) := by push_cast; ring
      rw [gaussMap, if_neg hy0, hr, hinv, Int.fract, Int.fract, Rat.floor_cast]
      push_cast
      ring
    have hr0 : 0 ≤ r := Int.fract_nonneg _
    have hr1 : r < 1 := Int.fract_lt_one _
    -- write `r = a / b`
    have hden : (0 : ℤ) < (r.den : ℤ) := by exact_mod_cast r.pos
    have hnum0 : 0 ≤ r.num := Rat.num_nonneg.mpr hr0
    have hnumlt : r.num < (r.den : ℤ) := by
      have hd : (0 : ℚ) < (r.den : ℚ) := by exact_mod_cast r.pos
      have h1 : (r.num : ℚ) = r * (r.den : ℚ) := by
        have hnd := Rat.num_div_den r
        rwa [div_eq_iff (ne_of_gt hd)] at hnd
      have h2 : (r.num : ℚ) < (r.den : ℚ) := by
        rw [h1]; nlinarith
      exact_mod_cast h2
    set a : ℕ := r.num.toNat with ha
    have hab : a < r.den := by omega
    have hcast : ((a : ℝ) / (r.den : ℝ)) = (r : ℝ) := by
      rw [Rat.cast_def, ha]
      congr 1
      exact_mod_cast Int.toNat_of_nonneg hnum0
    obtain ⟨n, hn⟩ := exists_gaussMap_iterate_div_eq_zero r.den a hab
    refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply, hstep, ← hcast, hn]

/-- A number whose Gauss orbit has reached `0` stays there. -/
lemma gaussMap_iterate_eq_zero_of_le {y : ℝ} {n : ℕ} (hn : gaussMap^[n] y = 0)
    {m : ℕ} (hm : n ≤ m) : gaussMap^[m] y = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  rw [add_comm, Function.iterate_add_apply, hn]
  induction k with
  | zero => rfl
  | succ j ihj => rw [Function.iterate_succ_apply', ihj]; simp [gaussMap]

/-- **A CF-normal number is irrational.**  A rational's digits are eventually the junk
value `0`, so the digit `1` occurs boundedly often and its frequency tends to `0`, while
CF-normality demands `γ(I_[1]) > 0`. -/
theorem not_isCFNormal_of_not_irrational {y : ℝ} (hy : ¬ Irrational y) : ¬ IsCFNormal y := by
  intro hnorm
  obtain ⟨n₀, hn₀⟩ := exists_gaussMap_iterate_eq_zero hy
  have hdig : ∀ m, n₀ ≤ m → cfDigit y m = 0 := by
    intro m hm
    rw [cfDigit, gaussMap_iterate_eq_zero_of_le hn₀ hm]
    simp
  have hbound : ∀ p : ℕ, countOccurrences [1] ((List.range p).map (cfDigit y)) ≤ n₀ := by
    intro p
    classical
    refine le_trans (countOccurrences_le_occStart [1] (by simp) (cfDigit y) p) ?_
    rw [occStart]
    refine le_trans (Finset.card_le_card (?_ : _ ⊆ Finset.range n₀)) (by simp)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    by_contra hcon
    have := hdig i (by omega)
    simp [this] at hi
  have hlim := hnorm [1] (by simp) (by simp)
  have h0 : Tendsto (fun p : ℕ => (n₀ : ℝ) / p) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hle : (gaussMeasure (cfCylinder [1])).toReal ≤ 0 := by
    refine le_of_tendsto_of_tendsto' hlim h0 (fun p => ?_)
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · have hp' : (0 : ℝ) < p := by exact_mod_cast hp
      have := hbound p
      have : (countOccurrences [1] ((List.range p).map (cfDigit y)) : ℝ) ≤ (n₀ : ℝ) := by
        exact_mod_cast this
      gcongr
  have hpos : 0 < (gaussMeasure (cfCylinder [1])).toReal :=
    VandeheyRenyi.Doeblin.gaussMeasure_cfCylinder_toReal_pos [1] (by simp) (by simp)
  linarith

/-- A rational's fractional part is rational. -/
lemma not_irrational_fract {x : ℝ} (h : ¬ Irrational x) : ¬ Irrational (Int.fract x) := by
  obtain ⟨q, rfl⟩ : ∃ q : ℚ, (q : ℝ) = x := by simpa [Irrational, not_not] using h
  have : Int.fract ((q : ℝ)) = ((q - (⌊q⌋ : ℚ) : ℚ) : ℝ) := by
    rw [Int.fract, Rat.floor_cast]; push_cast; ring
  intro hcon
  exact hcon ⟨q - (⌊q⌋ : ℚ), this.symm⟩

/-! ## The per-matrix predicate, and composition -/

/-- `MobiusCFN a b c d`: the Möbius map of the integer matrix `(a b; c d)` sends
CF-normal numbers (off its pole) to CF-normal numbers.  `vandehey_matrix_action` is
exactly `∀ M, det M ≠ 0 → MobiusCFN M`. -/
def MobiusCFN (a b c d : ℤ) : Prop :=
  ∀ x : ℝ, (c : ℝ) * x + d ≠ 0 → IsCFNormal (Int.fract x) →
    IsCFNormal (Int.fract (((a : ℝ) * x + b) / ((c : ℝ) * x + d)))

/-- **Content locator** (guard rule): the identity matrix satisfies `MobiusCFN`, with no
CF input at all.  This is where the content is *not*. -/
theorem mobiusCFN_one : MobiusCFN 1 0 0 1 := by
  intro x _ hx
  simpa using hx

/-- **Degenerate-case verdict** (guard rule): a constant map `x ↦ b/d` — the `a = c = 0`
configuration — satisfies `MobiusCFN` only vacuously; here it is outright FALSE, because a
rational constant is not CF-normal.  So the nonsingularity hypothesis is load-bearing. -/
theorem not_mobiusCFN_const : ¬ MobiusCFN 0 1 0 1 := by
  intro h
  obtain ⟨x, _, _, hxn, _⟩ := exists_cfNormal_with_cfNormal_image 1 0 0 1 (by norm_num)
  have hout := h x (by norm_num) hxn
  simp only [Int.cast_zero, Int.cast_one, zero_mul, zero_add, div_one, Int.fract_one] at hout
  exact not_isCFNormal_of_not_irrational (by simpa using Rat.not_irrational 0) hout

/-- A CF-normal number is irrational, in the form the pole analysis wants. -/
lemma irrational_of_isCFNormal_fract {x : ℝ} (hx : IsCFNormal (Int.fract x)) :
    Irrational x := by
  by_contra h
  exact not_isCFNormal_of_not_irrational (not_irrational_fract h) hx

/-- **Composition.**  `MobiusCFN` is closed under matrix product.  The only CF input is
that a CF-normal `x` is irrational, which is what keeps `x` off the inner pole. -/
theorem MobiusCFN.comp {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ}
    (hdet₂ : a₂ * d₂ - b₂ * c₂ ≠ 0)
    (h₁ : MobiusCFN a₁ b₁ c₁ d₁) (h₂ : MobiusCFN a₂ b₂ c₂ d₂) :
    MobiusCFN (a₁ * a₂ + b₁ * c₂) (a₁ * b₂ + b₁ * d₂)
      (c₁ * a₂ + d₁ * c₂) (c₁ * b₂ + d₁ * d₂) := by
  intro x hden hx
  have hirr : Irrational x := irrational_of_isCFNormal_fract hx
  -- the inner denominator is nonzero
  have hden₂ : (c₂ : ℝ) * x + d₂ ≠ 0 := by
    intro h0
    rcases eq_or_ne c₂ 0 with hc | hc
    · apply hdet₂
      have hd₂ : (d₂ : ℝ) = 0 := by rw [hc] at h0; simpa using h0
      have : d₂ = 0 := by exact_mod_cast hd₂
      simp [hc, this]
    · have hcR : (c₂ : ℝ) ≠ 0 := by exact_mod_cast hc
      have : x = (-(d₂ : ℝ)) / (c₂ : ℝ) := by field_simp at h0 ⊢; linarith
      exact hirr ⟨(-(d₂ : ℚ)) / (c₂ : ℚ), by rw [this]; push_cast; ring⟩
  set y : ℝ := ((a₂ : ℝ) * x + b₂) / ((c₂ : ℝ) * x + d₂) with hy
  have hyn : IsCFNormal (Int.fract y) := h₂ x hden₂ hx
  -- the composite denominator factors
  have hymul : y * ((c₂ : ℝ) * x + d₂) = (a₂ : ℝ) * x + b₂ := by
    rw [hy, div_mul_cancel₀ _ hden₂]
  have hfac : ((c₁ : ℝ) * y + d₁) * ((c₂ : ℝ) * x + d₂)
      = ((c₁ * a₂ + d₁ * c₂ : ℤ) : ℝ) * x + ((c₁ * b₂ + d₁ * d₂ : ℤ) : ℝ) := by
    push_cast
    linear_combination (c₁ : ℝ) * hymul
  have hden₁ : (c₁ : ℝ) * y + d₁ ≠ 0 := by
    intro h0
    exact hden (by rw [← hfac, h0, zero_mul])
  have hnum : ((a₁ : ℝ) * y + b₁) * ((c₂ : ℝ) * x + d₂)
      = ((a₁ * a₂ + b₁ * c₂ : ℤ) : ℝ) * x + ((a₁ * b₂ + b₁ * d₂ : ℤ) : ℝ) := by
    push_cast
    linear_combination (a₁ : ℝ) * hymul
  have hkey : (((a₁ * a₂ + b₁ * c₂ : ℤ) : ℝ) * x + ((a₁ * b₂ + b₁ * d₂ : ℤ) : ℝ))
      / (((c₁ * a₂ + d₁ * c₂ : ℤ) : ℝ) * x + ((c₁ * b₂ + d₁ * d₂ : ℤ) : ℝ))
      = ((a₁ : ℝ) * y + b₁) / ((c₁ : ℝ) * y + d₁) := by
    rw [← hnum, ← hfac, mul_div_mul_right _ _ hden₂]
  rw [hkey]
  exact h₁ y hden₁ hyn

/-- `MobiusCFN` only depends on the matrix entries up to propositional equality. -/
lemma MobiusCFN.congr {a b c d a' b' c' d' : ℤ} (ha : a = a') (hb : b = b') (hc : c = c')
    (hd : d = d') (h : MobiusCFN a b c d) : MobiusCFN a' b' c' d' := by
  subst ha; subst hb; subst hc; subst hd; exact h

/-! ## The two leaves -/

/-- **Leaf 1 (Serret).**  `GL₂(ℤ)` maps preserve CF-normality: `GL₂(ℤ)`-equivalent reals have
CF expansions with a common tail, and digit-window frequencies only see the tail. -/
def MobiusCFNGL2 : Prop :=
  ∀ a b c d : ℤ, a * d - b * c = 1 ∨ a * d - b * c = -1 → MobiusCFN a b c d

/-- **Leaf 2 (the class automaton).**  `x ↦ p·x` preserves CF-normality for prime `p`.  This is
the case Vandehey's transducer is built for, and the one where
`VandeheyTwo.tendsto_jointCount_classStep` already supplies the equidistribution input. -/
def MobiusCFNScale : Prop :=
  ∀ p : ℕ, p.Prime → MobiusCFN (p : ℤ) 0 0 1

/-! ## The descent -/

/-- Over `𝔽_p` a singular matrix kills a column vector of the normalized shape `(1, k)`, unless
its second column is already `≡ 0`.  This is the `p+1` coset decomposition of the det-`p` double
coset, in the only form the descent needs. -/
lemma exists_column_kill (p : ℕ) (hp : p.Prime) (a b c d : ℤ)
    (hdvd : (p : ℤ) ∣ a * d - b * c) :
    (∃ k : ℤ, (p : ℤ) ∣ a + b * k ∧ (p : ℤ) ∣ c + d * k) ∨ ((p : ℤ) ∣ b ∧ (p : ℤ) ∣ d) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hz : ∀ z : ℤ, ((p : ℤ) ∣ z) ↔ ((z : ZMod p) = 0) :=
    fun z => (ZMod.intCast_zmod_eq_zero_iff_dvd z p).symm
  have hdet : ((a : ZMod p) * d - b * c) = 0 := by
    have := (hz _).mp hdvd
    push_cast at this
    exact this
  by_cases hB : (b : ZMod p) = 0
  · by_cases hD : (d : ZMod p) = 0
    · exact Or.inr ⟨(hz b).mpr hB, (hz d).mpr hD⟩
    · -- `b ≡ 0`, `d ≢ 0`, so `a ≡ 0`; take `k = -c/d`
      have hA : (a : ZMod p) = 0 := by
        have : (a : ZMod p) * d = 0 := by rw [hB] at hdet; linear_combination hdet
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h hD
      refine Or.inl ⟨((-(c : ZMod p) / d).val : ℤ), ?_, ?_⟩ <;>
        rw [hz] <;> push_cast <;> simp only [ZMod.natCast_val, ZMod.cast_id]
      · rw [hA, hB]; ring
      · field_simp; ring
  · refine Or.inl ⟨((-(a : ZMod p) / b).val : ℤ), ?_, ?_⟩ <;>
      rw [hz] <;> push_cast <;> simp only [ZMod.natCast_val, ZMod.cast_id]
    · field_simp; ring
    · field_simp
      linear_combination -hdet

/-- **The Smith/Hermite descent.**  Every nonsingular integer matrix acts as a composition of
`GL₂(ℤ)` maps and prime scalings, so the two leaves imply the whole of `vandehey_matrix_action`.
Induction on `|det|`: a prime `p ∣ det` lets one factor `M = M'' · diag(p,1) · V` with
`V ∈ GL₂(ℤ)` and `|det M''| = |det M| / p`. -/
theorem mobiusCFN_of_leaves (hGL2 : MobiusCFNGL2) (hScale : MobiusCFNScale) :
    ∀ n : ℕ, ∀ a b c d : ℤ, (a * d - b * c).natAbs = n → a * d - b * c ≠ 0 →
      MobiusCFN a b c d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c d hn hdet
    rcases eq_or_ne n 1 with rfl | hn1
    · exact hGL2 a b c d (Int.natAbs_eq_iff.mp hn |>.imp (fun h => by simpa using h)
        (fun h => by simpa using h))
    · have hn0 : n ≠ 0 := fun h => hdet (Int.natAbs_eq_zero.mp (h ▸ hn))
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
      have hpdet : (p : ℤ) ∣ a * d - b * c := Int.natCast_dvd.mpr (by rw [hn]; exact hpn)
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.pos.ne'
      have hp2 : 2 ≤ p := hp.two_le
      have hscale : MobiusCFN (p : ℤ) 0 0 1 := hScale p hp
      have hdetscale : (p : ℤ) * 1 - 0 * 0 ≠ 0 := by simpa using hpz
      -- the descent bound, shared by both cases
      have hshrink : ∀ e : ℤ, ((p : ℤ) * e).natAbs = n → e ≠ 0 → e.natAbs < n := by
        intro e he hene
        have hnn : n = p * e.natAbs := by
          rw [← he, Int.natAbs_mul, Int.natAbs_natCast]
        have hpos : 0 < e.natAbs := Int.natAbs_pos.mpr hene
        nlinarith [hpos, hp2, hnn]
      rcases exists_column_kill p hp a b c d hpdet with ⟨k, hk1, hk2⟩ | ⟨hbdvd, hddvd⟩
      · obtain ⟨a', ha'⟩ := hk1
        obtain ⟨c', hc'⟩ := hk2
        have hkey : (p : ℤ) * (a' * d - b * c') = a * d - b * c := by
          linear_combination b * hc' - d * ha'
        have hne'' : a' * d - b * c' ≠ 0 := fun h => hdet (by rw [← hkey, h, mul_zero])
        have hM'' := ih _ (hshrink _ (by rw [hkey, hn]) hne'') a' b c' d rfl hne''
        have step1 := MobiusCFN.comp hdetscale hM'' hscale
        have hVinv : MobiusCFN 1 0 (-k) 1 := hGL2 1 0 (-k) 1 (Or.inl (by ring))
        have hdetVinv : (1 : ℤ) * 1 - 0 * (-k) ≠ 0 := by norm_num
        have step2 := MobiusCFN.comp hdetVinv step1 hVinv
        refine MobiusCFN.congr ?_ ?_ ?_ ?_ step2
        · linear_combination -ha'
        · ring
        · linear_combination -hc'
        · ring
      · obtain ⟨b', hb'⟩ := hbdvd
        obtain ⟨d', hd'⟩ := hddvd
        have hkey : (p : ℤ) * (b' * c - a * d') = b * c - a * d := by
          linear_combination a * hd' - c * hb'
        have hne'' : b' * c - a * d' ≠ 0 := by
          intro h
          apply hdet
          have h0 : b * c - a * d = 0 := by rw [← hkey, h, mul_zero]
          linarith
        have hnat : ((p : ℤ) * (b' * c - a * d')).natAbs = n := by
          rw [hkey, show b * c - a * d = -(a * d - b * c) by ring, Int.natAbs_neg, hn]
        have hM'' := ih _ (hshrink _ hnat hne'') b' a d' c rfl hne''
        have step1 := MobiusCFN.comp hdetscale hM'' hscale
        have hV : MobiusCFN 0 1 1 0 := hGL2 0 1 1 0 (Or.inr (by ring))
        have hdetV : (0 : ℤ) * 0 - 1 * 1 ≠ 0 := by norm_num
        have step2 := MobiusCFN.comp hdetV step1 hV
        refine MobiusCFN.congr ?_ ?_ ?_ ?_ step2
        · ring
        · linear_combination -hb'
        · ring
        · linear_combination -hd'

/-! ## Assembly -/

/-- `vandehey_matrix_action` is exactly `MobiusCFN` for every nonsingular matrix. -/
theorem vandehey_matrix_action_of_mobiusCFN
    (h : ∀ a b c d : ℤ, a * d - b * c ≠ 0 → MobiusCFN a b c d) : vandehey_matrix_action :=
  fun x a b c d hdet hden hx => h a b c d hdet x hden hx

/-- **The crux is implied by preservation.**  If every nonsingular integer Möbius map preserves
CF-normality then the limiting frequency in `VandeheyUniformFreq` is `γ(I_v)` — manifestly
independent of `x`, which is all the crux asks.  (The converse is
`vandehey_matrix_action_of_uniformFreq`, so the two are equivalent.) -/
theorem vandeheyUniformFreq_of_matrix_action (h : vandehey_matrix_action) :
    VandeheyUniformFreq := by
  intro a b c d hdet v hne hpos
  exact ⟨(gaussMeasure (cfCylinder v)).toReal,
    fun x hden hx => h x a b c d hdet hden hx v hne hpos⟩

/-- **The Smith reduction, assembled.**  Vandehey 2017 Theorem 1.1 — and hence the crux
`VandeheyUniformFreq` — follows from the two leaves: `GL₂(ℤ)` maps (Serret) and prime scalings
(the class automaton). -/
theorem vandeheyUniformFreq_of_leaves (hGL2 : MobiusCFNGL2) (hScale : MobiusCFNScale) :
    VandeheyUniformFreq :=
  vandeheyUniformFreq_of_matrix_action
    (vandehey_matrix_action_of_mobiusCFN
      (fun a b c d hdet => mobiusCFN_of_leaves hGL2 hScale _ a b c d rfl hdet))

end NormalNumbers.Literature

/-! ### Axiom audit -/
section
open NormalNumbers.Literature
#print axioms mobiusCFN_of_leaves
#print axioms vandeheyUniformFreq_of_leaves
#print axioms not_isCFNormal_of_not_irrational
end
