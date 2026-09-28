/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheySmith
import NormalNumbers.CFAffineFamily

/-!
# The Serret leaf: `GL₂(ℤ)` maps preserve CF-normality

`MobiusCFNGL2` (`VandeheySmith.lean`) is one of the two leaves the Smith reduction leaves
behind.  It is discharged here, from `PGL₂(ℤ) = ⟨x ↦ x + 1, x ↦ 1/x⟩` and the tail-shift
engine (`CFTailFreq.lean`): each generator moves the CF digit sequence by a bounded shift,
so window frequencies are untouched.

The one real computation is `x ↦ −x`, i.e. `t ↦ 1 − t` on `(0,1)`:

* `t < 1/2` (first digit `≥ 2`): `T²(1−t) = T t` — the digits of `1−t` are `1, a₁−1, a₂, …`;
* `t > 1/2` (first digit `= 1`): `T(1−t) = T² t` — the digits of `1−t` are `a₂+1, a₃, …`.

Either way the two digit sequences agree after a shift, which is exactly what
`isCFNormal_of_digit_shift` consumes.
-/

namespace NormalNumbers.Literature

open NormalNumbers Filter

/-- Digits are read off the Gauss orbit, so a coincidence of orbits at finite times gives a
digit shift. -/
lemma cfDigit_shift_of_iterate {y z : ℝ} {j k : ℕ} (h : gaussMap^[j] y = gaussMap^[k] z) :
    ∀ n, cfDigit y (n + j) = cfDigit z (n + k) := by
  intro n
  simp only [cfDigit]
  rw [Function.iterate_add_apply, Function.iterate_add_apply, h]

/-- `T² (1 − t) = T t` when `t < 1/2`. -/
lemma gaussMap_two_one_sub_of_lt {t : ℝ} (ht0 : 0 < t) (ht : t < 1 / 2) :
    gaussMap (gaussMap (1 - t)) = gaussMap t := by
  have hu0 : (1 : ℝ) / 2 < 1 - t := by linarith
  have hune : (1 : ℝ) - t ≠ 0 := by linarith
  have hinv : (1 - t)⁻¹ < 2 := by
    rw [inv_lt_comm₀ (by linarith) (by norm_num)]
    linarith
  have hinv1 : 1 < (1 - t)⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) (by linarith)]
    linarith
  have hfloor : ⌊(1 - t)⁻¹⌋ = 1 := by
    rw [Int.floor_eq_iff]
    constructor <;> [exact_mod_cast hinv1.le; exact_mod_cast hinv]
  have hstep : gaussMap (1 - t) = t / (1 - t) := by
    rw [gaussMap, if_neg hune, Int.fract, hfloor]
    push_cast
    field_simp
    ring
  rw [hstep]
  have hv0 : t / (1 - t) ≠ 0 := by positivity
  have hvinv : (t / (1 - t))⁻¹ = t⁻¹ - 1 := by
    rw [inv_div]
    field_simp
  rw [gaussMap, if_neg hv0, hvinv, gaussMap, if_neg (ne_of_gt ht0)]
  rw [show t⁻¹ - 1 = t⁻¹ - (1 : ℤ) by push_cast; ring, Int.fract_sub_intCast]

/-- `T (1 − t) = T² t` when `t > 1/2`. -/
lemma gaussMap_one_sub_of_gt {t : ℝ} (ht : 1 / 2 < t) (ht1 : t < 1) :
    gaussMap (1 - t) = gaussMap (gaussMap t) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hune : (1 : ℝ) - t ≠ 0 := by linarith
  have hu0 : (0 : ℝ) < 1 - t := by linarith
  have hinv : t⁻¹ < 2 := by
    rw [inv_lt_comm₀ ht0 (by norm_num)]
    linarith
  have hinv1 : 1 < t⁻¹ := by
    rw [lt_inv_comm₀ (by norm_num) ht0]
    linarith
  have hfloor : ⌊t⁻¹⌋ = 1 := by
    rw [Int.floor_eq_iff]
    constructor <;> [exact_mod_cast hinv1.le; exact_mod_cast hinv]
  have hstep : gaussMap t = (1 - t) / t := by
    rw [gaussMap, if_neg (ne_of_gt ht0), Int.fract, hfloor]
    push_cast
    field_simp
  rw [hstep]
  have hw0 : (1 - t) / t ≠ 0 := by positivity
  rw [gaussMap, if_neg hune, gaussMap, if_neg hw0, inv_div]
  have hdiff : (1 - t)⁻¹ = t / (1 - t) + 1 := by field_simp; ring
  rw [hdiff, Int.fract_add_one]

/-- **`t ↦ 1 − t` preserves CF-normality** on the irrationals of `(0,1)`: the digit sequences
agree after a shift by at most two. -/
theorem isCFNormal_one_sub {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hirr : Irrational t)
    (ht : IsCFNormal t) : IsCFNormal (1 - t) := by
  rcases lt_trichotomy t (1 / 2) with hlt | heq | hgt
  · refine isCFNormal_of_digit_shift (M := 2) (N := 1) (fun n => ?_) ht
    refine cfDigit_shift_of_iterate (j := 2) (k := 1) ?_ n
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    exact gaussMap_two_one_sub_of_lt ht0 hlt
  · exact absurd heq (by
      intro h
      exact hirr ⟨1 / 2, by rw [h]; norm_num⟩)
  · refine isCFNormal_of_digit_shift (M := 1) (N := 2) (fun n => ?_) ht
    refine cfDigit_shift_of_iterate (j := 1) (k := 2) ?_ n
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    exact gaussMap_one_sub_of_gt hgt ht1

/-! ## The generator `x ↦ −x` -/

/-- The fractional part of an irrational lies strictly inside `(0,1)`. -/
lemma fract_mem_Ioo_of_irrational {x : ℝ} (hirr : Irrational x) :
    0 < Int.fract x ∧ Int.fract x < 1 ∧ Irrational (Int.fract x) := by
  have h1 : Irrational (Int.fract x) := by
    rw [Int.fract]
    exact hirr.sub_intCast _
  refine ⟨?_, Int.fract_lt_one x, h1⟩
  rcases (Int.fract_nonneg x).lt_or_eq with h | h
  · exact h
  · exact absurd h.symm (by
      intro h0
      exact h1 ⟨0, by rw [h0]; norm_num⟩)

/-- **`x ↦ −x` preserves CF-normality** (in the `Int.fract` sense). -/
theorem isCFNormal_fract_neg {x : ℝ} (h : IsCFNormal (Int.fract x)) :
    IsCFNormal (Int.fract (-x)) := by
  have hirr : Irrational x := irrational_of_isCFNormal_fract h
  obtain ⟨h0, h1, hfirr⟩ := fract_mem_Ioo_of_irrational hirr
  rw [Int.fract_neg (ne_of_gt h0)]
  exact isCFNormal_one_sub h0 h1 hfirr h

/-! ## The generators -/

/-- `x ↦ x + n`: the fractional part does not move at all. -/
theorem mobiusCFN_add_int (n : ℤ) : MobiusCFN 1 n 0 1 := by
  intro x _ hx
  simpa [Int.fract_add_intCast] using hx

/-- `x ↦ 1/x` for positive `x`: one Gauss step in one direction or the other. -/
lemma isCFNormal_fract_inv_of_pos {x : ℝ} (hx : 0 < x) (h : IsCFNormal (Int.fract x)) :
    IsCFNormal (Int.fract x⁻¹) := by
  have hirr : Irrational x := irrational_of_isCFNormal_fract h
  have hx0 : x ≠ 0 := ne_of_gt hx
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · -- `x ∈ (0,1)`: `fract x⁻¹ = T x`
    have hfx : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx.le, hlt⟩
    have hgauss : gaussMap x = Int.fract x⁻¹ := by rw [gaussMap, if_neg hx0]
    rw [← hgauss]
    exact isCFNormal_gaussMap (by rwa [hfx] at h)
  · exact absurd heq (by intro h0; exact hirr ⟨1, by rw [h0]; norm_num⟩)
  · -- `x > 1`: `x⁻¹ ∈ (0,1)` and `T x⁻¹ = fract x`
    have hinv0 : 0 < x⁻¹ := by positivity
    have hinv1 : x⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]
      exact Or.inr hgt
    have hfinv : Int.fract x⁻¹ = x⁻¹ := Int.fract_eq_self.mpr ⟨hinv0.le, hinv1⟩
    rw [hfinv]
    refine isCFNormal_of_gaussMap ?_
    rw [gaussMap, if_neg (ne_of_gt hinv0), inv_inv]
    exact h

/-- `x ↦ 1/x`. -/
theorem mobiusCFN_inv : MobiusCFN 0 1 1 0 := by
  intro x hden hx
  have hx0 : x ≠ 0 := by simpa using hden
  have hgoal : ((0 : ℤ) : ℝ) * x + ((1 : ℤ) : ℝ) = 1 := by push_cast; ring
  have hgoal2 : ((1 : ℤ) : ℝ) * x + ((0 : ℤ) : ℝ) = x := by push_cast; ring
  rw [hgoal, hgoal2, one_div]
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · -- negative: conjugate the positive case by `x ↦ −x`
    have hnx : IsCFNormal (Int.fract (-x)) := isCFNormal_fract_neg hx
    have hpos' : 0 < -x := by linarith
    have := isCFNormal_fract_inv_of_pos hpos' hnx
    have hstep := isCFNormal_fract_neg this
    rwa [show -(-x)⁻¹ = x⁻¹ by field_simp] at hstep
  · exact isCFNormal_fract_inv_of_pos hpos hx

/-- Negating every entry does not change the Möbius map. -/
theorem mobiusCFN_neg_entries {a b c d : ℤ} (h : MobiusCFN a b c d) :
    MobiusCFN (-a) (-b) (-c) (-d) := by
  intro x hden hx
  have hden' : (c : ℝ) * x + d ≠ 0 := by
    intro h0
    apply hden
    push_cast
    push_cast at h0
    linarith
  have heq : (((-a : ℤ) : ℝ) * x + ((-b : ℤ) : ℝ)) / (((-c : ℤ) : ℝ) * x + ((-d : ℤ) : ℝ))
      = ((a : ℝ) * x + b) / ((c : ℝ) * x + d) := by
    push_cast
    rw [show -(a : ℝ) * x + -(b : ℝ) = -((a : ℝ) * x + b) by ring,
      show -(c : ℝ) * x + -(d : ℝ) = -((c : ℝ) * x + d) by ring, neg_div_neg_eq]
  rw [heq]
  exact h x hden' hx

/-- `x ↦ −x`. -/
theorem mobiusCFN_neg : MobiusCFN (-1) 0 0 1 := by
  intro x _ hx
  have : (((-1 : ℤ) : ℝ) * x + ((0 : ℤ) : ℝ)) / (((0 : ℤ) : ℝ) * x + ((1 : ℤ) : ℝ)) = -x := by
    push_cast; ring
  rw [this]
  exact isCFNormal_fract_neg hx

/-! ## The `GL₂(ℤ)` descent, once, for any composition-closed matrix property -/

/-- A property of integer matrices that is closed under the operations the Euclidean descent
uses.  Both `MobiusCFN` and `MobiusCFEquiv` are such properties, so the descent is written
once. -/
structure MobiusClosure (P : ℤ → ℤ → ℤ → ℤ → Prop) : Prop where
  /-- closed under matrix product, given a nonsingular inner factor -/
  comp : ∀ {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ}, a₂ * d₂ - b₂ * c₂ ≠ 0 →
    P a₁ b₁ c₁ d₁ → P a₂ b₂ c₂ d₂ →
    P (a₁ * a₂ + b₁ * c₂) (a₁ * b₂ + b₁ * d₂) (c₁ * a₂ + d₁ * c₂) (c₁ * b₂ + d₁ * d₂)
  /-- the translations `x ↦ x + n` -/
  addInt : ∀ n : ℤ, P 1 n 0 1
  /-- the inversion `x ↦ 1/x` -/
  inv : P 0 1 1 0
  /-- the reflection `x ↦ −x` -/
  neg : P (-1) 0 0 1
  /-- negating every entry is the same Möbius map -/
  negEntries : ∀ {a b c d : ℤ}, P a b c d → P (-a) (-b) (-c) (-d)

variable {P : ℤ → ℤ → ℤ → ℤ → Prop}

lemma mobius_congr {a b c d a' b' c' d' : ℤ} (ha : a = a') (hb : b = b') (hc : c = c')
    (hd : d = d') (h : P a b c d) : P a' b' c' d' := by
  subst ha; subst hb; subst hc; subst hd; exact h

/-- **The `GL₂(ℤ)` descent.**  `PGL₂(ℤ)` is generated by `x ↦ x + n` and `x ↦ 1/x`; the proof
is the Euclidean algorithm on the bottom-left entry, `M = T_q · S · M''` with `|r| < |c|`. -/
theorem mobius_gl2_of_closure (hP : MobiusClosure P) :
    ∀ a b c d : ℤ, a * d - b * c = 1 ∨ a * d - b * c = -1 → P a b c d := by
  have key : ∀ n : ℕ, ∀ a b c d : ℤ, c.natAbs = n →
      (a * d - b * c = 1 ∨ a * d - b * c = -1) → P a b c d := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a b c d hn hdet
      rcases eq_or_ne c 0 with hc0 | hc0
      · -- `c = 0`: `a * d = ±1`, so the map is `x ↦ ±x + b'`
        subst hc0
        have had : a * d = 1 ∨ a * d = -1 := by simpa using hdet
        have hunit : ∀ u v : ℤ, u * v = 1 ∨ u * v = -1 → u = 1 ∨ u = -1 := by
          intro u v h
          rcases h with h | h
          · exact Int.isUnit_iff.mp (isUnit_of_dvd_one ⟨v, h.symm⟩)
          · exact Int.isUnit_iff.mp (isUnit_of_dvd_one ⟨-v, by linarith⟩)
        have ha : a = 1 ∨ a = -1 := hunit a d had
        have had' : d * a = 1 ∨ d * a = -1 := by simpa [mul_comm] using had
        have hd : d = 1 ∨ d = -1 := hunit d a had'
        have hT : ∀ m : ℤ, P 1 m 0 1 := hP.addInt
        have hNegT : ∀ m : ℤ, P (-1) (-m) 0 1 := by
          intro m
          have hdet₂ : (1 : ℤ) * 1 - m * 0 ≠ 0 := by norm_num
          have := hP.comp hdet₂ hP.neg (hT m)
          refine mobius_congr ?_ ?_ ?_ ?_ this <;> ring
        rcases ha with rfl | rfl <;> rcases hd with rfl | rfl
        · exact hT b
        · exact mobius_congr (by ring) (by ring) (by ring) (by ring)
            (hP.negEntries (hNegT b))
        · exact mobius_congr (by ring) (by ring) (by ring) (by ring) (hNegT (-b))
        · exact mobius_congr (by ring) (by ring) (by ring) (by ring)
            (hP.negEntries (hT (-b)))
      · -- `c ≠ 0`: one Euclidean step, `M = T_q · S · M''`
        set q : ℤ := a / c with hq
        set r : ℤ := a % c with hr
        have hra : r + c * q = a := by
          rw [hr, hq, Int.emod_def]
          ring
        have hr0 : 0 ≤ r := Int.emod_nonneg a hc0
        have hrlt : r < |c| := Int.emod_lt_abs a hc0
        have hlt : r.natAbs < n := by
          rw [← hn, Int.abs_eq_natAbs] at *
          omega
        have hdet'' : c * (b - q * d) - d * r = 1 ∨ c * (b - q * d) - d * r = -1 := by
          rcases hdet with h | h
          · exact Or.inr (by linear_combination -h - d * hra)
          · exact Or.inl (by linear_combination -h - d * hra)
        have hM'' := ih _ hlt c d r (b - q * d) rfl hdet''
        have hdetM'' : c * (b - q * d) - d * r ≠ 0 := by
          rcases hdet'' with h | h <;> rw [h] <;> norm_num
        have step1 : P r (b - q * d) c d :=
          mobius_congr (by ring) (by ring) (by ring) (by ring)
            (hP.comp hdetM'' hP.inv hM'')
        have hdet1 : r * d - (b - q * d) * c ≠ 0 := by
          intro h0
          rcases hdet'' with h | h
          · exact absurd (by linear_combination h + h0 : (0 : ℤ) = 1) (by norm_num)
          · exact absurd (by linear_combination h + h0 : (0 : ℤ) = -1) (by norm_num)
        have step2 := hP.comp hdet1 (hP.addInt q) step1
        refine mobius_congr ?_ ?_ ?_ ?_ step2
        · linear_combination hra
        · ring
        · ring
        · ring
  intro a b c d hdet
  exact key c.natAbs a b c d rfl hdet

/-! ## Serret: the `GL₂(ℤ)` leaf -/

/-- **Leaf 1 is discharged.**  Every integer matrix of determinant `±1` acts by a composition
of `x ↦ x + n` and `x ↦ 1/x`, each of which moves the CF digit sequence by a bounded shift. -/
theorem mobiusCFNGL2_holds : MobiusCFNGL2 :=
  mobius_gl2_of_closure
    { comp := fun h h₁ h₂ => MobiusCFN.comp h h₁ h₂
      addInt := mobiusCFN_add_int
      inv := mobiusCFN_inv
      neg := mobiusCFN_neg
      negEntries := fun h => mobiusCFN_neg_entries h }

/-! ## Serret's theorem: `GL₂(ℤ)`-equivalent irrationals have meeting Gauss orbits -/

/-- **Serret equivalence**: the Gauss orbits of `y` and `z` meet.  Equivalently the CF
expansions share a tail. -/
def CFEquiv (y z : ℝ) : Prop := ∃ j k : ℕ, gaussMap^[j] y = gaussMap^[k] z

namespace CFEquiv

@[refl] theorem refl (y : ℝ) : CFEquiv y y := ⟨0, 0, rfl⟩

theorem symm {y z : ℝ} (h : CFEquiv y z) : CFEquiv z y := by
  obtain ⟨j, k, h⟩ := h
  exact ⟨k, j, h.symm⟩

theorem trans {y z w : ℝ} (h₁ : CFEquiv y z) (h₂ : CFEquiv z w) : CFEquiv y w := by
  obtain ⟨j, k, hjk⟩ := h₁
  obtain ⟨j', k', hjk'⟩ := h₂
  refine ⟨j + j', k + k', ?_⟩
  rw [add_comm j j', Function.iterate_add_apply, hjk, ← Function.iterate_add_apply,
    add_comm j' k, Function.iterate_add_apply, hjk', ← Function.iterate_add_apply]

/-- CF-normality is a Serret-equivalence invariant. -/
theorem isCFNormal {y z : ℝ} (h : CFEquiv y z) (hz : IsCFNormal z) : IsCFNormal y := by
  obtain ⟨j, k, hjk⟩ := h
  exact isCFNormal_of_digit_shift (cfDigit_shift_of_iterate hjk) hz

end CFEquiv

/-- A nonsingular integer Möbius map sends irrationals to irrationals. -/
lemma irrational_mobius {a b c d : ℤ} (hdet : a * d - b * c ≠ 0) {x : ℝ} (hirr : Irrational x)
    (hden : (c : ℝ) * x + d ≠ 0) :
    Irrational (((a : ℝ) * x + b) / ((c : ℝ) * x + d)) := by
  rintro ⟨q, hq⟩
  rw [eq_div_iff hden] at hq
  rcases eq_or_ne ((a : ℝ) - (q : ℝ) * c) 0 with h0 | h0
  · have ha : (a : ℝ) = (q : ℝ) * c := by linarith
    have hb : (b : ℝ) = (q : ℝ) * d := by linear_combination -hq - x * ha
    apply hdet
    have : ((a * d - b * c : ℤ) : ℝ) = 0 := by push_cast; rw [ha, hb]; ring
    exact_mod_cast this
  · have h0' : (a : ℚ) - q * c ≠ 0 := by
      intro h
      apply h0
      have : (((a : ℚ) - q * c : ℚ) : ℝ) = 0 := by rw [h]; norm_num
      push_cast at this
      linarith
    exact hirr ⟨((q : ℚ) * d - b) / ((a : ℚ) - q * c), by
      push_cast
      rw [div_eq_iff (by push_cast at h0' ⊢; exact_mod_cast h0')]
      linear_combination hq⟩

/-- The per-matrix Serret statement. -/
def MobiusCFEquiv (a b c d : ℤ) : Prop :=
  ∀ x : ℝ, Irrational x → (c : ℝ) * x + d ≠ 0 →
    CFEquiv (Int.fract (((a : ℝ) * x + b) / ((c : ℝ) * x + d))) (Int.fract x)

theorem mobiusCFEquiv_addInt (n : ℤ) : MobiusCFEquiv 1 n 0 1 := by
  intro x _ _
  have : (((1 : ℤ) : ℝ) * x + ((n : ℤ) : ℝ)) / (((0 : ℤ) : ℝ) * x + ((1 : ℤ) : ℝ)) = x + n := by
    push_cast; ring
  rw [this, Int.fract_add_intCast]

/-- `x ↦ −x` in Serret form. -/
theorem cfEquiv_fract_neg {x : ℝ} (hirr : Irrational x) :
    CFEquiv (Int.fract (-x)) (Int.fract x) := by
  obtain ⟨h0, h1, hfirr⟩ := fract_mem_Ioo_of_irrational hirr
  rw [Int.fract_neg (ne_of_gt h0)]
  rcases lt_trichotomy (Int.fract x) (1 / 2) with hlt | heq | hgt
  · refine ⟨2, 1, ?_⟩
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    exact gaussMap_two_one_sub_of_lt h0 hlt
  · exact absurd heq (by intro h; exact hfirr ⟨1 / 2, by rw [h]; norm_num⟩)
  · refine ⟨1, 2, ?_⟩
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    exact gaussMap_one_sub_of_gt hgt h1

/-- `x ↦ 1/x` in Serret form, for positive `x`. -/
lemma cfEquiv_fract_inv_of_pos {x : ℝ} (hx : 0 < x) (hirr : Irrational x) :
    CFEquiv (Int.fract x⁻¹) (Int.fract x) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  rcases lt_trichotomy x 1 with hlt | heq | hgt
  · have hfx : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx.le, hlt⟩
    refine ⟨0, 1, ?_⟩
    simp only [Function.iterate_zero, id_eq, Function.iterate_one, hfx]
    rw [gaussMap, if_neg hx0]
  · exact absurd heq (by intro h; exact hirr ⟨1, by rw [h]; norm_num⟩)
  · have hinv0 : 0 < x⁻¹ := by positivity
    have hinv1 : x⁻¹ < 1 := by rw [inv_lt_one_iff₀]; exact Or.inr hgt
    have hfinv : Int.fract x⁻¹ = x⁻¹ := Int.fract_eq_self.mpr ⟨hinv0.le, hinv1⟩
    refine ⟨1, 0, ?_⟩
    simp only [Function.iterate_one, Function.iterate_zero, id_eq, hfinv]
    rw [gaussMap, if_neg (ne_of_gt hinv0), inv_inv]

theorem mobiusCFEquiv_inv : MobiusCFEquiv 0 1 1 0 := by
  intro x hirr hden
  have hx0 : x ≠ 0 := by simpa using hden
  have hrw : (((0 : ℤ) : ℝ) * x + ((1 : ℤ) : ℝ)) / (((1 : ℤ) : ℝ) * x + ((0 : ℤ) : ℝ)) = x⁻¹ := by
    push_cast; rw [zero_mul, zero_add, add_zero, one_mul, one_div]
  rw [hrw]
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · have hnirr : Irrational (-x) := hirr.neg
    have hpos' : 0 < -x := by linarith
    have h1 : CFEquiv (Int.fract (-x)⁻¹) (Int.fract (-x)) := cfEquiv_fract_inv_of_pos hpos' hnirr
    have h2 : CFEquiv (Int.fract (-x)) (Int.fract x) := cfEquiv_fract_neg hirr
    have h3 : CFEquiv (Int.fract (-(-x)⁻¹)) (Int.fract (-x)⁻¹) :=
      cfEquiv_fract_neg (hnirr.inv)
    have hxi : -(-x)⁻¹ = x⁻¹ := by field_simp
    rw [← hxi]
    exact h3.trans (h1.trans h2)
  · exact cfEquiv_fract_inv_of_pos hpos hirr

theorem mobiusCFEquiv_neg : MobiusCFEquiv (-1) 0 0 1 := by
  intro x hirr _
  have : (((-1 : ℤ) : ℝ) * x + ((0 : ℤ) : ℝ)) / (((0 : ℤ) : ℝ) * x + ((1 : ℤ) : ℝ)) = -x := by
    push_cast; ring
  rw [this]
  exact cfEquiv_fract_neg hirr

theorem mobiusCFEquiv_negEntries {a b c d : ℤ} (h : MobiusCFEquiv a b c d) :
    MobiusCFEquiv (-a) (-b) (-c) (-d) := by
  intro x hirr hden
  have hden' : (c : ℝ) * x + d ≠ 0 := by
    intro h0
    apply hden
    push_cast
    push_cast at h0
    linarith
  have heq : (((-a : ℤ) : ℝ) * x + ((-b : ℤ) : ℝ)) / (((-c : ℤ) : ℝ) * x + ((-d : ℤ) : ℝ))
      = ((a : ℝ) * x + b) / ((c : ℝ) * x + d) := by
    push_cast
    rw [show -(a : ℝ) * x + -(b : ℝ) = -((a : ℝ) * x + b) by ring,
      show -(c : ℝ) * x + -(d : ℝ) = -((c : ℝ) * x + d) by ring, neg_div_neg_eq]
  rw [heq]
  exact h x hirr hden'

theorem mobiusCFEquiv_comp {a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℤ} (hdet₂ : a₂ * d₂ - b₂ * c₂ ≠ 0)
    (h₁ : MobiusCFEquiv a₁ b₁ c₁ d₁) (h₂ : MobiusCFEquiv a₂ b₂ c₂ d₂) :
    MobiusCFEquiv (a₁ * a₂ + b₁ * c₂) (a₁ * b₂ + b₁ * d₂)
      (c₁ * a₂ + d₁ * c₂) (c₁ * b₂ + d₁ * d₂) := by
  intro x hirr hden
  have hden₂ : (c₂ : ℝ) * x + d₂ ≠ 0 := by
    intro h0
    rcases eq_or_ne c₂ 0 with hc | hc
    · apply hdet₂
      have hd₂ : (d₂ : ℝ) = 0 := by rw [hc] at h0; simpa using h0
      have : d₂ = 0 := by exact_mod_cast hd₂
      simp [hc, this]
    · have hcR : (c₂ : ℝ) ≠ 0 := by exact_mod_cast hc
      have hxv : x = (-(d₂ : ℝ)) / (c₂ : ℝ) := by field_simp at h0 ⊢; linarith
      exact hirr ⟨(-(d₂ : ℚ)) / (c₂ : ℚ), by rw [hxv]; push_cast; ring⟩
  set y : ℝ := ((a₂ : ℝ) * x + b₂) / ((c₂ : ℝ) * x + d₂) with hy
  have hyirr : Irrational y := irrational_mobius hdet₂ hirr hden₂
  have hymul : y * ((c₂ : ℝ) * x + d₂) = (a₂ : ℝ) * x + b₂ := by
    rw [hy, div_mul_cancel₀ _ hden₂]
  have hfac : ((c₁ : ℝ) * y + d₁) * ((c₂ : ℝ) * x + d₂)
      = ((c₁ * a₂ + d₁ * c₂ : ℤ) : ℝ) * x + ((c₁ * b₂ + d₁ * d₂ : ℤ) : ℝ) := by
    push_cast
    linear_combination (c₁ : ℝ) * hymul
  have hden₁ : (c₁ : ℝ) * y + d₁ ≠ 0 := fun h0 => hden (by rw [← hfac, h0, zero_mul])
  have hnum : ((a₁ : ℝ) * y + b₁) * ((c₂ : ℝ) * x + d₂)
      = ((a₁ * a₂ + b₁ * c₂ : ℤ) : ℝ) * x + ((a₁ * b₂ + b₁ * d₂ : ℤ) : ℝ) := by
    push_cast
    linear_combination (a₁ : ℝ) * hymul
  have hkey : (((a₁ * a₂ + b₁ * c₂ : ℤ) : ℝ) * x + ((a₁ * b₂ + b₁ * d₂ : ℤ) : ℝ))
      / (((c₁ * a₂ + d₁ * c₂ : ℤ) : ℝ) * x + ((c₁ * b₂ + d₁ * d₂ : ℤ) : ℝ))
      = ((a₁ : ℝ) * y + b₁) / ((c₁ : ℝ) * y + d₁) := by
    rw [← hnum, ← hfac, mul_div_mul_right _ _ hden₂]
  rw [hkey]
  exact (h₁ y hyirr hden₁).trans (h₂ x hirr hden₂)

/-- **Serret's theorem** (the form Vandehey's fibre step needs): if `y` is the image of an
irrational `x` under an integer Möbius map of determinant `±1`, then the Gauss orbits of
`Int.fract y` and `Int.fract x` MEET — the CF expansions share a tail. -/
theorem serret_cfEquiv (a b c d : ℤ) (hdet : a * d - b * c = 1 ∨ a * d - b * c = -1) :
    MobiusCFEquiv a b c d :=
  mobius_gl2_of_closure
    { comp := fun h h₁ h₂ => mobiusCFEquiv_comp h h₁ h₂
      addInt := mobiusCFEquiv_addInt
      inv := mobiusCFEquiv_inv
      neg := mobiusCFEquiv_neg
      negEntries := fun h => mobiusCFEquiv_negEntries h } a b c d hdet

/-- **Vandehey 2017 Theorem 1.1 now has a single open leaf.**  With Serret discharged, the
crux `VandeheyUniformFreq` follows from `MobiusCFNScale` alone: `x ↦ p·x` for prime `p`. -/
theorem vandeheyUniformFreq_of_scale (hScale : MobiusCFNScale) : VandeheyUniformFreq :=
  vandeheyUniformFreq_of_leaves mobiusCFNGL2_holds hScale

end NormalNumbers.Literature

section
open NormalNumbers.Literature
#print axioms mobiusCFNGL2_holds
#print axioms serret_cfEquiv
#print axioms vandeheyUniformFreq_of_scale
end
