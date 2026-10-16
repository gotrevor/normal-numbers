/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MasterConjectures
import NormalNumbers.WallRational
import NormalNumbers.FiniteStateSelection
import NormalNumbers.CantorExactExponent
import NormalNumbers.NormalMeager
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Instances.Irrational

/-!
# A normal number in the ℚ-span of `√2, √3`?

The question (Trevor, 2026-10-05): *either `√2`, or `√3`, or `c₁√2 + c₂√3` for some rationals
`c₁, c₂` is normal.*  Since `c₂ = 0` and `c₁ = 0` are allowed, the disjunction is just
`QSpanNormal b √2 √3` (`sqrt_disjunction_iff`).  By Wall (`isNormal_rat_mul_add`) it is a
one-parameter question: `√3`, or `√2 + c√3` for one rational `c` (`qSpanNormal_iff_line`).

**How hard.**  Every nonzero element of the span is an algebraic irrational, so a proof would
exhibit the first algebraic irrational known to be normal (the Borel conjecture
`MasterConjectures.BorelConjecture` gives it at once, `qSpanNormal_of_borel`).  And unlike the
six-fold adder disjunction (`Adder.adder_sixfold_disjunction_universal`, true for every pair not
both rational), no pair-universal mechanism exists: a pair of sparse Liouville-type numbers,
ℚ-independent with `1`, has no normal number in its span (`exists_pair_qSpan_not_normal`,
frozen).  So a mechanism must use something `√2, √3` have and that pair lacks, such as
algebraicity.

The quantifier swap is where the difficulty sits: `∀ w, ∃ m, w occurs infinitely often in m·α`
holds for every irrational (Mahler 1973, Berend–Boshernitzan 1994, `MahlerMultiplier.lean`);
`∃ c, ∀ w` is the open statement.

## The entropy budget (Ren, 2026-10-05)

A rational combination is computed from the joint digit stream of `(x, y)` by bounded carries and
a finite division state, so its block entropy is at most the joint block entropy, which is at most
the sum of the two marginals at the same time `N`.  Normality is full entropy at every scale,
hence `1 ≤ dim_FS(x) + Dim_FS(y)` (`span_dimension_budget`): one lower dimension, one upper.
Both lower is false: split a normal number's digits into alternating sparse blocks.  Corollary
(`qSpanNormal_sqrt_upperDim`): if the span of `√2, √3` holds a normal number, one of `√2, √3` has
upper finite-state dimension at least `1/2`.  That is open (no algebraic irrational is known to
have positive digit entropy), so the open node implies an open, strictly weaker-looking node.

The budget also explains the Liouville sibling, and gives a second one with no Liouville
behaviour: a pair drawn from the product of `{0,1}`-digit Cantor measures has joint dimension
`log 4 / log 10 < 1` in base 10, so no span element is normal, yet every span element is a.e.
not very well approximable (Bénard–He–Zhang for the self-similar pushforwards); `exists_pair_exponentTwo_qSpan_not_normal`.  So Roth-type
(exponent-2) information about the span cannot force normality either; the missing input is
entropy, nothing Diophantine.
-/

namespace NormalNumbers.QSpan

open MasterConjectures FiniteState Filter CantorExactExponent
open scoped ENNReal

/-- Some nonzero rational combination `c₁x + c₂y` is normal in base `b`. -/
def QSpanNormal (b : ℕ) (x y : ℝ) : Prop :=
  ∃ c₁ c₂ : ℚ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ IsNormal b ((c₁ : ℝ) * x + c₂ * y)

/-- Trevor's disjunction is exactly `QSpanNormal`. -/
theorem sqrt_disjunction_iff (b : ℕ) :
    (IsNormal b (Real.sqrt 2) ∨ IsNormal b (Real.sqrt 3) ∨ QSpanNormal b (Real.sqrt 2) (Real.sqrt 3))
      ↔ QSpanNormal b (Real.sqrt 2) (Real.sqrt 3) := by
  constructor
  · rintro (h | h | h)
    · exact ⟨1, 0, Or.inl one_ne_zero, by simpa using h⟩
    · exact ⟨0, 1, Or.inr one_ne_zero, by simpa using h⟩
    · exact h
  · exact fun h => Or.inr (Or.inr h)

/-- **Wall reduction.**  The span question is the line `x + c·y` plus the point `y`. -/
theorem qSpanNormal_iff_line (b : ℕ) (hb : 2 ≤ b) (x y : ℝ) :
    QSpanNormal b x y ↔ IsNormal b y ∨ ∃ c : ℚ, IsNormal b (x + c * y) := by
  constructor
  · rintro ⟨c₁, c₂, hne, h⟩
    by_cases h1 : c₁ = 0
    · left
      have h2 : c₂ ≠ 0 := hne.resolve_left (not_not.2 h1)
      subst h1
      have := isNormal_rat_mul_add b hb _ (c₂⁻¹) 0 (inv_ne_zero h2) h
      convert this using 1
      push_cast
      field_simp
      ring
    · right
      refine ⟨c₂ / c₁, ?_⟩
      have := isNormal_rat_mul_add b hb _ (c₁⁻¹) 0 (inv_ne_zero h1) h
      convert this using 1
      push_cast
      field_simp
      ring
  · rintro (h | ⟨c, h⟩)
    · exact ⟨0, 1, Or.inr one_ne_zero, by simpa using h⟩
    · exact ⟨1, c, Or.inl one_ne_zero, by simpa using h⟩

/-- The Borel conjecture settles it (via `√2` alone). -/
theorem qSpanNormal_of_borel (hB : BorelConjecture) (b : ℕ) (hb : 2 ≤ b) :
    QSpanNormal b (Real.sqrt 2) (Real.sqrt 3) :=
  ⟨1, 0, Or.inl one_ne_zero, by simpa using hB _ irrational_sqrt_two isAlgebraic_sqrt_two b hb⟩

/-- **Open node: a normal number on the line `√2 + c√3`, or `√3`.**  Believed (~99%, it follows
from Borel); no mechanism (0% for a proof here).  Crux-linked to
`exists_pair_qSpan_not_normal`: a proof must use something the Liouville pair lacks. -/
theorem qSpanNormal_sqrt_two_sqrt_three (b : ℕ) (hb : 2 ≤ b) :
    QSpanNormal b (Real.sqrt 2) (Real.sqrt 3) := by
  sorry

/-- **Sibling: a ℚ-independent pair whose ℚ-span holds no normal number.**

The proof is a Baire-category argument.  For each nonzero rational pair `(c₁, c₂)`, the
linear form `(x, y) ↦ c₁x + c₂y` is a continuous open surjection.  Irrational reals are
residual, while base-`b` normal reals are meagre (`isMeagre_setOf_isNormal`), so the inverse image
of the irrational non-normal reals is residual in `ℝ × ℝ`.  Intersecting over the countable
set `ℚ × ℚ` gives a pair for which every nonzero rational linear combination is both
irrational and non-normal. -/
theorem exists_pair_qSpan_not_normal (b : ℕ) (hb : 2 ≤ b) :
    ∃ x y : ℝ, (∀ c₀ c₁ c₂ : ℚ, (c₁ : ℝ) * x + c₂ * y = c₀ → c₁ = 0 ∧ c₂ = 0) ∧
      ¬ QSpanNormal b x y := by
  let form (p : ℚ × ℚ) : ℝ × ℝ →L[ℝ] ℝ :=
    (((p.1 : ℝ) • ContinuousLinearMap.id ℝ ℝ).coprod
      ((p.2 : ℝ) • ContinuousLinearMap.id ℝ ℝ))
  have form_apply (p : ℚ × ℚ) (v : ℝ × ℝ) :
      form p v = (p.1 : ℝ) * v.1 + p.2 * v.2 := by
    simp [form, smul_eq_mul]
  have form_surj (p : ℚ × ℚ) (hp : p ≠ 0) : Function.Surjective (form p) := by
    intro z
    by_cases h₁ : p.1 = 0
    · have h₂ : p.2 ≠ 0 := by
        intro h₂
        apply hp
        ext <;> simp_all
      refine ⟨(0, z / (p.2 : ℝ)), ?_⟩
      rw [form_apply, h₁]
      simp only [Rat.cast_zero, zero_mul, Prod.fst, Prod.snd, zero_add]
      exact mul_div_cancel₀ z (Rat.cast_ne_zero.mpr h₂)
    · refine ⟨(z / (p.1 : ℝ), 0), ?_⟩
      rw [form_apply]
      simp only [Prod.fst, Prod.snd, mul_zero, add_zero]
      exact mul_div_cancel₀ z (Rat.cast_ne_zero.mpr h₁)
  let good : Set (ℝ × ℝ) := ⋂ p : ℚ × ℚ,
    {v | p ≠ 0 → Irrational (form p v) ∧ ¬ IsNormal b (form p v)}
  have hgood : good ∈ residual (ℝ × ℝ) := by
    dsimp only [good]
    refine countable_iInter_mem.2 fun p ↦ ?_
    by_cases hp : p = 0
    · simp [hp]
    · have hmap : Tendsto (form p) (residual (ℝ × ℝ)) (residual ℝ) :=
        tendsto_residual_of_isOpenMap (form p).continuous
          ((form p).isOpenMap (form_surj p hp))
      have hirr : {v : ℝ × ℝ | Irrational (form p v)} ∈ residual (ℝ × ℝ) :=
        hmap eventually_residual_irrational
      have hnon : {v : ℝ × ℝ | ¬ IsNormal b (form p v)} ∈ residual (ℝ × ℝ) := by
        change (form p) ⁻¹' {z : ℝ | ¬ IsNormal b z} ∈ residual (ℝ × ℝ)
        apply hmap
        exact isMeagre_setOf_isNormal b hb
      rw [show {v : ℝ × ℝ | p ≠ 0 →
          Irrational (form p v) ∧ ¬ IsNormal b (form p v)} =
        {v : ℝ × ℝ | Irrational (form p v)} ∩
          {v : ℝ × ℝ | ¬ IsNormal b (form p v)} by ext; simp [hp]]
      exact Filter.inter_mem hirr hnon
  obtain ⟨v, hv⟩ := nonempty_of_not_isMeagre (not_isMeagre_of_mem_residual hgood)
  have hv' (p : ℚ × ℚ) (hp : p ≠ 0) :
      Irrational (form p v) ∧ ¬ IsNormal b (form p v) := by
    exact (Set.mem_iInter.mp hv p) hp
  refine ⟨v.1, v.2, ?_, ?_⟩
  · intro c₀ c₁ c₂ heq
    by_contra hne
    have hp : (c₁, c₂) ≠ (0, 0) := by
      intro hp
      apply hne
      exact Prod.mk_eq_zero.mp hp
    apply (hv' (c₁, c₂) hp).1
    refine ⟨c₀, ?_⟩
    rw [form_apply]
    exact_mod_cast heq.symm
  · rintro ⟨c₁, c₂, hne, hnormal⟩
    have hp : (c₁, c₂) ≠ (0, 0) := by
      intro hp
      have hz := Prod.mk_eq_zero.mp hp
      exact hne.elim (fun h ↦ h hz.1) (fun h ↦ h hz.2)
    apply (hv' (c₁, c₂) hp).2
    rw [form_apply]
    exact hnormal

/-- Base-`b` digit sequence of `x` (of its fractional part), as letters of `Fin b`. -/
noncomputable def digitSeq (b : ℕ) (hb : 0 < b) (x : ℝ) : ℕ → Fin b :=
  fun i => ⟨digitOf b (Int.fract x) i, Nat.mod_lt _ hb⟩

/-- Upper (strong) finite-state dimension in decompression form: `fsDim` with `limsup`.  The
analogue of Doty–Moser's characterization for `Dim_FS`; that the two agree is not checked. -/
noncomputable def fsDimUpper {k : ℕ} (S : ℕ → Fin k) : ℝ≥0∞ :=
  ⨅ T : FST k, limsup (fun n : ℕ => ((infoK T (pre S n) : ℕ∞) : ℝ≥0∞) / (n : ℝ≥0∞)) atTop

theorem fsDim_le_fsDimUpper {k : ℕ} (S : ℕ → Fin k) : fsDim S ≤ fsDimUpper S :=
  iInf_mono fun _ => Filter.liminf_le_limsup

/-- **Entropy budget for a rational combination.**  Confidence 85%.

English proof.  Write `c₁x + c₂y = (a x + a' y)/q` with integers.  A length-`ℓ` block of the
combination at position `i` is a function of the length-`ℓ` blocks of `x` and `y` at `i`, the
carry into `i + ℓ` (at most `|a| + |a'| + 1` values) and the division remainder (`q` values).
So, for the empirical block laws up to time `N`, `H_ℓ(z) ≤ H_ℓ(x, y) + O(1) ≤ H_ℓ(x) + H_ℓ(y) +
O(1)`.  Normality makes `H_ℓ(z)/(ℓ log b) → 1` along every `N`; take liminf in `N` with the `y`
term bounded by its limsup, divide by `ℓ log b`, let `ℓ → ∞`, and use the block-entropy
characterization of `dim_FS`/`Dim_FS` (Bourke–Hitchcock–Vinodchandran 2005; decompression forms
Doty–Moser 2006).  The lower/upper split is needed: digits of a normal number split into
alternating sparse blocks give `x + y` normal with `dim_FS x = dim_FS y = 0`. -/
theorem span_dimension_budget (b : ℕ) (hb : 2 ≤ b) (x y : ℝ) (c₁ c₂ : ℚ)
    (hz : IsNormal b ((c₁ : ℝ) * x + c₂ * y)) :
    1 ≤ fsDim (digitSeq b (by omega) x) + fsDimUpper (digitSeq b (by omega) y) := by
  sorry

/-- **The open node implies an entropy node.**  If some nonzero rational combination of `√2` and
`√3` is normal, one of them has upper finite-state dimension at least `1/2`. -/
theorem qSpanNormal_sqrt_upperDim (b : ℕ) (hb : 2 ≤ b)
    (h : QSpanNormal b (Real.sqrt 2) (Real.sqrt 3)) :
    1 / 2 ≤ fsDimUpper (digitSeq b (by omega) (Real.sqrt 2)) ∨
      1 / 2 ≤ fsDimUpper (digitSeq b (by omega) (Real.sqrt 3)) := by
  obtain ⟨c₁, c₂, -, hz⟩ := h
  have h1 := span_dimension_budget b hb _ _ c₁ c₂ hz
  have h2 := h1.trans (add_le_add_left (fsDim_le_fsDimUpper (digitSeq b (by omega) (Real.sqrt 2))) _)
  by_contra hc
  push Not at hc
  have := ENNReal.add_lt_add hc.1 hc.2
  rw [ENNReal.add_halves] at this
  exact absurd (h2.trans_lt this) (lt_irrefl _)

/-- **Sibling: exponent-2 information does not force a normal span element.**  Confidence 80%.

English construction.  Let `μ` be the law of `Σ dᵢ 10^{−i−1}` with independent fair digits
`dᵢ ∈ {0, 1}`, and draw `(x, y)` from `μ × μ`.  (1) ℚ-independence of `1, x, y`: each relation
`c₀ + c₁x + c₂y = 0` with `(c₁, c₂) ≠ 0` cuts out a `μ × μ`-null set (a line meets the product of
two non-atomic measures in a null set), and there are countably many.  (2) Exponent 2: for
`(c₁, c₂) ≠ 0`, the pushforward of `μ × μ` under `c₁x + c₂y` is a self-similar measure with ratio
`1/10` and finitely many rational translations (an affine image of one when the IFS overlaps), so
Bénard–He–Zhang (Khintchine convergence for self-similar measures) gives exponent exactly 2 a.e.
(Dirichlet gives `≥ 2`); countably many combinations.  (3) No normal element:
`span_dimension_budget` with `dim_FS x, Dim_FS y ≤ log 2 / log 10` a.e., so the sum is
`log 4 / log 10 < 1`. -/
theorem exists_pair_exponentTwo_qSpan_not_normal :
    ∃ x y : ℝ, (∀ c₀ c₁ c₂ : ℚ, (c₁ : ℝ) * x + c₂ * y = c₀ → c₁ = 0 ∧ c₂ = 0) ∧
      (∀ c₁ c₂ : ℚ, (c₁ ≠ 0 ∨ c₂ ≠ 0) → HasIrrExponent ((c₁ : ℝ) * x + c₂ * y) 2) ∧
      ¬ QSpanNormal 10 x y := by
  sorry

end NormalNumbers.QSpan
