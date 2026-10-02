/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyS7Memory
import NormalNumbers.CFOrbitFreq
import NormalNumbers.VandeheySmith

/-!
# The ergodic route: §7 Problem 1 from a ONE-SIDED bound

Every route to §7 Problem 1 so far has gone through `AffineUniformFreq` — *some* limit exists and
does not depend on `x` — and then let `affineCFN_of_uniformFreq` identify it.  That is why the
crux `SampledUniformCount` is hard: an `x`-independent **limit** is a two-sided, exact demand.

This module opens a second route which never asks for a limit at all.

## The reduction

Write `z = Int.fract (q x + r₀)`.  `isCFNormal_of_irrational_orbit_freq` (already in the build)
says `z` is CF-normal as soon as its Gauss-orbit visit frequencies to every cylinder converge to
`γ`.  Classical ergodic theory supplies exactly that from a **one-sided, unsigned** hypothesis:

> if the orbit's visit frequencies to *intervals* are uniformly absolutely continuous —
> `#{j < p : Gʲz ∈ (a,b)} / p ≤ C (b − a) + o(1)` — then the orbit equidistributes for `γ`.

Why: the empirical measures are then tight (take `(0,δ)` and `(1−δ,1)`), so they have weak-∗
limit points; every limit point is `gaussMap`-invariant (Krylov–Bogolyubov) and has density
`≤ C`; the Gauss measure is the unique absolutely continuous invariant probability (`gaussMap` is
ergodic for `γ`, and the Radon–Nikodym derivative of one invariant measure against another is
itself invariant, hence constant); so every limit point is `γ` and the sequence converges.

That implication is `GaussACRigidity C`, a **cited literature input** in the repo's sense
(standing rule 3): a named hypothesis `Prop`, never an `axiom`.  Its own discharge is a real
target — the repo already owns the two hard inputs, `gaussMeasure_preimage` (invariance) and
`Literature.philipp_psi_mixing_holds` (ψ-mixing, hence mixing, hence ergodicity) — and is
tracked in `PENDING_WORK.md`.

## What this buys

`affineCFN_of_orbitACBound` proves the frozen target from

* `AffineImageIrrational q r₀` — the image of a CF-normal number is irrational (free for
  rational `q`; for `q = φ` it says `φ x ∉ ℚ`, which holds because `p / (qφ)` is a quadratic
  irrational and quadratic irrationals have eventually periodic, hence non-Gauss, digits);
* `GaussACRigidity C` — cited;
* `OrbitACBound q r₀ C` — **the new crux**.

`OrbitACBound` is strictly weaker in kind than `SampledUniformCount`: it is an *upper* bound, with
an *absolute constant*, and it never mentions `x`-independence.  The limit's value is then forced
to be `γ`, so `affineCFN_of_uniformFreq`'s either-or endgame is not needed either.  Both routes
must ultimately beat the same obstruction — the machine's state is a genuine hidden variable
(`VandeheyS7Memory`) — but a one-sided bound with slack is a different, and much more forgiving,
demand than an exact `x`-free limit.

## Guard rule

Content locator: `isCFNormal_of_gaussACRigidity` — the cited Prop's whole content is
"uniformly absolutely continuous orbit ⇒ CF-normal", and nothing beyond it;
`affineImageIrrational_one` — the identity map satisfies the irrationality hypothesis, so it is
not vacuous.  Degenerate cases: `one_le_of_gaussACRigidity_hyp` — the hypothesis forces `1 ≤ C`
(take `(a,b) = (0,1)`), so `gaussACRigidity_of_lt_one` shows the Prop is VACUOUS for `C < 1` and
carries content only for `C ≥ 1`; `one_le_of_orbitACBound` — the same on the crux, so a bound with
`C < 1` is unattainable rather than merely strong; and
`not_affineImageIrrational_zero_of_exists` — `q = 0` fails outright.
-/

namespace NormalNumbers.VandeheyS7

open Filter NormalNumbers

/-! ## The three hypotheses -/

/-- The image of every CF-normal input under `x ↦ q x + r₀` is irrational.  Needed because
`isCFNormal_of_irrational_orbit_freq` wants a full Gauss orbit, and rationals leave `(0,1)`. -/
def AffineImageIrrational (q r₀ : ℝ) : Prop :=
  ∀ x : ℝ, IsCFNormal (Int.fract x) → Irrational (q * x + r₀)

/-- **The new crux.**  The image orbit's visit frequency to every subinterval of `(0,1)` is
eventually at most `C` times its length — a ONE-SIDED bound, with an absolute constant, and with
no `x`-independent limit anywhere in it. -/
def OrbitACBound (q r₀ C : ℝ) : Prop :=
  ∀ x : ℝ, IsCFNormal (Int.fract x) → ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ p : ℕ in atTop,
      blockCount (Set.Ioo a b) p (Int.fract (q * x + r₀)) / p ≤ C * (b - a) + ε

/-- **Cited literature input** (standard ergodic theory).  A full Gauss orbit whose visit
frequencies to intervals are uniformly absolutely continuous equidistributes for the Gauss
measure.  Krylov–Bogolyubov gives an invariant limit point of the empirical measures, the bound
makes it absolutely continuous with density `≤ C`, and `γ` is the unique absolutely continuous
`gaussMap`-invariant probability. -/
def GaussACRigidity (C : ℝ) : Prop :=
  ∀ y : ℝ, Irrational y → y ∈ Set.Ioo (0:ℝ) 1 →
    (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ p : ℕ in atTop, blockCount (Set.Ioo a b) p y / p ≤ C * (b - a) + ε) →
    ∀ v : List ℕ, v ≠ [] → (∀ e ∈ v, 1 ≤ e) →
      Tendsto (fun p => blockCount (cfCylinder v) p y / (p : ℝ)) atTop
        (nhds (gaussMeasure (cfCylinder v)).toReal)

/-! ## The reduction -/

/-- `Int.fract` of an irrational is an irrational of `(0,1)`. -/
theorem irrational_fract_mem {z : ℝ} (hz : Irrational z) :
    Irrational (Int.fract z) ∧ Int.fract z ∈ Set.Ioo (0:ℝ) 1 := by
  have hf : Irrational (Int.fract z) := by
    have : Int.fract z = z - (⌊z⌋ : ℝ) := rfl
    rw [this]
    exact Irrational.sub_intCast hz ⌊z⌋
  refine ⟨hf, ?_, Int.fract_lt_one z⟩
  rcases lt_or_eq_of_le (Int.fract_nonneg z) with h | h
  · exact h
  · exact absurd ⟨0, by rw [← h]; norm_num⟩ hf

/-- **The ergodic route to the frozen target.**  Irrationality of the image, the cited rigidity,
and the one-sided bound give `AffineCFN q r₀` outright — no `AffineUniformFreq`, no `RunClock`,
no `SampledUniformCount`, and no either-or endgame. -/
theorem affineCFN_of_orbitACBound {q r₀ C : ℝ}
    (hirr : AffineImageIrrational q r₀) (hrig : GaussACRigidity C)
    (hbound : OrbitACBound q r₀ C) : AffineCFN q r₀ := by
  intro x hx
  obtain ⟨hfz, hmem⟩ := irrational_fract_mem (hirr x hx)
  exact isCFNormal_of_irrational_orbit_freq _ hfz hmem
    (hrig _ hfz hmem fun a b ha hab hb1 ε hε => hbound x hx a b ha hab hb1 ε hε)

/-- `x ↦ φ·x`, on the ergodic route. -/
theorem vandeheyS7_mul_phi_of_orbitACBound {C : ℝ}
    (hirr : AffineImageIrrational Real.goldenRatio 0) (hrig : GaussACRigidity C)
    (hbound : OrbitACBound Real.goldenRatio 0 C) : vandeheyS7_mul_phi :=
  affineCFN_of_orbitACBound hirr hrig hbound

/-- `x ↦ x + φ`, on the ergodic route. -/
theorem vandeheyS7_add_phi_of_orbitACBound {C : ℝ}
    (hirr : AffineImageIrrational 1 Real.goldenRatio) (hrig : GaussACRigidity C)
    (hbound : OrbitACBound 1 Real.goldenRatio C) : vandeheyS7_add_phi :=
  affineCFN_of_orbitACBound hirr hrig hbound

/-! ## Guard rule: locators and degenerate cases -/

/-- Content locator: the cited Prop's entire content is "uniformly absolutely continuous orbit
⇒ CF-normal".  Nothing else is being assumed. -/
theorem isCFNormal_of_gaussACRigidity {C y : ℝ} (hrig : GaussACRigidity C)
    (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    (hb : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ p : ℕ in atTop, blockCount (Set.Ioo a b) p y / p ≤ C * (b - a) + ε) :
    IsCFNormal y :=
  isCFNormal_of_irrational_orbit_freq y hy hmem (hrig y hy hmem hb)

/-- Content locator: the identity map satisfies the irrationality hypothesis, so
`AffineImageIrrational` is not vacuous.  It is `not_isCFNormal_of_not_irrational` plus the fact
that `x` and `Int.fract x` differ by an integer. -/
theorem affineImageIrrational_one : AffineImageIrrational 1 0 := by
  intro x hx
  have hf : Irrational (Int.fract x) := by
    by_contra h
    exact Literature.not_isCFNormal_of_not_irrational h hx
  have hsum : Irrational (Int.fract x + (⌊x⌋ : ℝ)) := Irrational.add_intCast hf ⌊x⌋
  have heq : Int.fract x + (⌊x⌋ : ℝ) = 1 * x + 0 := by
    simp only [Int.fract, one_mul, add_zero]; ring
  rwa [heq] at hsum

/-- Degenerate case: `q = 0` collapses the image to a constant, and `AffineImageIrrational 0 0`
asserts `Irrational 0`, so it fails as soon as one CF-normal number exists. -/
theorem not_affineImageIrrational_zero_of_exists (h : ∃ x : ℝ, IsCFNormal (Int.fract x)) :
    ¬ AffineImageIrrational 0 0 := by
  rintro hA
  obtain ⟨x, hx⟩ := h
  have := hA x hx
  simp only [zero_mul, add_zero] at this
  exact this ⟨0, by norm_num⟩

/-- The orbit of an irrational of `(0,1)` never leaves `(0,1)`, so it visits `(0,1)` at every
one of the first `p` times. -/
theorem blockCount_Ioo_zero_one {y : ℝ} (hy : Irrational y) (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    (p : ℕ) : blockCount (Set.Ioo (0:ℝ) 1) p y = p := by
  rw [blockCount_apply]
  have : ∀ k ∈ Finset.range p, blockIndic (Set.Ioo (0:ℝ) 1) (gaussMap^[k] y) = 1 := by
    intro k _
    exact Set.indicator_of_mem (irrational_orbit y hy hmem k).2 _
  rw [Finset.sum_congr rfl this]
  simp

/-- **Degenerate case: the constant cannot be below `1`.**  Taking `(a,b) = (0,1)` makes the
left-hand side identically `1`, so the hypothesis of `GaussACRigidity` forces `1 ≤ C`. -/
theorem one_le_of_gaussACRigidity_hyp {C y : ℝ} (hy : Irrational y)
    (hmem : y ∈ Set.Ioo (0:ℝ) 1)
    (hb : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ p : ℕ in atTop, blockCount (Set.Ioo a b) p y / p ≤ C * (b - a) + ε) :
    1 ≤ C := by
  by_contra hC
  push_neg at hC
  set ε : ℝ := (1 - C) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨p, hp, hp1⟩ := ((hb 0 1 le_rfl zero_le_one le_rfl ε hε0).and
    (eventually_gt_atTop 0)).exists
  have hpr : (0:ℝ) < p := by exact_mod_cast hp1
  rw [blockCount_Ioo_zero_one hy hmem p, div_self hpr.ne'] at hp
  simp only [sub_zero, mul_one] at hp
  rw [hε] at hp
  linarith

/-- Consequently `GaussACRigidity C` is **vacuously true** for `C < 1`: its hypothesis is
unsatisfiable, so the Prop carries content only for `C ≥ 1`. -/
theorem gaussACRigidity_of_lt_one {C : ℝ} (hC : C < 1) : GaussACRigidity C := by
  intro y hy hmem hb
  exact absurd (one_le_of_gaussACRigidity_hyp hy hmem hb) (not_le.mpr hC)

/-- **Degenerate case on the crux.**  The same computation on the image orbit: a bound with
`C < 1` is unattainable, not merely strong. -/
theorem one_le_of_orbitACBound {q r₀ C : ℝ} (hirr : AffineImageIrrational q r₀)
    (hbound : OrbitACBound q r₀ C) (h : ∃ x : ℝ, IsCFNormal (Int.fract x)) : 1 ≤ C := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨hfz, hmem⟩ := irrational_fract_mem (hirr x hx)
  exact one_le_of_gaussACRigidity_hyp hfz hmem
    fun a b ha hab hb1 ε hε => hbound x hx a b ha hab hb1 ε hε

section Audit

#print axioms irrational_fract_mem
#print axioms affineCFN_of_orbitACBound
#print axioms vandeheyS7_mul_phi_of_orbitACBound
#print axioms vandeheyS7_add_phi_of_orbitACBound
#print axioms isCFNormal_of_gaussACRigidity
#print axioms affineImageIrrational_one
#print axioms blockCount_Ioo_zero_one
#print axioms one_le_of_gaussACRigidity_hyp
#print axioms gaussACRigidity_of_lt_one
#print axioms one_le_of_orbitACBound

end Audit

end NormalNumbers.VandeheyS7
