/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-SA: `StateData` is vacuous too — the repair of S7-SC did not go deep enough

S7-SC found `BlockCoupling` satisfiable for free and repaired it by pinning the sets to a family of
`MobState`s (`StateCoupling`, `StateData`).  The pinning is not enough.  `StateData` quantifies
existentially over the state family `s : ℕ → MobState`, and a `MobState` may be chosen *after*
seeing the two orbits: for the single input point `t = Gⁿx` that the coupling ever evaluates, the
scaling state `lowState (Gⁿy / Gⁿx)` — a legitimate `MobState`, width `Gⁿy/Gⁿx`, distortion `1` —
sends `Gⁿx` to `Gⁿy` exactly.  With the clock `N n = n` every block has length one, and the pinned
pullback set `stateBlockSet (s n) w 0` then contains `Gⁿx` iff `Gⁿy ∈ I_w`.  So

    StateData q r₀ C   ⟸   OrbitWordBound q r₀ C

(`stateData_of_orbitWordBound`), i.e. the bundle is again a restatement of its own conclusion, and
`orbitWordBound_of_stateData` closes a circle.  Certified in kernel here.

## What this says about the pinning rule

S7-SC's lesson was "pin the witnesses".  The sharper lesson is that pinning a witness to a *type*
(`MobState`) pins nothing: the type is large enough to interpolate any single pair of points.  A
transducer hypothesis has content only when the state family is pinned to the input *as a function*
— i.e. by a recursion `s 0 = Φ`, `s (n+1) = (read/emit step applied to s n)` — so that `s n` is
determined by `x₁…xₙ` and cannot be chosen with knowledge of `Gⁿy`.  That recursion is exactly the
`MobState.comp` cocycle built in S7-RC/S7-E2/S7-CY, and `CocycleData` below states the bundle in
that form: the *only* existential left is over the emitted lengths, and the states are then forced.

The `γ`-mass side is unaffected: `MobState.gaussMeasure_preimage_tower_le` still prices the pinned
sets.  What the audit removes is the illusion that the mass bound alone gives the bundle content;
it does not, because the cheap witness has distortion `1` and satisfies every mass bound.
-/
import NormalNumbers.VandeheyS7Audit

namespace NormalNumbers.VandeheyS7

open Filter MeasureTheory NormalNumbers

/-! ## The cheap state family -/

/-- The scaling state sending `Gⁿx` to `Gⁿy`. -/
noncomputable def ratioState {x y : ℝ} (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hy : ∀ k, gaussMap^[k] y ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) : MobState :=
  lowState (gaussMap^[n] y / gaussMap^[n] x) (div_pos (hy n).1 (hx n).1)

lemma ratioState_apply {x y : ℝ} (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hy : ∀ k, gaussMap^[k] y ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    (ratioState hx hy n).mob (gaussMap^[n] x) = gaussMap^[n] y := by
  unfold ratioState
  rw [lowState_mob]
  exact div_mul_cancel₀ _ (hx n).1.ne'

/-- **The cheap coupling.**  With the unit clock, the scaling family satisfies `StateCoupling`
for *every* word and every pair of full orbits. -/
theorem stateCoupling_ratioState {w : List ℕ} {x y : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hy : ∀ k, gaussMap^[k] y ∈ Set.Ioo (0:ℝ) 1) :
    StateCoupling w x y (fun n => n) (ratioState hx hy) where
  base := rfl
  strictMono := strictMono_id
  couple := by
    intro n j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [Nat.add_zero]
    constructor
    · intro h
      refine ⟨⟨?_, ?_⟩, hx n⟩
      · simpa [Set.mem_preimage, ratioState_apply hx hy n] using h
      · simpa [ratioState_apply hx hy n] using hy n
    · rintro ⟨⟨h1, -⟩, -⟩
      simpa [Set.mem_preimage, ratioState_apply hx hy n] using h1

/-- On the unit clock the pinned block count at `Gⁿx` is just the image indicator at `Gⁿy`. -/
lemma blockHitCount_ratioState {w : List ℕ} {x y : ℝ}
    (hx : ∀ k, gaussMap^[k] x ∈ Set.Ioo (0:ℝ) 1)
    (hy : ∀ k, gaussMap^[k] y ∈ Set.Ioo (0:ℝ) 1) (n : ℕ) :
    blockHitCount (stateBlockSet (ratioState hx hy n) w) 1 (gaussMap^[n] x)
      = blockIndic (cfCylinder w) (gaussMap^[n] y) := by
  have h := (stateCoupling_ratioState (w := w) hx hy).couple n 0 (by omega)
  simp only [Nat.add_zero] at h
  unfold blockHitCount blockIndic
  rw [Finset.sum_range_one]
  by_cases hmem : gaussMap^[n] y ∈ cfCylinder w
  · rw [Set.indicator_of_mem (h.1 hmem), Set.indicator_of_mem hmem]
    rfl
  · rw [Set.indicator_of_notMem (fun hc => hmem (h.2 hc)), Set.indicator_of_notMem hmem]

/-! ## The circle -/

lemma tendsto_succ_div_self : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 1) := by
  have h : ∀ᶠ n : ℕ in atTop, ((n + 1 : ℕ) : ℝ) / (n : ℝ) = 1 + (n : ℝ)⁻¹ := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    push_cast
    field_simp
  refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm h) ?_
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa using (tendsto_const_nhds (x := (1:ℝ)) (f := (atTop : Filter ℕ))).add h2

/-- **S7-SA, the defect.**  The crux implies the bundle that was supposed to reduce to it. -/
theorem stateData_of_orbitWordBound {q r₀ C : ℝ} (hirr : AffineImageIrrational q r₀)
    (h : OrbitWordBound q r₀ C) : StateData q r₀ C := by
  intro x hx w hw
  have hx0 : Irrational x := Literature.irrational_of_isCFNormal_fract hx
  have hxirr : Irrational (Int.fract x) := (irrational_fract_mem hx0).1
  have hxmem : Int.fract x ∈ Set.Ioo (0:ℝ) 1 := (irrational_fract_mem hx0).2
  have hyirr0 : Irrational (q * x + r₀) := hirr x hx
  have hyirr : Irrational (Int.fract (q * x + r₀)) := (irrational_fract_mem hyirr0).1
  have hymem : Int.fract (q * x + r₀) ∈ Set.Ioo (0:ℝ) 1 := (irrational_fract_mem hyirr0).2
  have hxo : ∀ k, gaussMap^[k] (Int.fract x) ∈ Set.Ioo (0:ℝ) 1 :=
    fun k => (irrational_orbit _ hxirr hxmem k).2
  have hyo : ∀ k, gaussMap^[k] (Int.fract (q * x + r₀)) ∈ Set.Ioo (0:ℝ) 1 :=
    fun k => (irrational_orbit _ hyirr hymem k).2
  refine ⟨fun n => n, ratioState hxo hyo, stateCoupling_ratioState hxo hyo,
    tendsto_succ_div_self, ?_⟩
  intro ε hε
  filter_upwards [h x hx w hw ε hε, eventually_gt_atTop 0] with p hp hp0
  have hcast : (0:ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hsum : (∑ n ∈ Finset.range p,
      blockHitCount (stateBlockSet (ratioState hxo hyo n) w)
        ((n + 1) - n) (gaussMap^[n] (Int.fract x)))
      = blockCount (cfCylinder w) p (Int.fract (q * x + r₀)) := by
    rw [blockCount_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    simpa using blockHitCount_ratioState (w := w) hxo hyo n
  simp only [hsum]
  rw [div_le_iff₀ hcast] at hp
  simpa using hp

section Audit

#print axioms stateCoupling_ratioState
#print axioms stateData_of_orbitWordBound

end Audit

end NormalNumbers.VandeheyS7
