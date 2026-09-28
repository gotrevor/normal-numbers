/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.VandeheyClassEquidist

set_option maxHeartbeats 1000000

/-!
# The parity split: equidistribution for a PERIODIC automaton

The Raney transducer of `x ↦ D·x` has `det (M · B_j) = − det M`, so the sign of the determinant
is a deterministic period-2 phase: `stateAt lrDelta … i = ι^i (stateAt rplusDelta … i)` for the
phase-corrected automaton `rplusDelta`, and `1[stateAt lrDelta … i = t]` is supported on ONE
parity of `i`.  The joint (window, state) frequency of `lrDelta` is therefore the joint frequency
of the **product automaton**

    `prodStep δ : S × ZMod 2 → ℕ → S × ZMod 2`,   `(s, ε) ↦ (δ s a, ε + 1)`

at the state `(ι^p t, p)`.  `probes/raney_parity_split.py` confirms the answer is half the
unsigned one; this file is the proof.

## Why the plain pin cannot do it

`stateHorizonIntegral (prodStep δ) A n (d,η) (t,p) τ = 1[η+n=p] · stateHorizonIntegral δ A n d t τ`
oscillates in `n` between `0` and `≈ c·γ(A)`, so **no** constant `c'` pins it and
`classEquidistribution_of_pin` is unusable — the period-2 wall of `VandeheyRaneyReach` reappears
at the product.  The window-only half of the statement (`Σ_{i<n} (−1)^i 1[w_i = q] = o(n)`, the CF
analogue of "normal to base `b` ⇒ normal to base `b²`") cannot be bootstrapped from the state
statistics either: summing the signed identity over states gives `0 = o(n)`.

## What does work

Only the **variance** bound needs the pin, and it needs less than the pin gives.  Writing
`sel η p k := 1[η + k = p]`, the product automaton's deviation function factors through the
ORIGINAL automaton's events,

    `devFun (prodStep δ) (d,η) (t,p) q L k y = sel η p k · 1[J_k] − L · 1[W_k]`,

so the two-point integral is the same four masses as before with `sel`-coefficients.  Taking the
reference constant `L := c/2` (half the pin's constant), the constant parts cancel EXACTLY and
what survives is

    `mean(k, k') = e(k') · R(k)`,   `e(k') = ±1` alternating,   `|R(k)| ≤ 1`,

with `R` depending on `k` alone.  In the variance double sum the inner sum of `e(k')` over a
contiguous range is `O(1)`, so the mean part contributes `O(K)` and not `O(K²)`: the alternating
factor performs the cancellation that a constant pin would have performed termwise.  Hence
`∫ devAvg² = O(1/K)` again, and `classEquidistribution_of_variance` finishes.
-/

namespace NormalNumbers

open MeasureTheory Filter VandeheyAut VandeheyState VandeheyMix VandeheyTwo

namespace VandeheyPar

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## The product automaton -/

/-- The automaton `δ` with a parity counter attached. -/
def prodStep (δ : S → ℕ → S) : S × ZMod 2 → ℕ → S × ZMod 2 := fun s a => (δ s.1 a, s.2 + 1)

lemma runState_prodStep (δ : S → ℕ → S) (s : S × ZMod 2) (w : List ℕ) :
    runState (prodStep δ) s w = (runState δ s.1 w, s.2 + (w.length : ZMod 2)) := by
  induction w generalizing s with
  | nil => simp
  | cons a w ih =>
      rw [runState_cons, runState_cons, ih, Prod.mk.injEq]
      refine ⟨rfl, ?_⟩
      simp only [prodStep, List.length_cons, Nat.cast_add, Nat.cast_one]
      push_cast
      ring

lemma stateAt_prodStep (δ : S → ℕ → S) (s : S × ZMod 2) (x : ℝ) (i : ℕ) :
    stateAt (prodStep δ) s x i = (stateAt δ s.1 x i, s.2 + (i : ZMod 2)) := by
  rw [stateAt, stateAt, runState_prodStep, cfWord_length]

/-- The parity selector: `1` when the parity counter, started at `η`, reads `p` after `k`
digits. -/
def sel (η p : ZMod 2) (k : ℕ) : ℝ := if η + (k : ZMod 2) = p then 1 else 0

/-- The `±1` version of the selector. -/
def selSign (η p : ZMod 2) (k : ℕ) : ℝ := if η + (k : ZMod 2) = p then 1 else -1

lemma sel_eq (η p : ZMod 2) (k : ℕ) : sel η p k = (1 + selSign η p k) / 2 := by
  rw [sel, selSign]; split <;> norm_num

lemma sel_nonneg (η p : ZMod 2) (k : ℕ) : 0 ≤ sel η p k := by rw [sel]; split <;> norm_num

lemma sel_le_one (η p : ZMod 2) (k : ℕ) : sel η p k ≤ 1 := by rw [sel]; split <;> norm_num

lemma abs_sel_le_one (η p : ZMod 2) (k : ℕ) : |sel η p k| ≤ 1 := by
  rw [abs_of_nonneg (sel_nonneg η p k)]; exact sel_le_one η p k

lemma abs_selSign (η p : ZMod 2) (k : ℕ) : |selSign η p k| = 1 := by
  rw [selSign]; split <;> norm_num

/-- One digit flips the parity. -/
lemma selSign_succ (η p : ZMod 2) (k : ℕ) :
    selSign η p (k + 1) = - selSign η p k := by
  have key : ∀ a b : ZMod 2, (a + 1 = b) ↔ ¬ (a = b) := by decide
  have h : ((k + 1 : ℕ) : ZMod 2) = (k : ZMod 2) + 1 := by push_cast; ring
  rw [selSign, selSign, h, ← add_assoc]
  by_cases hk : η + (k : ZMod 2) = p
  · rw [if_neg (fun hc => ((key _ p).mp hc) hk), if_pos hk]
  · rw [if_pos ((key _ p).mpr hk), if_neg hk]; ring

/-- The selector's sign is a pure alternation. -/
lemma selSign_eq_mul_pow (η p : ZMod 2) (k : ℕ) :
    selSign η p k = selSign η p 0 * (-1 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [selSign_succ, ih, pow_succ]; ring

/-- **The alternating cancellation.**  The sign sums to `O(1)` over any contiguous range — this is
the one property that replaces the pin's termwise decay. -/
lemma abs_sum_selSign_le (η p : ZMod 2) (a b : ℕ) :
    |∑ i ∈ Finset.Ico a b, selSign η p i| ≤ 1 := by
  have hgeom : ∀ n : ℕ, |∑ i ∈ Finset.range n, (-1 : ℝ) ^ i| ≤ 1 := by
    intro n
    rw [neg_one_geom_sum]
    split <;> norm_num
  have hrw : ∑ i ∈ Finset.Ico a b, selSign η p i
      = selSign η p 0 * ∑ i ∈ Finset.Ico a b, (-1 : ℝ) ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => selSign_eq_mul_pow η p i
  rw [hrw, abs_mul, abs_selSign, one_mul]
  rcases le_or_gt a b with hab | hab
  · have hsub : ∑ i ∈ Finset.Ico a b, (-1 : ℝ) ^ i
        = (∑ i ∈ Finset.range b, (-1 : ℝ) ^ i) - ∑ i ∈ Finset.range a, (-1 : ℝ) ^ i := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun i => (-1 : ℝ) ^ i) (Nat.zero_le a) hab]
      ring
    rw [hsub]
    rw [neg_one_geom_sum, neg_one_geom_sum]
    split <;> split <;> norm_num
  · rw [Finset.Ico_eq_empty (by omega)]
    simp

/-! ## The events, and `devFun` for the product -/

/-- **The product automaton's joint event is the original one, parity-gated.** -/
lemma jointEvent_prodStep (δ : S → ℕ → S) (d t : S) (η p : ZMod 2) (q : List ℕ) (k : ℕ) :
    jointEvent (prodStep δ) (d, η) (t, p) q k
      = if η + (k : ZMod 2) = p then jointEvent δ d t q k else ∅ := by
  have hst : ∀ y : ℝ, runState (prodStep δ) (d, η) (cfWord y k)
      = (runState δ d (cfWord y k), η + (k : ZMod 2)) := by
    intro y
    rw [runState_prodStep, cfWord_length]
  by_cases hη : η + (k : ZMod 2) = p
  · rw [if_pos hη]
    rw [jointEvent, jointEvent, stateHorizonSet, stateHorizonSet]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, hst, Prod.mk.injEq, hη, and_true]
  · rw [if_neg hη, jointEvent, stateHorizonSet]
    refine Set.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
    have h2 : runState (prodStep δ) (d, η) (cfWord y k) = (t, p) := hy.2
    rw [hst y, Prod.mk.injEq] at h2
    exact hη h2.2

/-- **`devFun` for the product automaton**, written in the original automaton's events. -/
lemma devFun_prodStep (δ : S → ℕ → S) (d t : S) (η p : ZMod 2) (q : List ℕ) (L : ℝ) (k : ℕ)
    (y : ℝ) :
    devFun (prodStep δ) (d, η) (t, p) q L k y
      = sel η p k * (jointEvent δ d t q k).indicator (fun _ => (1 : ℝ)) y
        - L * (winEvent q k).indicator (fun _ => (1 : ℝ)) y := by
  rw [devFun, jointEvent_prodStep, sel]
  by_cases hη : η + (k : ZMod 2) = p
  · rw [if_pos hη, if_pos hη, one_mul]
  · rw [if_neg hη, if_neg hη, zero_mul, Set.indicator_empty]

/-! ## The two-point integral -/

private lemma integrable_ind' {E : Set ℝ} (hE : MeasurableSet E) :
    Integrable (E.indicator (fun _ => (1 : ℝ))) gaussMeasure :=
  (integrable_const (1 : ℝ)).indicator hE

/-- The product of two indicator combinations integrates to the four pair masses. -/
lemma integral_ind_comb_mul {A B A' B' : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA' : MeasurableSet A') (hB' : MeasurableSet B') (a b a' b' : ℝ) :
    ∫ y, (a * A.indicator (fun _ => (1 : ℝ)) y + b * B.indicator (fun _ => (1 : ℝ)) y)
        * (a' * A'.indicator (fun _ => (1 : ℝ)) y + b' * B'.indicator (fun _ => (1 : ℝ)) y)
        ∂gaussMeasure
      = a * a' * (gaussMeasure (A ∩ A')).toReal + a * b' * (gaussMeasure (A ∩ B')).toReal
        + b * a' * (gaussMeasure (B ∩ A')).toReal + b * b' * (gaussMeasure (B ∩ B')).toReal := by
  classical
  set f1 : ℝ → ℝ := (A ∩ A').indicator (fun _ => (1 : ℝ)) with hf1
  set f2 : ℝ → ℝ := (A ∩ B').indicator (fun _ => (1 : ℝ)) with hf2
  set f3 : ℝ → ℝ := (B ∩ A').indicator (fun _ => (1 : ℝ)) with hf3
  set f4 : ℝ → ℝ := (B ∩ B').indicator (fun _ => (1 : ℝ)) with hf4
  have i1 : Integrable f1 gaussMeasure := integrable_ind' (hA.inter hA')
  have i2 : Integrable f2 gaussMeasure := integrable_ind' (hA.inter hB')
  have i3 : Integrable f3 gaussMeasure := integrable_ind' (hB.inter hA')
  have i4 : Integrable f4 gaussMeasure := integrable_ind' (hB.inter hB')
  have hpt : ∀ y : ℝ,
      (a * A.indicator (fun _ => (1 : ℝ)) y + b * B.indicator (fun _ => (1 : ℝ)) y)
        * (a' * A'.indicator (fun _ => (1 : ℝ)) y + b' * B'.indicator (fun _ => (1 : ℝ)) y)
      = a * a' * f1 y + a * b' * f2 y + b * a' * f3 y + b * b' * f4 y := by
    intro y
    simp only [hf1, hf2, hf3, hf4, ← ind_mul_ind]
    ring
  have hmass : ∀ (E : Set ℝ), MeasurableSet E →
      ∫ y, E.indicator (fun _ => (1 : ℝ)) y ∂gaussMeasure = (gaussMeasure E).toReal := by
    intro E hE
    rw [integral_indicator_const (1 : ℝ) hE, measureReal_def, smul_eq_mul, mul_one]
  calc ∫ y, (a * A.indicator (fun _ => (1 : ℝ)) y + b * B.indicator (fun _ => (1 : ℝ)) y)
        * (a' * A'.indicator (fun _ => (1 : ℝ)) y + b' * B'.indicator (fun _ => (1 : ℝ)) y)
        ∂gaussMeasure
      = ∫ y, (a * a' * f1 y + a * b' * f2 y + b * a' * f3 y + b * b' * f4 y) ∂gaussMeasure := by
        simp only [hpt]
    _ = a * a' * (gaussMeasure (A ∩ A')).toReal + a * b' * (gaussMeasure (A ∩ B')).toReal
        + b * a' * (gaussMeasure (B ∩ A')).toReal
        + b * b' * (gaussMeasure (B ∩ B')).toReal := by
        rw [integral_add (μ := gaussMeasure)
            (f := fun y => a * a' * f1 y + a * b' * f2 y + b * a' * f3 y)
            (g := fun y => b * b' * f4 y)
            (((i1.const_mul _).add (i2.const_mul _)).add (i3.const_mul _))
            (i4.const_mul _),
          integral_add (μ := gaussMeasure)
            (f := fun y => a * a' * f1 y + a * b' * f2 y) (g := fun y => b * a' * f3 y)
            ((i1.const_mul _).add (i2.const_mul _)) (i3.const_mul _),
          integral_add (μ := gaussMeasure)
            (f := fun y => a * a' * f1 y) (g := fun y => a * b' * f2 y)
            (i1.const_mul _) (i2.const_mul _),
          integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
          hf1, hf2, hf3, hf4,
          hmass _ (hA.inter hA'), hmass _ (hA.inter hB'), hmass _ (hB.inter hA'),
          hmass _ (hB.inter hB')]

/-- The two-point integral for the product automaton: the same four masses as the aperiodic
case, with the parity selector as coefficients. -/
lemma integral_devFun_prodStep_mul (δ : S → ℕ → S) (d t : S) (η p : ZMod 2) (q : List ℕ)
    (L : ℝ) (k k' : ℕ) :
    ∫ y, devFun (prodStep δ) (d, η) (t, p) q L k y
        * devFun (prodStep δ) (d, η) (t, p) q L k' y ∂gaussMeasure
      = sel η p k * sel η p k'
          * (gaussMeasure (jointEvent δ d t q k ∩ jointEvent δ d t q k')).toReal
        - sel η p k * L * (gaussMeasure (jointEvent δ d t q k ∩ winEvent q k')).toReal
        - L * sel η p k' * (gaussMeasure (winEvent q k ∩ jointEvent δ d t q k')).toReal
        + L ^ 2 * (gaussMeasure (winEvent q k ∩ winEvent q k')).toReal := by
  have h := integral_ind_comb_mul (measurableSet_jointEvent δ d t q k)
    (measurableSet_winEvent q k) (measurableSet_jointEvent δ d t q k')
    (measurableSet_winEvent q k') (sel η p k) (-L) (sel η p k') (-L)
  have hcongr : ∀ y : ℝ, devFun (prodStep δ) (d, η) (t, p) q L k y
      * devFun (prodStep δ) (d, η) (t, p) q L k' y
      = (sel η p k * (jointEvent δ d t q k).indicator (fun _ => (1 : ℝ)) y
          + (-L) * (winEvent q k).indicator (fun _ => (1 : ℝ)) y)
        * (sel η p k' * (jointEvent δ d t q k').indicator (fun _ => (1 : ℝ)) y
          + (-L) * (winEvent q k').indicator (fun _ => (1 : ℝ)) y) := by
    intro y
    rw [devFun_prodStep, devFun_prodStep]
    ring
  simp only [hcongr]
  rw [h]
  ring

/-! ## The alternating two-point bound -/

section Pin

variable (δ : S → ℕ → S) (d t : S) (η p : ZMod 2) (q : List ℕ)

/-- The `γ`-mass of the length-`(k+|q|)` joint past. -/
noncomputable def pjMass (k : ℕ) : ℝ :=
  (gaussMeasure (familySetC (pastJoint δ d t q k))).toReal

/-- The `γ`-mass of the length-`(k+|q|)` window past. -/
noncomputable def pwMass (k : ℕ) : ℝ := (gaussMeasure (familySetC (pastWin q k))).toReal

private lemma mass_le_one (X : Set ℝ) : (gaussMeasure X).toReal ≤ 1 := by
  have h : gaussMeasure X ≤ 1 := prob_le_one
  have := ENNReal.toReal_mono (by norm_num : (1 : ENNReal) ≠ ⊤) h
  simpa using this

lemma pjMass_nonneg (k : ℕ) : 0 ≤ pjMass δ d t q k := ENNReal.toReal_nonneg
lemma pjMass_le_one (k : ℕ) : pjMass δ d t q k ≤ 1 := mass_le_one _
lemma pwMass_nonneg (k : ℕ) : 0 ≤ pwMass q k := ENNReal.toReal_nonneg
lemma pwMass_le_one (k : ℕ) : pwMass q k ≤ 1 := mass_le_one _

/-- **The alternating residue.**  What survives the exact cancellation in the product
automaton's two-point integral: a function of the *smaller* index alone, carried by a `±1`
alternation in the larger one. -/
noncomputable def altResidue (c : ℝ) (k : ℕ) : ℝ :=
  c / 2 * (gaussMeasure (cfCylinder q)).toReal
    * (pjMass δ d t q k * sel η p k - c / 2 * pwMass q k)

lemma abs_altResidue_le_one {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (k : ℕ) :
    |altResidue δ d t η p q c k| ≤ 1 := by
  have hγ0 : (0 : ℝ) ≤ (gaussMeasure (cfCylinder q)).toReal := ENNReal.toReal_nonneg
  have hγ1 : (gaussMeasure (cfCylinder q)).toReal ≤ 1 := mass_le_one _
  have h1 := pjMass_nonneg δ d t q k
  have h2 := pjMass_le_one δ d t q k
  have h3 := pwMass_nonneg q k
  have h4 := pwMass_le_one q k
  have h5 := sel_nonneg η p k
  have h6 := sel_le_one η p k
  have hx : |pjMass δ d t q k * sel η p k - c / 2 * pwMass q k| ≤ 1 := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg h1 h5, mul_le_one₀ h2 h5 h6]
  have hcγ : |c / 2 * (gaussMeasure (cfCylinder q)).toReal| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  rw [altResidue, abs_mul]
  calc |c / 2 * (gaussMeasure (cfCylinder q)).toReal|
        * |pjMass δ d t q k * sel η p k - c / 2 * pwMass q k| ≤ 1 * 1 :=
        mul_le_mul hcγ hx (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- **The alternating two-point bound.**  With the reference constant `c/2`, the constant part of
the product automaton's two-point integral cancels EXACTLY and the residue is
`selSign(k') · altResidue(k)` — a `±1` alternation times a function of `k` alone. -/
theorem abs_integral_devFun_prodStep_mul_sub_le {c C θ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 ≤ θ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hpin : ∀ (n : ℕ) (e : S) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      |stateHorizonIntegral δ (cfCylinder q) n e t τ
          - c * (gaussMeasure (cfCylinder q)).toReal|
        ≤ C * θ ^ n * (gaussMeasure (cfCylinder q)).toReal)
    (k n : ℕ) :
    |∫ y, devFun (prodStep δ) (d, η) (t, p) q (c / 2) k y
          * devFun (prodStep δ) (d, η) (t, p) q (c / 2) (k + q.length + n) y ∂gaussMeasure
        - selSign η p (k + q.length + n) * altResidue δ d t η p q c k|
      ≤ 2 * (C + 1) * max θ (79 / 100) ^ n := by
  classical
  set k' : ℕ := k + q.length + n with hk'
  set γq : ℝ := (gaussMeasure (cfCylinder q)).toReal with hγq
  set ρ : ℝ := max θ (79 / 100) with hρdef
  have hγ0 : (0 : ℝ) ≤ γq := ENNReal.toReal_nonneg
  have hγ1 : γq ≤ 1 := mass_le_one _
  have hρ0 : 0 ≤ ρ := le_trans hθ0 (le_max_left _ _)
  have hθρ : θ ^ n ≤ ρ ^ n := pow_le_pow_left₀ hθ0 (le_max_left _ _) n
  have h79ρ : (79 / 100 : ℝ) ^ n ≤ ρ ^ n := pow_le_pow_left₀ (by norm_num) (le_max_right _ _) n
  have hρn0 : (0 : ℝ) ≤ ρ ^ n := pow_nonneg hρ0 n
  set PJ : ℝ := pjMass δ d t q k with hPJ
  set PW : ℝ := pwMass q k with hPW
  have hPJ0 : 0 ≤ PJ := pjMass_nonneg δ d t q k
  have hPJ1 : PJ ≤ 1 := pjMass_le_one δ d t q k
  have hPW0 : 0 ≤ PW := pwMass_nonneg q k
  have hPW1 : PW ≤ 1 := pwMass_le_one q k
  set T1 : ℝ := (gaussMeasure (jointEvent δ d t q k ∩ jointEvent δ d t q k')).toReal with hT1d
  set T2 : ℝ := (gaussMeasure (jointEvent δ d t q k ∩ winEvent q k')).toReal with hT2d
  set T3 : ℝ := (gaussMeasure (winEvent q k ∩ jointEvent δ d t q k')).toReal with hT3d
  set T4 : ℝ := (gaussMeasure (winEvent q k ∩ winEvent q k')).toReal with hT4d
  -- the four estimates
  have b1 : |T1 - c * γq * PJ| ≤ C * θ ^ n * γq * PJ :=
    abs_measure_joint_inter_joint_sub_le δ d t q hpin k n
  have b2 : |T2 - γq * PJ| ≤ (79 / 100) ^ n * γq * PJ :=
    abs_measure_joint_inter_win_sub_le δ d t q k n
  have b3 : |T3 - c * γq * PW| ≤ C * θ ^ n * γq * PW :=
    abs_measure_win_inter_joint_sub_le δ d t q hpin k n
  have b4 : |T4 - γq * PW| ≤ (79 / 100) ^ n * γq * PW :=
    abs_measure_win_inter_win_sub_le q k n
  -- collapse the majorants
  have hθn0 : (0 : ℝ) ≤ θ ^ n := pow_nonneg hθ0 n
  have hcθ0 : (0 : ℝ) ≤ C * θ ^ n := mul_nonneg hC hθn0
  have hcθρ : C * θ ^ n ≤ C * ρ ^ n := mul_le_mul_of_nonneg_left hθρ hC
  have c1 : |T1 - c * γq * PJ| ≤ C * ρ ^ n := by
    refine le_trans b1 ?_
    have hgp : γq * PJ ≤ 1 := by nlinarith
    calc C * θ ^ n * γq * PJ = (C * θ ^ n) * (γq * PJ) := by ring
      _ ≤ (C * θ ^ n) * 1 := mul_le_mul_of_nonneg_left hgp hcθ0
      _ ≤ C * ρ ^ n := by linarith
  have c3 : |T3 - c * γq * PW| ≤ C * ρ ^ n := by
    refine le_trans b3 ?_
    have hgp : γq * PW ≤ 1 := by nlinarith
    calc C * θ ^ n * γq * PW = (C * θ ^ n) * (γq * PW) := by ring
      _ ≤ (C * θ ^ n) * 1 := mul_le_mul_of_nonneg_left hgp hcθ0
      _ ≤ C * ρ ^ n := by linarith
  have h79n0 : (0 : ℝ) ≤ (79 / 100 : ℝ) ^ n := pow_nonneg (by norm_num) n
  have c2 : |T2 - γq * PJ| ≤ ρ ^ n := by
    refine le_trans b2 ?_
    have hgp : γq * PJ ≤ 1 := by nlinarith
    calc (79 / 100 : ℝ) ^ n * γq * PJ = (79 / 100 : ℝ) ^ n * (γq * PJ) := by ring
      _ ≤ (79 / 100 : ℝ) ^ n * 1 := mul_le_mul_of_nonneg_left hgp h79n0
      _ ≤ ρ ^ n := by linarith
  have c4 : |T4 - γq * PW| ≤ ρ ^ n := by
    refine le_trans b4 ?_
    have hgp : γq * PW ≤ 1 := by nlinarith
    calc (79 / 100 : ℝ) ^ n * γq * PW = (79 / 100 : ℝ) ^ n * (γq * PW) := by ring
      _ ≤ (79 / 100 : ℝ) ^ n * 1 := mul_le_mul_of_nonneg_left hgp h79n0
      _ ≤ ρ ^ n := by linarith
  -- the exact cancellation
  set A : ℝ := sel η p k with hA
  set u : ℝ := selSign η p k' with hu
  have hA0 : 0 ≤ A := sel_nonneg η p k
  have hA1 : A ≤ 1 := sel_le_one η p k
  have hu1 : |u| = 1 := abs_selSign η p k'
  have hAu : sel η p k' = (1 + u) / 2 := sel_eq η p k'
  have hkey : (∫ y, devFun (prodStep δ) (d, η) (t, p) q (c / 2) k y
        * devFun (prodStep δ) (d, η) (t, p) q (c / 2) k' y ∂gaussMeasure)
      - u * altResidue δ d t η p q c k
      = A * ((1 + u) / 2) * (T1 - c * γq * PJ) - A * (c / 2) * (T2 - γq * PJ)
        - c / 2 * ((1 + u) / 2) * (T3 - c * γq * PW) + (c / 2) ^ 2 * (T4 - γq * PW) := by
    rw [integral_devFun_prodStep_mul, altResidue, ← hT1d, ← hT2d, ← hT3d, ← hT4d, ← hA, ← hPJ,
      ← hPW, ← hγq, hAu]
    ring
  rw [hkey]
  have hAu1 : |(1 + u) / 2| ≤ 1 := by
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hu1 with h | h <;> rw [h] <;> norm_num
  have e1 : |A * ((1 + u) / 2) * (T1 - c * γq * PJ)| ≤ C * ρ ^ n := by
    rw [abs_mul, abs_mul]
    have hle : |A| * |(1 + u) / 2| ≤ 1 := by
      rw [abs_of_nonneg hA0]
      exact mul_le_one₀ hA1 (abs_nonneg _) hAu1
    calc |A| * |(1 + u) / 2| * |T1 - c * γq * PJ|
        ≤ 1 * (C * ρ ^ n) := by
          refine mul_le_mul hle c1 (abs_nonneg _) zero_le_one
      _ = C * ρ ^ n := one_mul _
  have e3 : |c / 2 * ((1 + u) / 2) * (T3 - c * γq * PW)| ≤ C * ρ ^ n := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ c / 2)]
    have : c / 2 * |(1 + u) / 2| ≤ 1 :=
      mul_le_one₀ (by linarith) (abs_nonneg _) hAu1
    calc c / 2 * |(1 + u) / 2| * |T3 - c * γq * PW|
        ≤ 1 * (C * ρ ^ n) := by
          refine mul_le_mul this c3 (abs_nonneg _) zero_le_one
      _ = C * ρ ^ n := one_mul _
  have e2 : |A * (c / 2) * (T2 - γq * PJ)| ≤ ρ ^ n := by
    rw [abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg (by linarith : (0:ℝ) ≤ c / 2)]
    have : A * (c / 2) ≤ 1 := mul_le_one₀ hA1 (by linarith) (by linarith)
    calc A * (c / 2) * |T2 - γq * PJ| ≤ 1 * ρ ^ n := by
          refine mul_le_mul this c2 (abs_nonneg _) zero_le_one
      _ = ρ ^ n := one_mul _
  have e4 : |(c / 2) ^ 2 * (T4 - γq * PW)| ≤ ρ ^ n := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c / 2) ^ 2)]
    have : (c / 2) ^ 2 ≤ 1 := by
      rw [sq]
      exact mul_le_one₀ (by linarith) (by linarith) (by linarith)
    calc (c / 2) ^ 2 * |T4 - γq * PW| ≤ 1 * ρ ^ n := by
          refine mul_le_mul this c4 (abs_nonneg _) zero_le_one
      _ = ρ ^ n := one_mul _
  have htri : |A * ((1 + u) / 2) * (T1 - c * γq * PJ) - A * (c / 2) * (T2 - γq * PJ)
        - c / 2 * ((1 + u) / 2) * (T3 - c * γq * PW) + (c / 2) ^ 2 * (T4 - γq * PW)|
      ≤ |A * ((1 + u) / 2) * (T1 - c * γq * PJ)| + |A * (c / 2) * (T2 - γq * PJ)|
        + |c / 2 * ((1 + u) / 2) * (T3 - c * γq * PW)| + |(c / 2) ^ 2 * (T4 - γq * PW)| := by
    have f1 := abs_add_le (A * ((1 + u) / 2) * (T1 - c * γq * PJ)
      - A * (c / 2) * (T2 - γq * PJ) - c / 2 * ((1 + u) / 2) * (T3 - c * γq * PW))
      ((c / 2) ^ 2 * (T4 - γq * PW))
    have f2 := abs_sub (A * ((1 + u) / 2) * (T1 - c * γq * PJ) - A * (c / 2) * (T2 - γq * PJ))
      (c / 2 * ((1 + u) / 2) * (T3 - c * γq * PW))
    have f3 := abs_sub (A * ((1 + u) / 2) * (T1 - c * γq * PJ)) (A * (c / 2) * (T2 - γq * PJ))
    linarith
  calc |A * ((1 + u) / 2) * (T1 - c * γq * PJ) - A * (c / 2) * (T2 - γq * PJ)
        - c / 2 * ((1 + u) / 2) * (T3 - c * γq * PW) + (c / 2) ^ 2 * (T4 - γq * PW)|
      ≤ C * ρ ^ n + ρ ^ n + C * ρ ^ n + ρ ^ n := by linarith
    _ ≤ 2 * (C + 1) * ρ ^ n := by linarith

end Pin

end VandeheyPar

end NormalNumbers
