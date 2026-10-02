/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-FR: a predictor with FINITE range cannot beat the Gauss measure

Directive fact (α) says a *predictable* family — one determined by the past — can be hit at every
single time (`exists_predictor_all_hit`), so no argument using only predictability and bounded
distortion can bound the crux.  It leaves exactly one soft escape: **finiteness of the predictor's
range**.  This module proves that the escape works.

* `maxDen`, `abs_mob_sub_ge` — the expansion bound `|mob z − mob z'| ≥ (|det|/maxDen²)·|z − z'|`,
  from the identity `mob z − mob z' = det·(z−z')/((cz+d)(cz'+d))`.
* `preimage_diam_le` — hence the pullback of an interval of length `ℓ` has diameter
  `≤ ℓ·maxDen²/|det|`, with no monotonicity argument and no interval structure needed.
* `varCount` — the hit count of a *varying* family along the orbit.
* `varCount_le_sum` — the union bound: a family drawn from a finite set `T` of states is dominated
  by the sum over `T` of the fixed pullbacks.
* **`varCount_finiteRange_le`** — the theorem: for a CF-normal `x`, any `σ : ℕ → MapState` with
  values in a finite `T`, and any interval target `(a,b)`,

      freq{n : Gⁿx ∈ (σ n)⁻¹(a,b)}  ≤  |T| · 4D(b−a)/log 2 + |T|·2δ ,

  where `D` bounds `maxDen²/|det|` over `T`.  `σ` is completely arbitrary — in particular it may
  depend on the whole past, which is exactly what fact (α) forbids arguing about.

## What this settles, and what it does not

It settles that **finiteness beats predictability**, with the honest constant `|T|`.  It does NOT
close the crux, and the reason is quantitative, worth recording: fact (δ) only gives the true
states a `ρ`-NET, so `(σ n)⁻¹(a,b)` has to be replaced by a `δ`-thickening with `δ ≍ ρ`, and the
net size grows like `ρ^{-3}`.  The resulting bound `|T|·(b−a) + |T|·δ` has an additive term
`≍ ρ^{-3}·ρ = ρ^{-2}`, which cannot be balanced against `(b−a) = γ(I_w) → 0`.  So the union bound
is *tight* (a predictor CAN spread its hits over all `|T|` sets) but too lossy for a net, and the
crux genuinely needs the JOINT statement — state-cell against orbit point — not this one.
-/
import NormalNumbers.VandeheyS7Near
import NormalNumbers.VandeheyS7IooFreq

namespace NormalNumbers.VandeheyS7

open Set Filter MeasureTheory NormalNumbers

namespace MapState

/-! ## The expansion bound -/

/-- The larger of the two denominators. -/
noncomputable def maxDen (s : MapState) : ℝ := max s.d (s.c + s.d)

lemma maxDen_pos (s : MapState) : 0 < s.maxDen := lt_of_lt_of_le s.hd (le_max_left _ _)

lemma den_le_maxDen (s : MapState) {z : ℝ} (hz : z ∈ Icc (0:ℝ) 1) : s.c * z + s.d ≤ s.maxDen := by
  have h : s.c * z + s.d = (1 - z) * s.d + z * (s.c + s.d) := by ring
  have h1 : s.d ≤ s.maxDen := le_max_left _ _
  have h2 : s.c + s.d ≤ s.maxDen := le_max_right _ _
  rw [h]
  nlinarith [hz.1, hz.2]

/-- **The expansion bound.**  `mob` expands by at least `|det| / maxDen²` on `[0,1]`. -/
theorem abs_mob_sub_ge (s : MapState) {z z' : ℝ} (hz : z ∈ Icc (0:ℝ) 1) (hz' : z' ∈ Icc (0:ℝ) 1) :
    |s.det| / s.maxDen ^ 2 * |z - z'| ≤ |s.mob z - s.mob z'| := by
  have hd1 := s.den_pos hz
  have hd2 := s.den_pos hz'
  have hm := s.maxDen_pos
  have key : s.mob z - s.mob z' = s.det * (z - z') / ((s.c * z + s.d) * (s.c * z' + s.d)) := by
    rw [mob, mob, div_sub_div _ _ hd1.ne' hd2.ne', det]
    congr 1
    ring
  have hprod : (s.c * z + s.d) * (s.c * z' + s.d) ≤ s.maxDen ^ 2 := by
    have h1 := s.den_le_maxDen hz
    have h2 := s.den_le_maxDen hz'
    nlinarith [hd1, hd2, hm]
  rw [key, abs_div, abs_mul, abs_of_pos (mul_pos hd1 hd2)]
  have hnn : 0 ≤ |s.det| * |z - z'| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc |s.det| / s.maxDen ^ 2 * |z - z'| = |s.det| * |z - z'| / s.maxDen ^ 2 := by ring
    _ ≤ |s.det| * |z - z'| / ((s.c * z + s.d) * (s.c * z' + s.d)) :=
        div_le_div_of_nonneg_left hnn (mul_pos hd1 hd2) hprod

/-- The pullback of an interval of length `b − a` has diameter at most `(b−a)·maxDen²/|det|`. -/
theorem preimage_diam_le (s : MapState) {a b z z' : ℝ}
    (hz : z ∈ Icc (0:ℝ) 1) (hz' : z' ∈ Icc (0:ℝ) 1)
    (h : s.mob z ∈ Ioo a b) (h' : s.mob z' ∈ Ioo a b) :
    |z - z'| ≤ (b - a) * (s.maxDen ^ 2 / |s.det|) := by
  have hdet : 0 < |s.det| := abs_pos.mpr s.hdet
  have hm := s.maxDen_pos
  have hge := s.abs_mob_sub_ge hz hz'
  have hlt : |s.mob z - s.mob z'| ≤ b - a := by
    rw [abs_le]
    constructor <;> [linarith [h.1, h.2, h'.1, h'.2]; linarith [h.1, h.2, h'.1, h'.2]]
  have hchain : |s.det| / s.maxDen ^ 2 * |z - z'| ≤ b - a := le_trans hge hlt
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hchain
  have hgoal : (b - a) * (s.maxDen ^ 2 / |s.det|) = ((b - a) * s.maxDen ^ 2) / |s.det| := by ring
  rw [hgoal, le_div_iff₀ hdet]
  linarith [hchain]

/-! ## Counting a varying family -/

/-- The hit count of a **varying** family of targets along the orbit. -/
noncomputable def varCount (S : ℕ → Set ℝ) (p : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range p, blockIndic (S n) (gaussMap^[n] x)

lemma blockCount_mono {A B : Set ℝ} (hAB : A ⊆ B) (p : ℕ) (x : ℝ) :
    blockCount A p x ≤ blockCount B p x := by
  rw [blockCount_apply, blockCount_apply]
  refine Finset.sum_le_sum ?_
  intro k _
  by_cases h : gaussMap^[k] x ∈ A
  · rw [blockIndic, Set.indicator_of_mem h, blockIndic, Set.indicator_of_mem (hAB h)]
  · rw [blockIndic, Set.indicator_of_notMem h]
    exact Set.indicator_nonneg (by intro _ _; norm_num) _

/-- **The union bound.**  A family drawn from a finite set of states is dominated by the sum, over
that set, of the fixed targets. -/
theorem varCount_le_sum {T : Finset MapState} {σ : ℕ → MapState} (hσ : ∀ n, σ n ∈ T)
    {S : ℕ → Set ℝ} {A : MapState → Set ℝ} (hS : ∀ n, S n ⊆ A (σ n)) (p : ℕ) (x : ℝ) :
    varCount S p x ≤ ∑ t ∈ T, blockCount (A t) p x := by
  classical
  rw [varCount]
  have hswap : ∑ t ∈ T, blockCount (A t) p x
      = ∑ n ∈ Finset.range p, ∑ t ∈ T, blockIndic (A t) (gaussMap^[n] x) := by
    simp only [blockCount_apply]
    exact Finset.sum_comm
  rw [hswap]
  refine Finset.sum_le_sum ?_
  intro n _
  by_cases h : gaussMap^[n] x ∈ S n
  · rw [blockIndic, Set.indicator_of_mem h]
    have hmem : gaussMap^[n] x ∈ A (σ n) := hS n h
    have hterm : blockIndic (A (σ n)) (gaussMap^[n] x) = 1 := by
      rw [blockIndic, Set.indicator_of_mem hmem]; rfl
    calc (1 : ℝ) = blockIndic (A (σ n)) (gaussMap^[n] x) := hterm.symm
      _ ≤ ∑ t ∈ T, blockIndic (A t) (gaussMap^[n] x) := by
          refine Finset.single_le_sum (f := fun t => blockIndic (A t) (gaussMap^[n] x)) ?_ (hσ n)
          intro t _
          exact Set.indicator_nonneg (by intro _ _; norm_num) _
  · rw [blockIndic, Set.indicator_of_notMem h]
    exact Finset.sum_nonneg fun t _ => Set.indicator_nonneg (by intro _ _; norm_num) _

/-! ## The theorem -/

open Classical in
/-- **S7-FR.**  A predictor with FINITE range cannot beat the Gauss measure by more than the size
of its range.  `σ` is arbitrary — it may read the entire past. -/
theorem varCount_finiteRange_le {x : ℝ} (hirr : Irrational x) (hmem : x ∈ Ioo (0:ℝ) 1)
    (hx : IsCFNormal x) {T : Finset MapState} {σ : ℕ → MapState} (hσ : ∀ n, σ n ∈ T)
    {a b D : ℝ} (hab : a < b) (hD : 0 < D) (hTD : ∀ t ∈ T, t.maxDen ^ 2 / |t.det| ≤ D)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ p : ℕ in atTop,
      varCount (fun n => (σ n).mob ⁻¹' Ioo a b ∩ Icc (0:ℝ) 1) p x / (p : ℝ)
        ≤ (T.card : ℝ) * (4 * (D * (b - a)) / Real.log 2 + 2 * δ) := by
  classical
  set L : ℝ := D * (b - a) with hL
  have hLpos : 0 < L := by rw [hL]; positivity
  -- for each state, a fixed interval containing its pullback
  set A : MapState → Set ℝ := fun t => t.mob ⁻¹' Ioo a b ∩ Icc (0:ℝ) 1 with hA
  set ctr : MapState → ℝ := fun t => if h : (A t).Nonempty then h.choose else 0 with hctr
  set Itv : MapState → Set ℝ := fun t => Ioo (ctr t - 2 * L) (ctr t + 2 * L) with hItv
  have hsub : ∀ t ∈ T, A t ⊆ Itv t := by
    intro t ht z hz
    have hne : (A t).Nonempty := ⟨z, hz⟩
    have hc : ctr t = hne.choose := by rw [hctr]; simp [dif_pos hne]
    have hcmem : ctr t ∈ A t := by rw [hc]; exact hne.choose_spec
    have hdiam : |z - ctr t| ≤ (b - a) * (t.maxDen ^ 2 / |t.det|) :=
      t.preimage_diam_le hz.2 hcmem.2 hz.1 hcmem.1
    have hDb : (b - a) * (t.maxDen ^ 2 / |t.det|) ≤ L := by
      rw [hL, mul_comm D (b - a)]
      exact mul_le_mul_of_nonneg_left (hTD t ht) (by linarith)
    have : |z - ctr t| ≤ L := le_trans hdiam hDb
    rw [abs_le] at this
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  -- each fixed interval has the right frequency
  have hfreq : ∀ t ∈ T, ∀ᶠ p : ℕ in atTop,
      blockCount (Itv t) p x / (p : ℝ) ≤ 4 * L / Real.log 2 + 2 * δ := by
    intro t _
    have h := blockCount_Ioo_le' hirr hmem hx
      (show ctr t - 2 * L ≤ ctr t + 2 * L by linarith) hδ
    filter_upwards [h] with p hp
    have hlen : (ctr t + 2 * L) - (ctr t - 2 * L) = 4 * L := by ring
    rwa [hlen] at hp
  have hall : ∀ᶠ p : ℕ in atTop, ∀ t ∈ T,
      blockCount (Itv t) p x / (p : ℝ) ≤ 4 * L / Real.log 2 + 2 * δ :=
    (Filter.eventually_all_finset T).2 hfreq
  filter_upwards [hall, eventually_gt_atTop 0] with p hp hp0
  have hpR : (0:ℝ) < p := by exact_mod_cast hp0
  have hstep : varCount (fun n => (σ n).mob ⁻¹' Ioo a b ∩ Icc (0:ℝ) 1) p x
      ≤ ∑ t ∈ T, blockCount (Itv t) p x := by
    refine varCount_le_sum hσ (A := Itv) (fun n => ?_) p x
    exact fun z hz => hsub (σ n) (hσ n) hz
  rw [div_le_iff₀ hpR]
  have hsum : ∑ t ∈ T, blockCount (Itv t) p x
      ≤ ∑ _t ∈ T, (4 * L / Real.log 2 + 2 * δ) * p := by
    refine Finset.sum_le_sum ?_
    intro t ht
    have := hp t ht
    rw [div_le_iff₀ hpR] at this
    exact this
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  calc varCount (fun n => (σ n).mob ⁻¹' Ioo a b ∩ Icc (0:ℝ) 1) p x
      ≤ ∑ t ∈ T, blockCount (Itv t) p x := hstep
    _ ≤ (T.card : ℝ) * ((4 * L / Real.log 2 + 2 * δ) * p) := hsum
    _ = (T.card : ℝ) * (4 * L / Real.log 2 + 2 * δ) * p := by ring

end MapState

section Audit

#print axioms MapState.abs_mob_sub_ge
#print axioms MapState.preimage_diam_le
#print axioms MapState.varCount_le_sum
#print axioms MapState.varCount_finiteRange_le

end Audit

end NormalNumbers.VandeheyS7
