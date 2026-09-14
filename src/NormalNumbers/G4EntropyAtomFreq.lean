/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyWindows
import NormalNumbers.G4EntropyPosition

/-!
# Entropy expedition — one atom already carries every word at its correct frequency

`tendsto_occursCountP_primeLambertFour` averages over **all** triples `(n, α, p)`.  This module
renders `G4EntropyGoodAtoms.coordAvg` at the schedule and shows the average over `α` is not
needed: at each scale there is a *single* atom whose own windows already carry every binary word
at its correct density, to within `2√(log 2·ℓ·100√K/(m_K−ℓ+1))`.

The atom is chosen by `exists_good_coord`, which is `ℓ`- and word-free — so **one** atom works
for every word of every length at that scale.  Combined with `window_gap_same_atom` (the windows
at a fixed atom are pairwise disjoint), this is a window family that is simultaneously

* certified — its own statistics obey the capture bound, with no averaging over atoms, and
* geometrically clean — its windows never overlap, so reading it in position order is literally
  the concatenation of its window contents.

That pair is what a subsequence construction consumes.  It does **not** give normality: by
`certified_granule_exceeds_previous_scale`, the prefix frequencies still cannot converge across
scales.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The count rendering of one atom's average -/

open Classical in
/-- **One atom's count rendering.**  `coordAvg` at the scale-`i` law is the density, among the
`|P_K|·(m_K−ℓ+1)` pairs `(n, p)` at the fixed atom `α`, of those whose `ℓ`-block at window
position `p` is `w`. -/
theorem coordAvg_eq_count (i ℓ : ℕ) (x : ℝ) (α : (gridAt i).Atom) (w : Fin (2 ^ ℓ)) :
    coordAvg (kk i) ℓ (jointLawAt i x) α w
      = (∑ p : Fin (kk i - ℓ + 1),
            (((PK i).filter fun n =>
              posAt (kk i) ℓ (p : ℕ) (ZVec (gridAt i) (kk i) x n α) = w).card : ℝ))
        / (((PK i).card : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ)) := by
  classical
  have hp : ∀ p : Fin (kk i - ℓ + 1),
      ((soloLaw (jointLawAt i x) α).map
          (fun z : Unit → Fin (2 ^ kk i) => posAt (kk i) ℓ (p : ℕ) (z default))).prob {w}
        = (((PK i).filter fun n =>
              posAt (kk i) ℓ (p : ℕ) (ZVec (gridAt i) (kk i) x n α) = w).card : ℝ)
          / ((PK i).card : ℝ) := by
    intro p
    rw [soloLaw, FinLaw.prob_singleton_map_map, FinLaw.prob, Finset.sum_singleton]
    exact map_empirical_p (apSample_nonempty (gridAt i) (b₀_lt_X_at i)) _ _ w
  rw [coordAvg, posAvg, Fintype.sum_prod_type]
  simp only [Fintype.card_unit, Nat.cast_one, one_mul, Finset.univ_unique,
    Finset.sum_singleton, hp]
  rw [← Finset.sum_div, div_div]

open Classical in
/-- **One atom's digit rendering.** -/
theorem coordAvg_eq_digits (i ℓ : ℕ) (hℓm : ℓ ≤ kk i) (x : ℝ) (α : (gridAt i).Atom)
    (w : Fin (2 ^ ℓ)) :
    coordAvg (kk i) ℓ (jointLawAt i x) α w
      = (∑ p : Fin (kk i - ℓ + 1),
            (((PK i).filter fun n =>
              blockVal (Int.fract x) (2 * kIdx (gridAt i) n α + (p : ℕ)) ℓ = (w : ℕ)).card : ℝ))
        / (((PK i).card : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ)) := by
  classical
  rw [coordAvg_eq_count i ℓ x α w]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  have hZ : ∀ n : ℕ, ZVec (gridAt i) (kk i) x n α
      = ⟨blockVal (Int.fract x) (2 * kIdx (gridAt i) n α) (kk i), blockVal_lt _ _ _⟩ :=
    fun n => Fin.ext (ZSample_eq_blockVal (gridAt i) (kk i) x n α)
  have hfit : (p : ℕ) + ℓ ≤ kk i := by
    have := p.isLt
    omega
  refine Finset.filter_congr fun n _ => ?_
  rw [hZ n, posAt_blockVal _ _ _ _ _ hfit]
  exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

/-! ### The good atom at scale `i` -/

/-- The scale-`i` per-window deficit at `ρ = 1/2`: `entropy_E1`'s `50√K`, doubled. -/
noncomputable def atomDeficit (i : ℕ) : ℝ := 100 * Real.sqrt (KK i)

lemma atomDeficit_pos (i : ℕ) : 0 < atomDeficit i := by
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have := Real.sqrt_pos.2 hKpos
  rw [atomDeficit]
  linarith

open Classical in
/-- **At every scale one atom carries all but `100√K` of its own `m_K` bits.**
`exists_good_coord_deficit` at `ρ = 1/2`, fed `entropy_E1`'s deficit. -/
theorem exists_good_atom (i : ℕ) :
    ∃ α : (gridAt i).Atom,
      FinLaw.coordDeficit (jointLawAt i (primeLambertAtBase 4)) α ≤ atomDeficit i := by
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hδ : (0 : ℝ) < 50 * Real.sqrt (KK i) := by
    have := Real.sqrt_pos.2 hKpos
    linarith
  obtain ⟨α, hα⟩ := exists_good_coord_deficit (jointLawAt i (primeLambertAtBase 4)) hδ
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1) (deficit_primeLambertFour i)
  refine ⟨α, ?_⟩
  have hrw : 50 * Real.sqrt (KK i) / (1 / 2 : ℝ) = atomDeficit i := by
    rw [atomDeficit]; ring
  rwa [hrw] at hα


/-! ### The good atom's frequency limit -/

open Classical in
/-- The chosen good atom at scale `i`.  Word- and length-free. -/
noncomputable def goodAtom (i : ℕ) : (gridAt i).Atom := (exists_good_atom i).choose

lemma goodAtom_deficit (i : ℕ) :
    FinLaw.coordDeficit (jointLawAt i (primeLambertAtBase 4)) (goodAtom i) ≤ atomDeficit i :=
  (exists_good_atom i).choose_spec

/-- The good atom's capture bound, for every word of every length. -/
lemma goodAtom_spec (i : ℕ) : ∀ ℓ : ℕ, 0 < ℓ → ℓ ≤ kk i → ∀ w : Fin (2 ^ ℓ),
    |coordAvg (kk i) ℓ (jointLawAt i (primeLambertAtBase 4)) (goodAtom i) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (Real.log 2 * (ℓ : ℝ) * atomDeficit i / ((kk i : ℝ) - ℓ + 1)) :=
  fun ℓ hℓ hℓm w =>
    abs_coordAvg_sub_le hℓ hℓm _ (goodAtom i) w (atomDeficit_pos i) (goodAtom_deficit i)

/-- **The good atom's capture bound in the `1/√K` form.**  `m_K − ℓ + 1 ≥ m_K/2` and
`√K·√K = 4m_K`, so the deficit `100√K` becomes `800 log 2·ℓ/√K`. -/
theorem abs_coordAvg_goodAtom_le (i ℓ : ℕ) (hℓ : 0 < ℓ) (hℓm : 2 * ℓ ≤ kk i)
    (w : Fin (2 ^ ℓ)) :
    |coordAvg (kk i) ℓ (jointLawAt i (primeLambertAtBase 4)) (goodAtom i) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (800 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS0 : 0 < Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_pos.2 hKpos
  refine (goodAtom_spec i ℓ hℓ (by omega) w).trans ?_
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hhalf : (kk i : ℝ) / 2 ≤ (kk i : ℝ) - ℓ + 1 := by
    have : (2 : ℝ) * ℓ ≤ (kk i : ℝ) := by exact_mod_cast hℓm
    linarith
  have hden : (0 : ℝ) < (kk i : ℝ) - ℓ + 1 := by
    have : (2 : ℝ) * ℓ ≤ (kk i : ℝ) := by exact_mod_cast hℓm
    linarith
  have hkk4 : (KK i : ℝ) = 4 * (kk i : ℝ) := by unfold KK; push_cast; ring
  have hsq : Real.sqrt ((KK i : ℕ) : ℝ) * Real.sqrt ((KK i : ℕ) : ℝ) = 4 * (kk i : ℝ) := by
    rw [Real.mul_self_sqrt hKpos.le, hkk4]
  have hstep : Real.log 2 * (ℓ : ℝ) * atomDeficit i / ((kk i : ℝ) - ℓ + 1)
      ≤ 800 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i) := by
    rw [atomDeficit, div_le_div_iff₀ hden hS0]
    have hkey : Real.log 2 * (ℓ : ℝ) * (100 * Real.sqrt (KK i)) * Real.sqrt ((KK i : ℕ) : ℝ)
        = 400 * Real.log 2 * (ℓ : ℝ) * (kk i : ℝ) := by
      linear_combination (100 * Real.log 2 * (ℓ : ℝ)) * hsq
    rw [hkey]
    nlinarith [mul_le_mul_of_nonneg_left hhalf
      (by positivity : (0:ℝ) ≤ 800 * Real.log 2 * (ℓ : ℝ))]
  have hpos1 : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ) * atomDeficit i / ((kk i : ℝ) - ℓ + 1) := by
    rw [atomDeficit]
    positivity
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (by norm_num)

open Classical in
/-- **The endpoint of the single-atom line.**  For every finite binary word `v`, the proportion
of pairs `(n, p)` — sample time and window position, at the *one* schedule-chosen atom
`goodAtom i` — at which `v` occurs in `G₄`'s binary digits at `2·kIdx(n, goodAtom i) + p` tends
to `2^{−|v|}`.

`tendsto_occursCountP_primeLambertFour` is the same statement averaged over **all** atoms.  The
atom here is chosen once per scale, before any word is named. -/
theorem tendsto_goodAtom_occursCount (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) :
    Tendsto (fun i =>
      (∑ p : Fin (kk i - v.length + 1),
          (((PK i).filter fun n =>
            OccursAt 2 (primeLambertAtBase 4) v
              (2 * kIdx (gridAt i) n (goodAtom i) + (p : ℕ))).card : ℝ))
        / (((PK i).card : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)))
      atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
  classical
  set w : ∀ i : ℕ, Fin (2 ^ v.length) := fun _ => ⟨wordVal v, wordVal_lt hv⟩ with hw
  -- the capture bound tends to zero
  have hgrow : Tendsto (fun i => (v.length : ℝ) / Real.sqrt (KK i)) atTop (nhds 0) := by
    have hsqrt : Tendsto (fun i => Real.sqrt (KK i)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_KK_atTop
    exact hsqrt.const_div_atTop _
  have hinner : Tendsto (fun i => 800 * Real.log 2 * (v.length : ℝ) / Real.sqrt (KK i))
      atTop (nhds 0) := by
    have h := hgrow.const_mul (800 * Real.log 2)
    simp only [mul_zero] at h
    refine h.congr fun i => ?_
    rw [mul_div_assoc]
  have hsq : Tendsto (fun i => 2 * Real.sqrt (800 * Real.log 2 * (v.length : ℝ)
      / Real.sqrt (KK i))) atTop (nhds 0) := by
    have := hinner.sqrt
    simpa using this.const_mul (2 : ℝ)
  have hzero : Tendsto (fun i =>
      coordAvg (kk i) v.length (jointLawAt i (primeLambertAtBase 4)) (goodAtom i) (w i)
        - 1 / (2 : ℝ) ^ v.length) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hsq
    filter_upwards [eventually_ge_atTop (2 * v.length)] with i hi
    have hle : 2 * v.length ≤ kk i := by unfold kk; omega
    simpa [Real.norm_eq_abs] using abs_coordAvg_goodAtom_le i v.length hlen hle (w i)
  have hmain : Tendsto (fun i =>
      coordAvg (kk i) v.length (jointLawAt i (primeLambertAtBase 4)) (goodAtom i) (w i))
      atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
    have hlim : Tendsto (fun _ : ℕ => (1 : ℝ) / (2 : ℝ) ^ v.length) atTop
        (nhds (1 / (2 : ℝ) ^ v.length)) := tendsto_const_nhds
    simpa using hzero.add hlim
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop v.length] with i hi
  have hle : v.length ≤ kk i := by unfold kk; omega
  rw [coordAvg_eq_digits i v.length hle _ (goodAtom i) (w i)]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  refine Finset.filter_congr fun n _ => ?_
  exact blockVal_eq_wordVal_iff (y := primeLambertAtBase 4) hv

end NormalNumbers.G4.Sched
