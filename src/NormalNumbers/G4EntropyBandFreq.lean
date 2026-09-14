/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBand

/-!
# Entropy expedition — the band-restricted good atom is still certified

`bandS i` keeps at least half of the good atom's sample times (`card_bandS_ge`), and a
sample-time restriction of relative size `σ` costs `(δ+1)/σ` in deficit
(`H₂_empirical_window_restrict_ge`).  With `σ ≥ 1/2` the good atom's own deficit `100√K` becomes
at most `2(100√K+1) ≤ 202√K`, still `o(m_K)` — so the band-restricted window family carries
every word at its correct frequency, and its windows are pairwise disjoint and all lie inside
scale `i`'s band.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

variable {Ω Ω' : Type*} [Fintype Ω] [Fintype Ω']

lemma FinLaw.map_id [DecidableEq Ω] (L : FinLaw Ω) : L.map id = L := by
  refine FinLaw.ext' (funext fun ω => ?_)
  rw [FinLaw.map_p]
  simp [Finset.filter_eq']

lemma FinLaw.H₂_map_injective [DecidableEq Ω] [DecidableEq Ω'] (L : FinLaw Ω) {g : Ω → Ω'}
    (hg : Function.Injective g) : (L.map g).H₂ = L.H₂ := by
  have h := L.H₂_map_congr_comp (f := id) (g := g) hg (F := g) (fun ω => rfl)
  rw [h, FinLaw.map_id]

open Classical in
/-- Pushing an empirical law forward re-samples the composite statistic. -/
lemma map_empirical {ι : Type*} [DecidableEq Ω'] {S : Finset ι} (hS : S.Nonempty)
    (f : ι → Ω) (g : Ω → Ω') :
    (empirical S hS f).map g = empirical S hS (fun i => g (f i)) := by
  classical
  refine FinLaw.ext' (funext fun ω' => ?_)
  rw [map_empirical_p, empirical_p]
  congr 1
  congr 1
  exact Finset.card_nbij id (fun a ha => by simpa using ha) (fun a _ b _ h => h)
    (fun b hb => ⟨b, by simpa using hb, rfl⟩)

end NormalNumbers.G4Entropy

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-! ### The single-coordinate law is an empirical law -/

open Classical in
/-- The scale-`i` law at one coordinate is the empirical law of that coordinate's window. -/
theorem map_coord_jointLawAt (i : ℕ) (x : ℝ) (α : (gridAt i).Atom) :
    (jointLawAt i x).map (fun z => z α)
      = empirical (PK i) (PK_nonempty i) (fun n => ZVec (gridAt i) (kk i) x n α) := by
  classical
  refine FinLaw.ext' (funext fun u => ?_)
  show ((jointLawAt i x).map (fun z => z α)).p u = _
  rw [jointLawAt, jointLaw, map_empirical_p, empirical_p]
  show ((((apSample (X (KK i)) (gridAt i).P₀ (gridAt i).b₀).filter
      fun n => ZVec (gridAt i) (kk i) x n α = u).card : ℝ)
    / ((apSample (X (KK i)) (gridAt i).P₀ (gridAt i).b₀).card : ℝ)) = _
  congr 1
  congr 1
  exact Finset.card_nbij id (fun a ha => by simpa [PK] using ha) (fun a _ b _ h => h)
    (fun b hb => ⟨b, by simpa [PK] using hb, rfl⟩)

/-! ### The band law -/

lemma bandS_nonempty (i : ℕ) : (bandS i).Nonempty := by
  classical
  rcases i with _ | j
  · -- `bandLo 0 = 0`, so nothing is dropped
    obtain ⟨n, hn⟩ := PK_nonempty 0
    exact ⟨n, Finset.mem_filter.2 ⟨hn, by simp [bandLo]⟩⟩
  · rw [← Finset.card_pos]
    have h := card_bandS_ge j
    have hP : (0 : ℝ) < ((PK (j + 1)).card : ℝ) := by
      exact_mod_cast PK_card_pos (j + 1)
    have : (0 : ℝ) < ((bandS (j + 1)).card : ℝ) := by linarith
    exact_mod_cast this

open Classical in
/-- The band-restricted window law at the good atom, as a one-element family. -/
noncomputable def bandLaw (i : ℕ) (x : ℝ) : FinLaw (Unit → Fin (2 ^ kk i)) :=
  empirical (bandS i) (bandS_nonempty i)
    (fun n => fun _ : Unit => ZVec (gridAt i) (kk i) x n (goodAtom i))

open Classical in
lemma H₂_bandLaw (i : ℕ) (x : ℝ) :
    (bandLaw i x).H₂
      = (empirical (bandS i) (bandS_nonempty i)
          (fun n => ZVec (gridAt i) (kk i) x n (goodAtom i))).H₂ := by
  classical
  have hmap := (map_empirical (Ω := Fin (2 ^ kk i)) (Ω' := Unit → Fin (2 ^ kk i))
    (bandS_nonempty i) (fun n => ZVec (gridAt i) (kk i) x n (goodAtom i))
    (fun u => fun _ : Unit => u)).symm
  have hH := FinLaw.H₂_map_injective
    (empirical (bandS i) (bandS_nonempty i) (fun n => ZVec (gridAt i) (kk i) x n (goodAtom i)))
    (g := fun u : Fin (2 ^ kk i) => fun _ : Unit => u) (fun u u' h => congrFun h ())
  rw [← hH, ← hmap]
  rfl

/-! ### The band law is still certified -/

open Classical in
/-- **The band-restricted good atom keeps its deficit up to a factor 2 (plus a bit).**  The
restriction costs `(δ+1)/σ` and `σ ≥ 1/2`. -/
theorem H₂_bandLaw_ge (i : ℕ) :
    (kk i : ℝ) - 2 * (atomDeficit i + 1) ≤ (bandLaw i (primeLambertAtBase 4)).H₂ := by
  classical
  set f : ℕ → Fin (2 ^ kk i) :=
    fun n => ZVec (gridAt i) (kk i) (primeLambertAtBase 4) n (goodAtom i) with hf
  -- the full law has the good atom's deficit
  have hfull : ((kk i : ℝ) - atomDeficit i) ≤ (empirical (PK i) (PK_nonempty i) f).H₂ := by
    have hmap := map_coord_jointLawAt i (primeLambertAtBase 4) (goodAtom i)
    have hd := goodAtom_deficit i
    rw [FinLaw.coordDeficit] at hd
    rw [hmap] at hd
    linarith
  -- restriction
  have hrest := H₂_empirical_window_restrict_ge (m := kk i) (PK_nonempty i) (bandS_nonempty i)
    (bandS_subset i) f (δ := atomDeficit i) hfull
  -- σ ≥ 1/2
  have hPpos : (0 : ℝ) < ((PK i).card : ℝ) := by exact_mod_cast PK_card_pos i
  have hSpos : (0 : ℝ) < ((bandS i).card : ℝ) := by
    have := Finset.card_pos.2 (bandS_nonempty i)
    exact_mod_cast this
  have hσ : (1 : ℝ) / 2 ≤ ((bandS i).card : ℝ) / ((PK i).card : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num) hPpos]
    linarith [card_bandS_ge' i]
  have hδpos : (0 : ℝ) < atomDeficit i + 1 := by
    have := atomDeficit_pos i
    linarith
  have hcost : (atomDeficit i + 1) / (((bandS i).card : ℝ) / ((PK i).card : ℝ))
      ≤ 2 * (atomDeficit i + 1) := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : (1 : ℝ) ≤ 2 * (((bandS i).card : ℝ) / ((PK i).card : ℝ)) := by linarith
    nlinarith [hδpos, h2]
  rw [H₂_bandLaw]
  linarith

set_option maxHeartbeats 1000000 in
/-- **The band law's capture bound.**  Every binary word of length `ℓ` has, among the band's
windows and all their positions, frequency within `2√(2000 log 2·ℓ/√K)` of `2^{−ℓ}`. -/
theorem abs_posAvg_bandLaw_le (i ℓ : ℕ) (hℓ : 0 < ℓ) (hℓm : 2 * ℓ ≤ kk i)
    (w : Fin (2 ^ ℓ)) :
    |posAvg (kk i) ℓ (bandLaw i (primeLambertAtBase 4)) w - 1 / (2 : ℝ) ^ ℓ|
      ≤ 2 * Real.sqrt (2000 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKpos : (0 : ℝ) < (KK i : ℝ) := by
    have : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast KK_ge i
    linarith
  have hS0 : 0 < Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_pos.2 hKpos
  have hS400 : (400 : ℝ) ≤ Real.sqrt ((KK i : ℕ) : ℝ) := by
    have h : (160000 : ℝ) ≤ ((KK i : ℕ) : ℝ) := by exact_mod_cast KK_ge i
    have h2 : Real.sqrt (160000 : ℝ) ≤ Real.sqrt ((KK i : ℕ) : ℝ) := Real.sqrt_le_sqrt h
    have h400 : Real.sqrt (160000 : ℝ) = 400 := by
      rw [show (160000 : ℝ) = 400 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h400 ▸ h2]
  have hδ : (0 : ℝ) < 2 * (atomDeficit i + 1) := by
    have := atomDeficit_pos i; linarith
  have hdef : ((kk i : ℝ) - 2 * (atomDeficit i + 1)) * (Fintype.card Unit : ℝ)
      ≤ (bandLaw i (primeLambertAtBase 4)).H₂ := by
    simp only [Fintype.card_unit, Nat.cast_one, mul_one]
    exact H₂_bandLaw_ge i
  have hmain := abs_posAvg_sub_le hℓ (by omega) (bandLaw i (primeLambertAtBase 4)) w hδ hdef
  refine hmain.trans ?_
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
  -- `2(100√K + 1) ≤ 201√K`
  have hdle : 2 * (atomDeficit i + 1) ≤ 201 * Real.sqrt ((KK i : ℕ) : ℝ) := by
    rw [atomDeficit]
    linarith [hS400]
  have hstep : Real.log 2 * (ℓ : ℝ) * (2 * (atomDeficit i + 1)) / ((kk i : ℝ) - ℓ + 1)
      ≤ 2000 * Real.log 2 * (ℓ : ℝ) / Real.sqrt (KK i) := by
    rw [div_le_div_iff₀ hden hS0]
    have hnum : Real.log 2 * (ℓ : ℝ) * (2 * (atomDeficit i + 1)) * Real.sqrt ((KK i : ℕ) : ℝ)
        ≤ Real.log 2 * (ℓ : ℝ) * (201 * Real.sqrt ((KK i : ℕ) : ℝ))
            * Real.sqrt ((KK i : ℕ) : ℝ) := by
      have hc : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ) * Real.sqrt ((KK i : ℕ) : ℝ) := by positivity
      nlinarith [hdle, hc]
    have hrw : Real.log 2 * (ℓ : ℝ) * (201 * Real.sqrt ((KK i : ℕ) : ℝ))
        * Real.sqrt ((KK i : ℕ) : ℝ) = 804 * Real.log 2 * (ℓ : ℝ) * (kk i : ℝ) := by
      linear_combination (201 * Real.log 2 * (ℓ : ℝ)) * hsq
    have hfin : 804 * Real.log 2 * (ℓ : ℝ) * (kk i : ℝ)
        ≤ 2000 * Real.log 2 * (ℓ : ℝ) * ((kk i : ℝ) - ℓ + 1) := by
      have hc : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ) * (kk i : ℝ) := by positivity
      have hstep2 := mul_le_mul_of_nonneg_left hhalf
        (by positivity : (0:ℝ) ≤ 2000 * Real.log 2 * (ℓ : ℝ))
      linarith [hc, hstep2]
    rw [hrw] at hnum
    linarith [hnum, hfin]
  have hpos1 : (0 : ℝ) ≤ Real.log 2 * (ℓ : ℝ) * (2 * (atomDeficit i + 1))
      / ((kk i : ℝ) - ℓ + 1) := by
    have : (0:ℝ) ≤ 2 * (atomDeficit i + 1) := hδ.le
    positivity
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (by norm_num)

/-! ### The band count, and its limit -/

open Classical in
/-- **The band's count rendering.** -/
theorem posAvg_bandLaw_eq_count (i ℓ : ℕ) (x : ℝ) (w : Fin (2 ^ ℓ)) :
    posAvg (kk i) ℓ (bandLaw i x) w
      = (∑ p : Fin (kk i - ℓ + 1),
            (((bandS i).filter fun n =>
              posAt (kk i) ℓ (p : ℕ) (ZVec (gridAt i) (kk i) x n (goodAtom i)) = w).card : ℝ))
        / (((bandS i).card : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ)) := by
  classical
  have hp : ∀ p : Fin (kk i - ℓ + 1),
      ((bandLaw i x).map
          (fun z : Unit → Fin (2 ^ kk i) => posAt (kk i) ℓ (p : ℕ) (z default))).prob {w}
        = (((bandS i).filter fun n =>
              posAt (kk i) ℓ (p : ℕ) (ZVec (gridAt i) (kk i) x n (goodAtom i)) = w).card : ℝ)
          / ((bandS i).card : ℝ) := by
    intro p
    rw [bandLaw, FinLaw.prob, Finset.sum_singleton]
    exact map_empirical_p (bandS_nonempty i) _ _ w
  rw [posAvg, Fintype.sum_prod_type]
  simp only [Fintype.card_unit, Nat.cast_one, one_mul, Finset.univ_unique,
    Finset.sum_singleton, hp]
  rw [← Finset.sum_div, div_div]

open Classical in
/-- **The band's digit rendering.** -/
theorem posAvg_bandLaw_eq_digits (i ℓ : ℕ) (hℓm : ℓ ≤ kk i) (x : ℝ) (w : Fin (2 ^ ℓ)) :
    posAvg (kk i) ℓ (bandLaw i x) w
      = (∑ p : Fin (kk i - ℓ + 1),
            (((bandS i).filter fun n =>
              blockVal (Int.fract x) (2 * kIdx (gridAt i) n (goodAtom i) + (p : ℕ)) ℓ
                = (w : ℕ)).card : ℝ))
        / (((bandS i).card : ℝ) * ((kk i - ℓ + 1 : ℕ) : ℝ)) := by
  classical
  rw [posAvg_bandLaw_eq_count i ℓ x w]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  have hZ : ∀ n : ℕ, ZVec (gridAt i) (kk i) x n (goodAtom i)
      = ⟨blockVal (Int.fract x) (2 * kIdx (gridAt i) n (goodAtom i)) (kk i),
        blockVal_lt _ _ _⟩ :=
    fun n => Fin.ext (ZSample_eq_blockVal (gridAt i) (kk i) x n (goodAtom i))
  have hfit : (p : ℕ) + ℓ ≤ kk i := by
    have := p.isLt
    omega
  refine Finset.filter_congr fun n _ => ?_
  rw [hZ n, posAt_blockVal _ _ _ _ _ hfit]
  exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩

open Classical in
/-- **The band's frequency limit.**  For every finite binary word `v`, the proportion of pairs
`(n, p)` with `n` a band-`i` sample time at the good atom and `p` a window position, at which
`v` occurs in `G₄`'s digits at `2·kIdx(n, goodAtom i) + p`, tends to `2^{−|v|}`. -/
theorem tendsto_band_occursCount (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) :
    Tendsto (fun i =>
      (∑ p : Fin (kk i - v.length + 1),
          (((bandS i).filter fun n =>
            OccursAt 2 (primeLambertAtBase 4) v
              (2 * kIdx (gridAt i) n (goodAtom i) + (p : ℕ))).card : ℝ))
        / (((bandS i).card : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)))
      atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
  classical
  set w : ∀ i : ℕ, Fin (2 ^ v.length) := fun _ => ⟨wordVal v, wordVal_lt hv⟩ with hw
  have hgrow : Tendsto (fun i => (v.length : ℝ) / Real.sqrt (KK i)) atTop (nhds 0) := by
    have hsqrt : Tendsto (fun i => Real.sqrt (KK i)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_KK_atTop
    exact hsqrt.const_div_atTop _
  have hinner : Tendsto (fun i => 2000 * Real.log 2 * (v.length : ℝ) / Real.sqrt (KK i))
      atTop (nhds 0) := by
    have h := hgrow.const_mul (2000 * Real.log 2)
    simp only [mul_zero] at h
    refine h.congr fun i => ?_
    rw [mul_div_assoc]
  have hsq : Tendsto (fun i => 2 * Real.sqrt (2000 * Real.log 2 * (v.length : ℝ)
      / Real.sqrt (KK i))) atTop (nhds 0) := by
    have := hinner.sqrt
    simpa using this.const_mul (2 : ℝ)
  have hzero : Tendsto (fun i =>
      posAvg (kk i) v.length (bandLaw i (primeLambertAtBase 4)) (w i)
        - 1 / (2 : ℝ) ^ v.length) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hsq
    filter_upwards [eventually_ge_atTop (2 * v.length)] with i hi
    have hle : 2 * v.length ≤ kk i := by unfold kk; omega
    simpa [Real.norm_eq_abs] using abs_posAvg_bandLaw_le i v.length hlen hle (w i)
  have hmain : Tendsto (fun i =>
      posAvg (kk i) v.length (bandLaw i (primeLambertAtBase 4)) (w i))
      atTop (nhds (1 / (2 : ℝ) ^ v.length)) := by
    have hlim : Tendsto (fun _ : ℕ => (1 : ℝ) / (2 : ℝ) ^ v.length) atTop
        (nhds (1 / (2 : ℝ) ^ v.length)) := tendsto_const_nhds
    simpa using hzero.add hlim
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop v.length] with i hi
  have hle : v.length ≤ kk i := by unfold kk; omega
  rw [posAvg_bandLaw_eq_digits i v.length hle _ (w i)]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 2
  refine Finset.filter_congr fun n _ => ?_
  exact blockVal_eq_wordVal_iff (y := primeLambertAtBase 4) hv

end NormalNumbers.G4.Sched
