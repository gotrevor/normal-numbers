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

end NormalNumbers.G4.Sched
