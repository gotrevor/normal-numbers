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

end NormalNumbers.G4.Sched
