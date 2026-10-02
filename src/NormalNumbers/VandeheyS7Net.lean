/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
/-
# S7-NT: the net EXISTS — fact (δ) delivers a genuine `StateNet`

S7-CL made `StateNet` an interface: centres, a cell assignment, and the guarantee that a state of
width `≥ η` lies within `ρ` of its centre.  This module *builds* one, so that
`blockAverageBound_of_classFreq` is not vacuous.

The construction is exactly directive fact (δ) cashed in:

* `runState_entries_abs_le` (S7-BX) puts the entry vectors of all wide run states in the compact
  box `[−M,M]⁴`, `M = √(6|det Φ|/η)`;
* a compact set is totally bounded, so the *reachable* wide entry vectors admit a finite `ρ`-net
  **whose centres are themselves reachable states** (`TotallyBounded.exists_subset`);
* choosing, for each centre, a time realizing it turns those points back into honest `MapState`s
  — which matters, because an arbitrary point of `ℝ⁴` need not satisfy the `MapState` axioms, so
  a naive grid net would not typecheck, let alone be Lipschitz.

`exists_stateNet` is the result: for every `η, ρ > 0` there are `M` and a `StateNet Φ x η ρ M`.
-/
import NormalNumbers.VandeheyS7Class

namespace NormalNumbers.VandeheyS7

open Set Filter Finset NormalNumbers

namespace MapState

/-- The four matrix entries as a point of `ℝ⁴` (sup metric). -/
def entryVec (s : MapState) : Fin 4 → ℝ := ![s.a, s.b, s.c, s.d]

lemma dist_entryVec_le {s t : MapState} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : dist (entryVec s) (entryVec t) ≤ ρ) :
    |s.a - t.a| ≤ ρ ∧ |s.b - t.b| ≤ ρ ∧ |s.c - t.c| ≤ ρ ∧ |s.d - t.d| ≤ ρ := by
  rw [dist_pi_le_iff hρ] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [entryVec, Real.dist_eq] using h 0
  · simpa [entryVec, Real.dist_eq] using h 1
  · simpa [entryVec, Real.dist_eq] using h 2
  · simpa [entryVec, Real.dist_eq] using h 3

/-- **Fact (δ) as a subset statement.**  The entry vectors of wide run states lie in a compact
box of `ℝ⁴`. -/
theorem entryVec_mem_box {Φ : MapState} {x η : ℝ} (hη : 0 < η) {m : ℕ}
    (hw : η ≤ (runState Φ x (m + 2)).width) :
    entryVec (runState Φ x (m + 2)) ∈
      Set.univ.pi (fun _ : Fin 4 =>
        Icc (-Real.sqrt (6 * |Φ.det| / η)) (Real.sqrt (6 * |Φ.det| / η))) := by
  obtain ⟨ha, hb, hc, hd⟩ := runState_entries_abs_le hη m hw
  intro i _
  fin_cases i
  · simpa [entryVec] using abs_le.mp ha
  · simpa [entryVec] using abs_le.mp hb
  · simpa [entryVec] using abs_le.mp hc
  · simpa [entryVec] using abs_le.mp hd

/-- **S7-NT.**  For every `η, ρ > 0` a finite net of the run's wide states exists, with centres
that are themselves run states. -/
theorem exists_stateNet (Φ : MapState) (x : ℝ) {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) :
    ∃ M : ℕ, Nonempty (StateNet Φ x η ρ M) := by
  classical
  set Mb := Real.sqrt (6 * |Φ.det| / η) with hMb
  set box : Set (Fin 4 → ℝ) := Set.univ.pi (fun _ : Fin 4 => Icc (-Mb) Mb) with hbox
  have hboxc : IsCompact box := isCompact_univ_pi (fun _ => isCompact_Icc)
  set W : Set ℕ := {m : ℕ | η ≤ (runState Φ x (m + 2)).width} with hW
  set A : Set (Fin 4 → ℝ) := (fun m => entryVec (runState Φ x (m + 2))) '' W with hA
  have hAB : A ⊆ box := by
    rintro y ⟨m, hm, rfl⟩
    exact entryVec_mem_box hη hm
  have htb : TotallyBounded A := hboxc.totallyBounded.subset hAB
  obtain ⟨t, hts, htfin, htcov⟩ :=
    htb.exists_subset (Metric.dist_mem_uniformity hρ)
  obtain ⟨F, hF⟩ := htfin.exists_finset_coe
  have hFt : ∀ y : Fin 4 → ℝ, y ∈ F ↔ y ∈ t := by
    intro y; constructor
    · intro hy; rw [← hF]; exact_mod_cast hy
    · intro hy; have : y ∈ (F : Set (Fin 4 → ℝ)) := by rw [hF]; exact hy
      exact_mod_cast this
  -- every centre is realized by a run state, so it is an honest `MapState`
  have hcen : ∀ j : Fin F.card,
      ∃ s : MapState, entryVec s = ((F.equivFin.symm j : {y // y ∈ F}) : Fin 4 → ℝ) := by
    intro j
    have hy : ((F.equivFin.symm j : {y // y ∈ F}) : Fin 4 → ℝ) ∈ A :=
      hts ((hFt _).1 (F.equivFin.symm j).2)
    obtain ⟨m, -, hm⟩ := hy
    exact ⟨runState Φ x (m + 2), hm⟩
  choose cen0 hcen0 using hcen
  set cen : Fin (F.card + 1) → MapState := fun i =>
    if h : (i : ℕ) < F.card then cen0 ⟨(i : ℕ), h⟩ else Φ with hcendef
  have key : ∀ m : ℕ, ∃ i : Fin (F.card + 1),
      η ≤ (runState Φ x (m + 2)).width →
        dist (entryVec (runState Φ x (m + 2))) (entryVec (cen i)) ≤ ρ := by
    intro m
    by_cases hm : η ≤ (runState Φ x (m + 2)).width
    · have hmem : entryVec (runState Φ x (m + 2)) ∈ A := ⟨m, hm, rfl⟩
      have hcov := htcov hmem
      rw [Set.mem_iUnion₂] at hcov
      obtain ⟨y, hyt, hy⟩ := hcov
      have hyF : y ∈ F := (hFt y).2 hyt
      set j : Fin F.card := F.equivFin ⟨y, hyF⟩ with hj
      refine ⟨⟨(j : ℕ), by omega⟩, fun _ => ?_⟩
      have hlt : ((⟨(j : ℕ), by omega⟩ : Fin (F.card + 1)) : ℕ) < F.card := j.2
      have hcenval : cen ⟨(j : ℕ), by omega⟩ = cen0 ⟨(j : ℕ), hlt⟩ := by
        rw [hcendef]; exact dif_pos hlt
      have hjj : (⟨(j : ℕ), hlt⟩ : Fin F.card) = j := by exact Fin.ext rfl
      have hent : entryVec (cen ⟨(j : ℕ), by omega⟩) = y := by
        rw [hcenval, hjj, hcen0 j, hj, Equiv.symm_apply_apply]
      rw [hent]
      exact le_of_lt hy
    · exact ⟨Fin.last _, fun h => absurd h hm⟩
  choose idx hidx using key
  refine ⟨F.card + 1, ⟨?_⟩⟩
  exact { cen := cen
          idx := idx
          near := fun m hm => dist_entryVec_le hρ.le (hidx m hm) }

end MapState

section Audit

#print axioms MapState.entryVec_mem_box
#print axioms MapState.exists_stateNet

end Audit

end NormalNumbers.VandeheyS7
