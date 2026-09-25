import NormalNumbers.AbelianNormal

/-!
# C4: which sets of window lengths can a binary sequence be abelian-normal at, exactly?

Conjecture C4 (`CONJECTURES-2026-09-23-casting-out-and-rungs.md`): for every `S ⊆ {L ≥ 1}` with
`S = ∅` or `1 ∈ S` — infinite `S` included — some binary sequence is abelian at exactly the
lengths in `S`.  The one forced implication is `abelianAt_one_of_abelianAt` (the mean of
Binomial(`L`, 1/2) forces digit density 1/2).  Probe: `probes/abelian_window_sets.py` (finite `S`,
`k ≤ 8`, Markov perturbations of the uniform measure).  See `KICKOFF-2026-09-24-c4.md`.
-/

open Finset Filter Topology

namespace NormalNumbers.Abelian

/-- Abelian at the single window length `L`: one-counts of length-`L` windows are
asymptotically Binomial(`L`, 1/2). -/
def IsAbelianAt (s : ℕ → ℕ) (L : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ L → Tendsto (onesFreq s L j) atTop (𝓝 ((L.choose j : ℝ) / 2 ^ L))

/-- **NECESSITY (ratified).**  Abelian at any length forces abelian at length 1. -/
theorem abelianAt_one_of_abelianAt (s : ℕ → ℕ) (hs : ∀ m, s m < 2) (L : ℕ) (hL : 1 ≤ L)
    (h : IsAbelianAt s L) : IsAbelianAt s 1 := by
  sorry

/-- **C4 (ratified headline).**  Every admissible set of window lengths is realized exactly. -/
theorem c4_realizable (S : Set ℕ) (hS : ∀ L ∈ S, 1 ≤ L) (hadm : S = ∅ ∨ 1 ∈ S) :
    ∃ s : ℕ → ℕ, (∀ m, s m < 2) ∧ ∀ L : ℕ, 1 ≤ L → (IsAbelianAt s L ↔ L ∈ S) := by
  sorry

end NormalNumbers.Abelian
