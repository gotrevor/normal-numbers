/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBlockWord

/-!
# Entropy expedition — the strictly increasing sampled-position enumeration

`G4EntropyBlockWord.samplePos` reuses positions (`rep m` copies of block `m`), and `E-T8`'s
upgrade to a strictly increasing map is refuted at the *normality* level by
`G4EntropySubsample.chunks_insufficient`.  At the **disjunctivity** level it is reachable, and
this module builds it.

`sampleEnum` is the increasing enumeration of the set of ALL sampled positions of ALL scales.
It is strictly monotone and mentions no real.  The key observation is that consecutive integers
in that set are *adjacent* in the enumeration — nothing can sit between `q` and `q+1` — so a word
occupying a run of positions inside one sampled window survives the enumeration as a contiguous
block.  Combined with `tendsto_occursCountP_primeLambertFour` (every binary word occurs in a
positive fraction of the sampled windows), every finite binary word occurs in `G₄`'s digits read
along `sampleEnum`.

**Not a claim about `G₄`.**  This is a statement about `G₄`'s digits restricted to a density-zero
set of positions; `G₄`'s own normality stays closed on this mechanism.
-/

open Finset Filter

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4Entropy NormalNumbers.PrimeLambert

/-- A digit position covered by some sampled window of some scale. -/
def IsSampledPos (q : ℕ) : Prop :=
  ∃ i n, n ∈ PK i ∧ ∃ (α : (gridAt i).Atom) (p : ℕ), p < kk i ∧
    q = 2 * kIdx (gridAt i) n α + p

/-- There are arbitrarily late sampled positions. -/
theorem exists_isSampledPos_gt (N : ℕ) : ∃ q, IsSampledPos q ∧ N < q := by
  sorry

theorem infinite_isSampledPos : (Set.ofPred IsSampledPos).Infinite := by
  sorry

open Classical in
/-- **The strictly increasing enumeration of the sampled positions.**  Defined from the schedule
alone. -/
noncomputable def sampleEnum (j : ℕ) : ℕ := Nat.nth IsSampledPos j

theorem sampleEnum_strictMono : StrictMono sampleEnum := by
  sorry

theorem sampleEnum_mem (j : ℕ) : IsSampledPos (sampleEnum j) :=
  Nat.nth_mem_of_infinite infinite_isSampledPos j

open Classical in
/-- **Consecutive sampled positions are adjacent in the enumeration.**  This is what lets a word
that occupies a run of positions inside one window survive the enumeration. -/
theorem sampleEnum_run {q ℓ : ℕ} (h : ∀ j < ℓ, IsSampledPos (q + j)) (j : ℕ) (hj : j < ℓ) :
    sampleEnum (Nat.count IsSampledPos q + j) = q + j := by
  sorry

/-- For every binary word and every scale beyond a threshold, some sampled window of that scale
contains the word. -/
theorem exists_occursAt_sampled (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) :
    ∃ i n, n ∈ PK i ∧ ∃ (α : (gridAt i).Atom) (p : ℕ), p + v.length ≤ kk i ∧
      OccursAt 2 (primeLambertAtBase 4) v (2 * kIdx (gridAt i) n α + p) := by
  sorry

open Classical in
/-- **The endpoint.**  Every finite binary word occurs in `G₄`'s binary digits read along the
strictly increasing, schedule-defined sequence `sampleEnum` of sampled positions. -/
theorem occurs_along_sampleEnum (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) :
    ∃ t, MatchesAt
      (fun j => digitOf 2 (Int.fract (primeLambertAtBase 4)) (sampleEnum j)) v t := by
  sorry

end NormalNumbers.G4.Sched
