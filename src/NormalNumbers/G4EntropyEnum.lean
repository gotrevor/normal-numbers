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
  obtain ⟨n, hn⟩ := PK_nonempty N
  refine ⟨2 * kIdx (gridAt N) n (Classical.arbitrary _) + (kk N - 1),
    ⟨N, n, hn, Classical.arbitrary _, kk N - 1, ?_, rfl⟩, ?_⟩
  · have := kk_pos N; omega
  · have : kk N = 40000 + N := rfl
    omega

theorem infinite_isSampledPos : (Set.ofPred IsSampledPos).Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := hfin.bddAbove
  obtain ⟨q, hq, hqM⟩ := exists_isSampledPos_gt M
  exact absurd (hM (show q ∈ Set.ofPred IsSampledPos from hq)) (by omega)

open Classical in
/-- **The strictly increasing enumeration of the sampled positions.**  Defined from the schedule
alone. -/
noncomputable def sampleEnum (j : ℕ) : ℕ := Nat.nth IsSampledPos j

theorem sampleEnum_strictMono : StrictMono sampleEnum := by
  intro a b hab
  exact (Nat.nth_lt_nth infinite_isSampledPos).2 hab

theorem sampleEnum_mem (j : ℕ) : IsSampledPos (sampleEnum j) :=
  Nat.nth_mem_of_infinite infinite_isSampledPos j

open Classical in
/-- **Consecutive sampled positions are adjacent in the enumeration.**  This is what lets a word
that occupies a run of positions inside one window survive the enumeration. -/
theorem sampleEnum_run {q ℓ : ℕ} (h : ∀ j < ℓ, IsSampledPos (q + j)) (j : ℕ) (hj : j < ℓ) :
    sampleEnum (Nat.count IsSampledPos q + j) = q + j := by
  classical
  have hcount : ∀ k, k ≤ ℓ → Nat.count IsSampledPos (q + k) = Nat.count IsSampledPos q + k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hk' : k < ℓ := by omega
      have hstep : q + (k + 1) = (q + k) + 1 := by ring
      rw [hstep, Nat.count_succ, ih (by omega), if_pos (h k hk')]
      ring
  rw [← hcount j (le_of_lt hj)]
  exact Nat.nth_count (h j hj)

/-- For every binary word and every scale beyond a threshold, some sampled window of that scale
contains the word. -/
theorem exists_occursAt_sampled (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) :
    ∃ i n, n ∈ PK i ∧ ∃ (α : (gridAt i).Atom) (p : ℕ), p + v.length ≤ kk i ∧
      OccursAt 2 (primeLambertAtBase 4) v (2 * kIdx (gridAt i) n α + p) := by
  classical
  have hlim := tendsto_occursCountP_primeLambertFour v hlen hv
  have hpos : (0 : ℝ) < 1 / (2 : ℝ) ^ v.length := by positivity
  obtain ⟨i, hi, hi2⟩ :=
    ((hlim.eventually (eventually_gt_nhds hpos)).and (eventually_ge_atTop v.length)).exists
  have hilen : v.length ≤ kk i := by
    have h : v.length ≤ i := hi2
    unfold kk
    omega
  set F : (gridAt i).Atom × Fin (kk i - v.length + 1) → ℕ := fun c =>
    ((PK i).filter fun n =>
      OccursAt 2 (primeLambertAtBase 4) v
        (2 * kIdx (gridAt i) n c.1 + (c.2 : ℕ))).card with hF
  have hnum : (0 : ℝ) < ∑ c, (F c : ℝ) := by
    by_contra hcon
    push_neg at hcon
    have hden : (0 : ℝ) ≤ ((PK i).card : ℝ)
        * ((Fintype.card (gridAt i).Atom : ℝ) * ((kk i - v.length + 1 : ℕ) : ℝ)) := by
      positivity
    exact absurd hi (not_lt.2 (div_nonpos_of_nonpos_of_nonneg hcon hden))
  obtain ⟨c, hc⟩ : ∃ c, F c ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    rw [Finset.sum_eq_zero fun c _ => by rw [hcon c]; norm_num] at hnum
    exact lt_irrefl _ hnum
  obtain ⟨n, hn⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hc)
  rw [Finset.mem_filter] at hn
  refine ⟨i, n, hn.1, c.1, (c.2 : ℕ), ?_, hn.2⟩
  have := c.2.isLt
  omega

open Classical in
/-- **The endpoint.**  Every finite binary word occurs in `G₄`'s binary digits read along the
strictly increasing, schedule-defined sequence `sampleEnum` of sampled positions. -/
theorem occurs_along_sampleEnum (v : List ℕ) (hlen : 0 < v.length)
    (hv : ∀ j, ∀ h : j < v.length, v[j] < 2) :
    ∃ t, MatchesAt
      (fun j => digitOf 2 (Int.fract (primeLambertAtBase 4)) (sampleEnum j)) v t := by
  classical
  obtain ⟨i, n, hn, α, p, hfit, hocc⟩ := exists_occursAt_sampled v hlen hv
  set q := 2 * kIdx (gridAt i) n α + p with hq
  have hrun : ∀ j < v.length, IsSampledPos (q + j) := by
    intro j hj
    exact ⟨i, n, hn, α, p + j, by omega, by rw [hq]; ring⟩
  refine ⟨Nat.count IsSampledPos q, fun j hj => ?_⟩
  have hnth := sampleEnum_run hrun j hj
  simp only []
  rw [hnth]
  rw [hocc j hj]
  exact (List.getD_eq_getElem v 0 hj).symm

end NormalNumbers.G4.Sched
