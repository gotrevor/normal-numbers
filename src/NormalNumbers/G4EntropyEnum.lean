/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBlockWord
import NormalNumbers.G4EntropyWall

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

/-! ### The disjunctive real read off the subsequence -/

open Classical in
/-- The digit sequence of `G₄` along the strictly increasing enumeration. -/
noncomputable def enumDigits (j : ℕ) : ℕ :=
  digitOf 2 (Int.fract (primeLambertAtBase 4)) (sampleEnum j)

lemma enumDigits_lt (j : ℕ) : enumDigits j < 2 := Nat.mod_lt _ (by omega)

/-- **The subsequence never sticks at `1`.**  Apply `occurs_along_sampleEnum` to the word
`1^N ++ [0]`: the match puts a `0` at index `≥ N`. -/
theorem properDigits_enumDigits : ProperDigits 2 enumDigits := by
  intro N
  have hlenv : (List.replicate (N + 1) 0).length = N + 1 := by simp
  have hbin : ∀ j, ∀ h : j < (List.replicate (N + 1) 0).length,
      (List.replicate (N + 1) 0)[j] < 2 := by
    intro j hj
    rw [List.getElem_replicate]
    omega
  obtain ⟨t, ht⟩ := occurs_along_sampleEnum (List.replicate (N + 1) 0) (by omega) hbin
  refine ⟨t + N, by omega, ?_⟩
  have hN : N < (List.replicate (N + 1) 0).length := by omega
  have h := ht N hN
  rw [List.getD_eq_getElem _ 0 hN, List.getElem_replicate] at h
  have h0 : enumDigits (t + N) = 0 := h
  rw [h0]
  omega

/-- **The disjunctive real.**  `G₄`'s binary digits, read along the strictly increasing,
schedule-defined enumeration of ALL sampled positions, sum to a real in which **every** finite
binary word occurs.

Unlike `isNormal_realOfDigits_samplePos`, the position map here is a genuine *subsequence*:
`sampleEnum` is `StrictMono` and every value is a sampled position.  Still not a claim about
`G₄`. -/
theorem isDisjunctive_enumReal : IsDisjunctive 2 (realOfDigits 2 enumDigits) := by
  have hmem := realOfDigits_mem_Ico 2 (le_refl 2) enumDigits enumDigits_lt properDigits_enumDigits
  rw [Set.mem_Ico] at hmem
  have hfract : Int.fract (realOfDigits 2 enumDigits) = realOfDigits 2 enumDigits :=
    Int.fract_eq_self.mpr hmem
  have hdig : digitOf 2 (realOfDigits 2 enumDigits) = enumDigits :=
    digitOf_realOfDigits 2 (le_refl 2) enumDigits enumDigits_lt properDigits_enumDigits
  rw [isDisjunctive_iff_forall_occursAt 2 (le_refl 2)]
  intro w hw
  by_cases hw0 : w = []
  · subst hw0
    exact ⟨0, fun j hj => absurd hj (by simp)⟩
  · have hlen : 0 < w.length := List.length_pos_iff.2 hw0
    have hbin : ∀ j, ∀ h : j < w.length, w[j] < 2 :=
      fun j hj => hw _ (List.getElem_mem hj)
    obtain ⟨t, ht⟩ := occurs_along_sampleEnum w hlen hbin
    refine ⟨t, fun j hj => ?_⟩
    rw [hfract, hdig]
    have h : enumDigits (t + j) = w.getD j 0 := ht j hj
    rw [h]
    exact List.getD_eq_getElem _ 0 hj

/-- Hence the real read off the subsequence is irrational. -/
theorem irrational_enumReal : Irrational (realOfDigits 2 enumDigits) :=
  isDisjunctive_enumReal.irrational

/-! ### Non-vacuity: the sampled set is sparse, so `sampleEnum` is far from the identity -/

/-- `IsSampledPos` is the repo's `IsSampled`: a position read by *some* scale. -/
lemma isSampledPos_iff_isSampled (q : ℕ) : IsSampledPos q ↔ IsSampled q := by
  constructor
  · rintro ⟨i, n, hn, α, p, hp, rfl⟩
    exact ⟨i, (mem_sampledPos (gridAt i)).2 ⟨n, hn, α, p, hp, rfl⟩⟩
  · rintro ⟨i, hi⟩
    obtain ⟨n, hn, α, p, hp, hq⟩ := (mem_sampledPos (gridAt i)).1 hi
    exact ⟨i, n, hn, α, p, hp, hq⟩

open Classical in
/-- Every position below `L` that some scale samples is sampled by one of finitely many scales. -/
lemma exists_cover (L : ℕ) : ∃ I : ℕ,
    ((Finset.range L).filter IsSampled)
      ⊆ (Finset.range (I + 1)).biUnion (fun i => (sampledPosAt i).filter (fun j => j < L)) := by
  classical
  set S := (Finset.range L).filter IsSampled with hS
  have hwit : ∀ q ∈ S, ∃ i, q ∈ sampledPosAt i := by
    intro q hq
    exact (Finset.mem_filter.1 hq).2
  refine ⟨S.sup (fun q => if h : ∃ i, q ∈ sampledPosAt i then h.choose else 0), fun q hq => ?_⟩
  have hex : ∃ i, q ∈ sampledPosAt i := hwit q hq
  have hmem : q ∈ sampledPosAt hex.choose := hex.choose_spec
  refine Finset.mem_biUnion.2 ⟨hex.choose, ?_, ?_⟩
  · refine Finset.mem_range.2 (Nat.lt_succ_of_le ?_)
    have hle := Finset.le_sup (f := fun q =>
      if h : ∃ i, q ∈ sampledPosAt i then h.choose else 0) hq
    rwa [dif_pos hex] at hle
  · exact Finset.mem_filter.2 ⟨hmem, (Finset.mem_range.1 (Finset.mem_filter.1 hq).1)⟩

open Classical in
/-- **The sampled set has density at most ¼.**  Every scale's own density is at most
`⅛(2/K⁶)^K ≤ ⅛·2^{−K}` (`density_le_pow_real`), and those sum over all scales to at most `¼`.

So `sampleEnum` is *not* the identity and `isDisjunctive_enumReal` is not a restatement of
`isDisjunctive_two`: the subsequence omits at least three quarters of the digits. -/
theorem card_filter_isSampled_le (L : ℕ) :
    (((Finset.range L).filter IsSampled).card : ℝ) ≤ (L : ℝ) / 4 := by
  classical
  obtain ⟨I, hI⟩ := exists_cover L
  have hcard : ((Finset.range L).filter IsSampled).card
      ≤ ∑ i ∈ Finset.range (I + 1), ((sampledPosAt i).filter (fun j => j < L)).card :=
    le_trans (Finset.card_le_card hI) (Finset.card_biUnion_le)
  have hcardR : (((Finset.range L).filter IsSampled).card : ℝ)
      ≤ ∑ i ∈ Finset.range (I + 1),
          (((sampledPosAt i).filter (fun j => j < L)).card : ℝ) := by
    exact_mod_cast hcard
  have hterm : ∀ i ∈ Finset.range (I + 1),
      (((sampledPosAt i).filter (fun j => j < L)).card : ℝ)
        ≤ (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ i * (L : ℝ) := by
    intro i _
    refine (density_le_pow_real i L).trans ?_
    have hK1 : (1 : ℕ) ≤ KK i := KK_one_le i
    have hKR : (2 : ℝ) ≤ (KK i : ℝ) := by
      have : (160000 : ℕ) ≤ KK i := KK_ge i
      have h2 : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast this
      linarith
    have hsmall : (2 : ℝ) / (KK i : ℝ) ^ 6 ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hKR 6]
    have hnn : (0 : ℝ) ≤ 2 / (KK i : ℝ) ^ 6 := by positivity
    have hpow : (2 / (KK i : ℝ) ^ 6) ^ KK i ≤ (1 / 2 : ℝ) ^ KK i :=
      pow_le_pow_left₀ hnn hsmall _
    have hmono : (1 / 2 : ℝ) ^ KK i ≤ (1 / 2 : ℝ) ^ i := by
      refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
      have : i ≤ KK i := by unfold KK kk; omega
      exact this
    have hL : (0 : ℝ) ≤ (L : ℝ) := by positivity
    have : (2 / (KK i : ℝ) ^ 6) ^ KK i ≤ (1 / 2 : ℝ) ^ i := hpow.trans hmono
    nlinarith [this, hL]
  refine le_trans hcardR (le_trans (Finset.sum_le_sum hterm) ?_)
  have hgeom : ∑ i ∈ Finset.range (I + 1), (1 / 2 : ℝ) ^ i ≤ 2 := sum_geometric_two_le _
  have hL : (0 : ℝ) ≤ (L : ℝ) := by positivity
  calc ∑ i ∈ Finset.range (I + 1), (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ i * (L : ℝ)
      = (1 / 8 : ℝ) * (L : ℝ) * ∑ i ∈ Finset.range (I + 1), (1 / 2 : ℝ) ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (1 / 8 : ℝ) * (L : ℝ) * 2 := by
        refine mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = (L : ℝ) / 4 := by ring

end NormalNumbers.G4.Sched
