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

/-! ### The sampled set has density zero -/

open Classical in
/-- The tail cover: positions below `L` sampled only by scales `> I`. -/
lemma exists_cover_tail (I L : ℕ) : ∃ J,
    ((Finset.range L).filter (fun q => ∃ i, I < i ∧ q ∈ sampledPosAt i))
      ⊆ (Finset.Ico (I + 1) (J + 1)).biUnion
          (fun i => (sampledPosAt i).filter (fun j => j < L)) := by
  classical
  set S := (Finset.range L).filter (fun q => ∃ i, I < i ∧ q ∈ sampledPosAt i) with hS
  refine ⟨S.sup (fun q => if h : ∃ i, I < i ∧ q ∈ sampledPosAt i then h.choose else 0),
    fun q hq => ?_⟩
  have hex : ∃ i, I < i ∧ q ∈ sampledPosAt i := (Finset.mem_filter.1 hq).2
  refine Finset.mem_biUnion.2 ⟨hex.choose, ?_, ?_⟩
  · refine Finset.mem_Ico.2 ⟨hex.choose_spec.1, Nat.lt_succ_of_le ?_⟩
    have hle := Finset.le_sup (f := fun q =>
      if h : ∃ i, I < i ∧ q ∈ sampledPosAt i then h.choose else 0) hq
    rwa [dif_pos hex] at hle
  · exact Finset.mem_filter.2 ⟨hex.choose_spec.2,
      Finset.mem_range.1 (Finset.mem_filter.1 hq).1⟩

/-- Each scale's density bound, in the geometric form the tail sum consumes. -/
lemma density_geom (i L : ℕ) :
    (((sampledPosAt i).filter (fun j => j < L)).card : ℝ)
      ≤ (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ i * (L : ℝ) := by
  refine (density_le_pow_real i L).trans ?_
  have hKR : (2 : ℝ) ≤ (KK i : ℝ) := by
    have h : (160000 : ℕ) ≤ KK i := KK_ge i
    have h2 : (160000 : ℝ) ≤ (KK i : ℝ) := by exact_mod_cast h
    linarith
  have hsmall : (2 : ℝ) / (KK i : ℝ) ^ 6 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hKR 6]
  have hnn : (0 : ℝ) ≤ 2 / (KK i : ℝ) ^ 6 := by positivity
  have hpow : (2 / (KK i : ℝ) ^ 6) ^ KK i ≤ (1 / 2 : ℝ) ^ KK i := pow_le_pow_left₀ hnn hsmall _
  have hmono : (1 / 2 : ℝ) ^ KK i ≤ (1 / 2 : ℝ) ^ i := by
    refine pow_le_pow_of_le_one (by norm_num) (by norm_num) ?_
    unfold KK kk
    omega
  have hL : (0 : ℝ) ≤ (L : ℝ) := by positivity
  nlinarith [hpow.trans hmono, hL]

open Classical in
/-- **The tail of the scales contributes at most `2^{−I}/8` of any range.** -/
theorem card_tail_le (I L : ℕ) :
    (((Finset.range L).filter (fun q => ∃ i, I < i ∧ q ∈ sampledPosAt i)).card : ℝ)
      ≤ (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ I * (L : ℝ) := by
  classical
  obtain ⟨J, hJ⟩ := exists_cover_tail I L
  have hcard := le_trans (Finset.card_le_card hJ) (Finset.card_biUnion_le
    (s := Finset.Ico (I + 1) (J + 1))
    (t := fun i => (sampledPosAt i).filter (fun j => j < L)))
  have hcardR : (((Finset.range L).filter
      (fun q => ∃ i, I < i ∧ q ∈ sampledPosAt i)).card : ℝ)
      ≤ ∑ i ∈ Finset.Ico (I + 1) (J + 1),
          (((sampledPosAt i).filter (fun j => j < L)).card : ℝ) := by
    exact_mod_cast hcard
  refine hcardR.trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => density_geom i L) ?_
  rcases Nat.lt_or_ge J I with hIJ | hIJ
  · rw [Finset.Ico_eq_empty (by omega)]
    simp
  · rw [Finset.sum_Ico_eq_sum_range]
    have hrw : ∀ k ∈ Finset.range (J + 1 - (I + 1)),
        (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ (I + 1 + k) * (L : ℝ)
          = ((1 / 8 : ℝ) * (1 / 2 : ℝ) ^ (I + 1) * (L : ℝ)) * (1 / 2 : ℝ) ^ k := by
      intro k _
      rw [pow_add]
      ring
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
    have hgeom : ∑ k ∈ Finset.range (J + 1 - (I + 1)), (1 / 2 : ℝ) ^ k ≤ 2 :=
      sum_geometric_two_le _
    have hpos : (0 : ℝ) ≤ (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ (I + 1) * (L : ℝ) := by positivity
    calc ((1 / 8 : ℝ) * (1 / 2 : ℝ) ^ (I + 1) * (L : ℝ))
            * ∑ k ∈ Finset.range (J + 1 - (I + 1)), (1 / 2 : ℝ) ^ k
        ≤ ((1 / 8 : ℝ) * (1 / 2 : ℝ) ^ (I + 1) * (L : ℝ)) * 2 :=
          mul_le_mul_of_nonneg_left hgeom hpos
      _ = (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ I * (L : ℝ) := by
          rw [pow_succ]; ring

open Classical in
/-- **The sampled set has density zero.**  Each scale's own set of sampled positions is finite,
and the scales beyond `I` together occupy at most a `2^{−I}/8` fraction — so the union occupies
an asymptotically vanishing fraction of `[0, L)`.

This is the sharp non-vacuity of `isDisjunctive_enumReal`: `sampleEnum` skips *almost every*
digit of `G₄`. -/
theorem tendsto_density_isSampled :
    Tendsto (fun L => (((Finset.range L).filter IsSampled).card : ℝ) / (L : ℝ))
      atTop (nhds 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- pick a scale cutoff making the tail smaller than ε/2
  obtain ⟨I, hI⟩ : ∃ I : ℕ, (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ I < ε / 2 := by
    obtain ⟨I, hI⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < ε / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨I, by nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) I]⟩
  -- the head is a fixed finite set
  set C : ℕ := ((Finset.range (I + 1)).biUnion sampledPosAt).card with hC
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℕ, 0 < L₀ ∧ (C : ℝ) / (L₀ : ℝ) < ε / 2 := by
    obtain ⟨L₀, hL₀⟩ := exists_nat_gt (max 1 ((C : ℝ) / (ε / 2)))
    refine ⟨L₀, ?_, ?_⟩
    · have : (1 : ℝ) ≤ max 1 ((C : ℝ) / (ε / 2)) := le_max_left _ _
      have : (1 : ℝ) < (L₀ : ℝ) := lt_of_le_of_lt this hL₀
      exact_mod_cast lt_trans (by norm_num : (0:ℝ) < 1) this
    · have h1 : (C : ℝ) / (ε / 2) < (L₀ : ℝ) := lt_of_le_of_lt (le_max_right _ _) hL₀
      have hL : (0 : ℝ) < (L₀ : ℝ) := by
        have : (1 : ℝ) ≤ max 1 ((C : ℝ) / (ε / 2)) := le_max_left _ _
        linarith [lt_of_le_of_lt this hL₀]
      rw [div_lt_iff₀ hL]
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < ε / 2)] at h1
      linarith
  refine ⟨L₀, fun L hL => ?_⟩
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := lt_of_lt_of_le hL₀.1 hL
    exact_mod_cast this
  have hL₀pos : (0 : ℝ) < (L₀ : ℝ) := by exact_mod_cast hL₀.1
  -- split the sampled positions below `L` into head scales and tail scales
  have hsplit : ((Finset.range L).filter IsSampled).card
      ≤ C + ((Finset.range L).filter (fun q => ∃ i, I < i ∧ q ∈ sampledPosAt i)).card := by
    have hsub : (Finset.range L).filter IsSampled
        ⊆ ((Finset.range (I + 1)).biUnion sampledPosAt)
          ∪ (Finset.range L).filter (fun q => ∃ i, I < i ∧ q ∈ sampledPosAt i) := by
      intro q hq
      obtain ⟨i, hi⟩ := (Finset.mem_filter.1 hq).2
      rcases Nat.lt_or_ge I i with hiI | hiI
      · exact Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hq).1, ⟨i, hiI, hi⟩⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 (by omega), hi⟩)
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  have hsplitR : (((Finset.range L).filter IsSampled).card : ℝ)
      ≤ (C : ℝ) + (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ I * (L : ℝ) := by
    have h1 : (((Finset.range L).filter IsSampled).card : ℝ)
        ≤ (C : ℝ) + (((Finset.range L).filter
          (fun q => ∃ i, I < i ∧ q ∈ sampledPosAt i)).card : ℝ) := by exact_mod_cast hsplit
    linarith [card_tail_le I L]
  have hCL : (C : ℝ) / (L : ℝ) < ε / 2 := by
    refine lt_of_le_of_lt ?_ hL₀.2
    have hLL : (L₀ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    exact div_le_div_of_nonneg_left (by positivity) hL₀pos hLL
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  calc (((Finset.range L).filter IsSampled).card : ℝ) / (L : ℝ)
      ≤ ((C : ℝ) + (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ I * (L : ℝ)) / (L : ℝ) := by
        exact div_le_div_of_nonneg_right hsplitR hLpos.le
    _ = (C : ℝ) / (L : ℝ) + (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ I := by
        field_simp
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end NormalNumbers.G4.Sched
