/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CFLimit

/-!
# W5 — the construction schedule (B–Y §2.1)

This file iterates the refinement lemma (`TBrick.exists_refinement_uniform`)
and the level step (`TBrick.exists_extend_succ`) into the B–Y brick sequence:

* `wordFamily t` — the finite family of CF patterns active at level `t`
  (length and digits in `[1, t]`);
* `schedEps t = 1/(t+1)` — the level-`t` accuracy (both `δ` and `ε`);
* choice-extracted level constants: `kminFn t` (block-length floor), `NFn t`
  (order threshold), and the canonical stage length `nFn t ≥ max (NFn t) (t²+1)`
  — **uniform over bricks** thanks to the uniform refinement lemma, so the
  stage length is constant within a level epoch;
* the state `SchedState` (level + brick), the promotion rule
  `promThreshold (t+1) ≤ |w|` (promote only once the accumulated word
  dominates the next level's stage length — B–Y's "slow `t`" constraint),
  the step relation `SchedStep` packaging every Lemma-13 payload, and the
  schedule `sched : ℕ → SchedState` built by choice from `schedStep_exists`.

The correctness chains (§2.2) consume only `sched_step`/`sched_zero` plus the
recorded payloads.
-/

namespace NormalNumbers

open MeasureTheory

/-! ## The active pattern family -/

/-- The genuine CF words of length exactly `l` with digits in `[1, t]`. -/
def boundedWords (t l : ℕ) : Finset (List ℕ) :=
  (Fintype.piFinset (fun _ : Fin l => Finset.Icc 1 t)).image List.ofFn

theorem mem_boundedWords {t l : ℕ} {v : List ℕ} :
    v ∈ boundedWords t l ↔ v.length = l ∧ ∀ a ∈ v, 1 ≤ a ∧ a ≤ t := by
  constructor
  · intro hv
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hv
    rw [Fintype.mem_piFinset] at hf
    refine ⟨List.length_ofFn, fun a ha => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    exact Finset.mem_Icc.1 (hf i)
  · rintro ⟨rfl, hv⟩
    refine Finset.mem_image.2 ⟨fun i => v.get i, ?_, List.ofFn_get v⟩
    rw [Fintype.mem_piFinset]
    exact fun i => Finset.mem_Icc.2 (hv _ (v.get_mem i))

/-- The patterns active at level `t`: genuine words with length and digits
in `[1, t]`. -/
def wordFamily (t : ℕ) : Finset (List ℕ) :=
  (Finset.Icc 1 t).biUnion (boundedWords t)

theorem mem_wordFamily {t : ℕ} {v : List ℕ} :
    v ∈ wordFamily t ↔
      (1 ≤ v.length ∧ v.length ≤ t) ∧ ∀ a ∈ v, 1 ≤ a ∧ a ≤ t := by
  constructor
  · intro hv
    obtain ⟨l, hl, hvl⟩ := Finset.mem_biUnion.1 hv
    obtain ⟨rfl, hd⟩ := mem_boundedWords.1 hvl
    exact ⟨Finset.mem_Icc.1 hl, hd⟩
  · rintro ⟨⟨h1, h2⟩, hd⟩
    exact Finset.mem_biUnion.2 ⟨v.length, Finset.mem_Icc.2 ⟨h1, h2⟩,
      mem_boundedWords.2 ⟨rfl, hd⟩⟩

theorem wordFamily_pos (t : ℕ) : ∀ v ∈ wordFamily t, ∀ a ∈ v, 1 ≤ a :=
  fun v hv a ha => ((mem_wordFamily.1 hv).2 a ha).1

theorem wordFamily_ne (t : ℕ) : ∀ v ∈ wordFamily t, v ≠ [] := by
  intro v hv h
  have := (mem_wordFamily.1 hv).1.1
  rw [h] at this
  simp at this

/-- The family grows with the level. -/
theorem wordFamily_mono {t t' : ℕ} (h : t ≤ t') :
    wordFamily t ⊆ wordFamily t' := by
  intro v hv
  obtain ⟨⟨h1, h2⟩, hd⟩ := mem_wordFamily.1 hv
  exact mem_wordFamily.2 ⟨⟨h1, le_trans h2 h⟩,
    fun a ha => ⟨(hd a ha).1, le_trans (hd a ha).2 h⟩⟩

/-! ## Level parameters and choice constants -/

/-- The level-`t` accuracy, used for both `δ` and `ε`: `1/(t+1)`. -/
noncomputable def schedEps (t : ℕ) : ℝ := 1 / (t + 1)

theorem schedEps_pos (t : ℕ) : 0 < schedEps t := by
  have : (0 : ℝ) < t + 1 := by positivity
  exact div_pos one_pos this

theorem mul_schedEps_le (t : ℕ) : (t : ℝ) * schedEps t ≤ 1 := by
  rw [schedEps, mul_one_div, div_le_one (by positivity)]
  linarith

theorem schedEps_le {t t' : ℕ} (h : t ≤ t') : schedEps t' ≤ schedEps t := by
  apply div_le_div_of_nonneg_left one_pos.le (by positivity)
  have : (t : ℝ) ≤ t' := by exact_mod_cast h
  linarith

/-- The global good-length constant (from `half_mass_long_extensions`). -/
noncomputable def goodC : ℝ := exists_C_half_le_volume_goodExtSet.choose

theorem goodC_pos : 0 < goodC :=
  exists_C_half_le_volume_goodExtSet.choose_spec.1

theorem goodC_half : ∀ (w : List ℕ), w ≠ [] → (∀ a ∈ w, 1 ≤ a) → ∀ n : ℕ,
    volume (cfCylinder w) ≤ 2 * volume (goodExtSet w goodC n) :=
  exists_C_half_le_volume_goodExtSet.choose_spec.2

/-- The uniform refinement lemma, instantiated at the canonical level-`t`
parameters (`F = wordFamily t`, `δ = ε = schedEps t`, `C = goodC`). -/
theorem sched_refinement (t : ℕ) :
    ∃ kmin₀ : ℕ, ∀ kmin, kmin₀ ≤ kmin → ∃ N : ℕ,
      ∀ (B : TBrick t) (n : ℕ), N ≤ n → 0 < n →
      ∃ (B' : TBrick t) (u : List ℕ),
        B'.w = B.w ++ u ∧ u.length = n ∧ (∀ a ∈ u, 1 ≤ a) ∧
        (cfK u : ℝ) ≤ Real.exp (goodC * n) ∧
        (∀ v ∈ wordFamily t, |(countOccurrences v u : ℝ)
          - (gaussMeasure (cfCylinder v)).toReal * n|
            < schedEps t * n + v.length) ∧
        (∀ d, 2 ≤ d → d ≤ t → B.m d + kmin ≤ B'.m d) ∧
        (∀ d, 2 ≤ d → d ≤ t → ∀ y ∈ cfCylinder B'.w,
          ∃ i : ℕ, i < 2 ∧ y ∈ daryCell d (B.m d) (B.j d + i) 1 ∧
            ∃ β : Fin (B'.m d - B.m d) → Fin d,
              β ∉ badBlocks d (B'.m d - B.m d) (schedEps t) ∧
              y ∈ daryCell d (B.m d + (B'.m d - B.m d))
                ((B.j d + i) * d ^ (B'.m d - B.m d)
                  + blockNatVal d (List.ofFn fun l => (β l : ℕ))) 1) :=
  TBrick.exists_refinement_uniform t (wordFamily t) (wordFamily_pos t)
    (wordFamily_ne t) (schedEps_pos t) (schedEps_pos t)
    (mul_schedEps_le t) goodC_half

/-- The level-`t` block-length floor (`≥ 1`). -/
noncomputable def kminFn (t : ℕ) : ℕ := max (sched_refinement t).choose 1

theorem one_le_kminFn (t : ℕ) : 1 ≤ kminFn t := le_max_right _ _

theorem kminFn_spec (t : ℕ) : ∃ N : ℕ,
    ∀ (B : TBrick t) (n : ℕ), N ≤ n → 0 < n →
    ∃ (B' : TBrick t) (u : List ℕ),
      B'.w = B.w ++ u ∧ u.length = n ∧ (∀ a ∈ u, 1 ≤ a) ∧
      (cfK u : ℝ) ≤ Real.exp (goodC * n) ∧
      (∀ v ∈ wordFamily t, |(countOccurrences v u : ℝ)
        - (gaussMeasure (cfCylinder v)).toReal * n|
          < schedEps t * n + v.length) ∧
      (∀ d, 2 ≤ d → d ≤ t → B.m d + kminFn t ≤ B'.m d) ∧
      (∀ d, 2 ≤ d → d ≤ t → ∀ y ∈ cfCylinder B'.w,
        ∃ i : ℕ, i < 2 ∧ y ∈ daryCell d (B.m d) (B.j d + i) 1 ∧
          ∃ β : Fin (B'.m d - B.m d) → Fin d,
            β ∉ badBlocks d (B'.m d - B.m d) (schedEps t) ∧
            y ∈ daryCell d (B.m d + (B'.m d - B.m d))
              ((B.j d + i) * d ^ (B'.m d - B.m d)
                + blockNatVal d (List.ofFn fun l => (β l : ℕ))) 1) :=
  (sched_refinement t).choose_spec (kminFn t) (le_max_left _ _)

/-- The canonical level-`t` stage length: at least the refinement threshold
and at least `t² + 1` (the latter feeds the §2.2 margin arithmetic). -/
noncomputable def nFn (t : ℕ) : ℕ := max (kminFn_spec t).choose (t * t + 1)

theorem nFn_pos (t : ℕ) : 0 < nFn t :=
  lt_of_lt_of_le (Nat.succ_pos _) (le_max_right _ _)

theorem sq_lt_nFn (t : ℕ) : t * t < nFn t :=
  lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)

/-- The per-stage refinement at the canonical parameters: every level-`t`
brick refines by a genuine word of length exactly `nFn t` carrying all
Lemma-13 payloads. -/
theorem nFn_spec (t : ℕ) (B : TBrick t) :
    ∃ (B' : TBrick t) (u : List ℕ),
      B'.w = B.w ++ u ∧ u.length = nFn t ∧ (∀ a ∈ u, 1 ≤ a) ∧
      (cfK u : ℝ) ≤ Real.exp (goodC * nFn t) ∧
      (∀ v ∈ wordFamily t, |(countOccurrences v u : ℝ)
        - (gaussMeasure (cfCylinder v)).toReal * nFn t|
          < schedEps t * nFn t + v.length) ∧
      (∀ d, 2 ≤ d → d ≤ t → B.m d + kminFn t ≤ B'.m d) ∧
      (∀ d, 2 ≤ d → d ≤ t → ∀ y ∈ cfCylinder B'.w,
        ∃ i : ℕ, i < 2 ∧ y ∈ daryCell d (B.m d) (B.j d + i) 1 ∧
          ∃ β : Fin (B'.m d - B.m d) → Fin d,
            β ∉ badBlocks d (B'.m d - B.m d) (schedEps t) ∧
            y ∈ daryCell d (B.m d + (B'.m d - B.m d))
              ((B.j d + i) * d ^ (B'.m d - B.m d)
                + blockNatVal d (List.ofFn fun l => (β l : ℕ))) 1) :=
  (kminFn_spec t).choose_spec B (nFn t) (le_max_left _ _) (nFn_pos t)

/-! ## The schedule -/

/-- The word-length threshold gating promotion INTO level `t`: the
accumulated word must dominate `t` stages of the new level. -/
noncomputable def promThreshold (t : ℕ) : ℕ := t * nFn t

/-- The schedule state: current level and current brick. -/
structure SchedState where
  /-- The current level (`bases 2..t` are active). -/
  t : ℕ
  /-- The current brick. -/
  B : TBrick t

/-- One step of the B–Y schedule (promotion decision + refinement), with
every Lemma-13 payload recorded.  `u` is the appended CF word; `(m₁, j₁, r₁)`
are the cell data of the intermediate brick (post-promotion, pre-refinement):
they agree with `S`'s brick on the old bases and provide the start cell for a
newly adjoined base. -/
def SchedStep (S S' : SchedState) : Prop :=
  ∃ (u : List ℕ) (m₁ : ℕ → ℕ) (j₁ : ℕ → ℤ) (r₁ : ℕ → ℕ),
    S'.t = (if promThreshold (S.t + 1) ≤ S.B.w.length
      then S.t + 1 else S.t) ∧
    S'.B.w = S.B.w ++ u ∧
    u.length = nFn S'.t ∧ (∀ a ∈ u, 1 ≤ a) ∧
    (∀ d, 2 ≤ d → d ≤ S.t → m₁ d = S.B.m d ∧ j₁ d = S.B.j d) ∧
    (∀ d, 2 ≤ d → d ≤ S'.t → 1 ≤ r₁ d ∧ r₁ d ≤ 2 ∧
      cfCylinder S.B.w ⊆ daryCell d (m₁ d) (j₁ d) (r₁ d)) ∧
    (cfK u : ℝ) ≤ Real.exp (goodC * nFn S'.t) ∧
    (∀ v ∈ wordFamily S'.t, |(countOccurrences v u : ℝ)
      - (gaussMeasure (cfCylinder v)).toReal * nFn S'.t|
        < schedEps S'.t * nFn S'.t + v.length) ∧
    (∀ d, 2 ≤ d → d ≤ S'.t → m₁ d + kminFn S'.t ≤ S'.B.m d) ∧
    (∀ d, 2 ≤ d → d ≤ S'.t → ∀ y ∈ cfCylinder S'.B.w,
      ∃ i : ℕ, i < 2 ∧ y ∈ daryCell d (m₁ d) (j₁ d + i) 1 ∧
        ∃ β : Fin (S'.B.m d - m₁ d) → Fin d,
          β ∉ badBlocks d (S'.B.m d - m₁ d) (schedEps S'.t) ∧
          y ∈ daryCell d (m₁ d + (S'.B.m d - m₁ d))
            ((j₁ d + i) * d ^ (S'.B.m d - m₁ d)
              + blockNatVal d (List.ofFn fun l => (β l : ℕ))) 1)

/-- Every state steps: promote if the threshold is met, then refine at the
(possibly new) level. -/
theorem schedStep_exists (S : SchedState) : ∃ S', SchedStep S S' := by
  by_cases hprom : promThreshold (S.t + 1) ≤ S.B.w.length
  · -- promotion: adjoin base `S.t + 1`, then refine at level `S.t + 1`
    obtain ⟨B₁, hB₁w, hB₁pres⟩ := TBrick.exists_extend_succ S.B
    obtain ⟨B', u, h1, h2, h3, h4, h5, h6, h7⟩ := nFn_spec (S.t + 1) B₁
    refine ⟨⟨S.t + 1, B'⟩, u, B₁.m, B₁.j, B₁.r,
      by simp [hprom], by rw [h1, hB₁w], h2, h3, ?_, ?_, h4, h5, h6, ?_⟩
    · intro d hd2 hdt
      obtain ⟨hm, hj, -⟩ := hB₁pres d hd2 hdt
      exact ⟨hm, hj⟩
    · intro d hd2 hdt
      refine ⟨B₁.hr1 d hd2 hdt, B₁.hr2 d hd2 hdt, ?_⟩
      rw [← hB₁w]
      exact B₁.hsub d hd2 hdt
    · exact h7
  · -- no promotion: refine at the current level
    obtain ⟨B', u, h1, h2, h3, h4, h5, h6, h7⟩ := nFn_spec S.t S.B
    refine ⟨⟨S.t, B'⟩, u, S.B.m, S.B.j, S.B.r,
      by simp [hprom], h1, h2, h3, fun d _ _ => ⟨rfl, rfl⟩, ?_, h4, h5, h6, h7⟩
    intro d hd2 hdt
    exact ⟨S.B.hr1 d hd2 hdt, S.B.hr2 d hd2 hdt, S.B.hsub d hd2 hdt⟩

/-- The seed word: `promThreshold 2` ones (long enough that the promotion
invariant `promThreshold t ≤ |w|` holds from the start). -/
noncomputable def seedWord : List ℕ := List.replicate (promThreshold 2) 1

theorem seedWord_ne : seedWord ≠ [] := by
  have h2 : 0 < promThreshold 2 :=
    Nat.mul_pos (by norm_num) (nFn_pos 2)
  rw [seedWord, ← List.length_pos_iff_ne_nil, List.length_replicate]
  exact h2

theorem seedWord_pos : ∀ a ∈ seedWord, 1 ≤ a := by
  intro a ha
  simp only [seedWord] at ha
  rw [List.eq_of_mem_replicate ha]

theorem seedWord_length : seedWord.length = promThreshold 2 := by
  simp [seedWord]

/-- The seed state: a 2-brick on the seed word. -/
noncomputable def seedState : SchedState :=
  ⟨2, (exists_seed_brick seedWord seedWord_ne seedWord_pos).choose⟩

theorem seedState_w : seedState.B.w = seedWord :=
  (exists_seed_brick seedWord seedWord_ne seedWord_pos).choose_spec

theorem seedState_t : seedState.t = 2 := rfl

/-- **The B–Y schedule**: the brick sequence of §2.1. -/
noncomputable def sched : ℕ → SchedState
  | 0 => seedState
  | s + 1 => (schedStep_exists (sched s)).choose

theorem sched_zero : sched 0 = seedState := rfl

theorem sched_step (s : ℕ) : SchedStep (sched s) (sched (s + 1)) :=
  (schedStep_exists (sched s)).choose_spec

/-! ## First consequences -/

/-- The schedule's words strictly extend (feeds
`exists_irrational_mem_iInter_cfCylinder`). -/
theorem sched_word_extends (s : ℕ) :
    ∃ u, u ≠ [] ∧ (sched (s + 1)).B.w = (sched s).B.w ++ u := by
  obtain ⟨u, -, -, -, -, hw, hlen, -⟩ := sched_step s
  refine ⟨u, fun h => ?_, hw⟩
  rw [h] at hlen
  simp at hlen
  exact absurd hlen.symm (nFn_pos _).ne'

/-- The schedule's level is nondecreasing, moving by `0` or `1` each step. -/
theorem sched_t_step (s : ℕ) :
    (sched (s + 1)).t = (sched s).t ∨
      (sched (s + 1)).t = (sched s).t + 1 := by
  obtain ⟨u, -, -, -, ht, -⟩ := sched_step s
  by_cases h : promThreshold ((sched s).t + 1) ≤ (sched s).B.w.length
  · right; rw [ht, if_pos h]
  · left; rw [ht, if_neg h]

theorem sched_t_mono : Monotone fun s => (sched s).t := by
  apply monotone_nat_of_le_succ
  intro s
  rcases sched_t_step s with h | h <;> omega

end NormalNumbers
