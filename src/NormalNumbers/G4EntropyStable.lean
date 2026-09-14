/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyDensityOne
import NormalNumbers.Stoneham

/-!
# Normality is stable under density-zero digit changes — the barrier is sharp

`G4EntropyDensityOne` proved that a satisfiable digit-local hypothesis can force binary
normality only if the positions it reads have density `1`.  This module proves the converse
half, which shows that threshold is exactly right:

> **`isNormal_congr_of_density_zero`**: if the binary digits of `x` and `y` agree off a set `D`
> of density `0`, then `x` is normal iff `y` is.

Consequently, for *every* position set `S` whose complement has density `0`, the property
`P x := IsNormal 2 x` is `S`-local (`isNormal_local_of_density_one`) — and it trivially forces
normality.  So `density = 1` is not an artifact of the proof in `G4EntropyDensityOne`: it is
attained, and the barrier's constant cannot be improved.

The estimate is the window count: changing the digit at one position changes the number of
occurrences of a length-`ℓ` word by at most `ℓ`, so

  `|#occ w in x's first n digits − #occ w in y's first n digits| ≤ ℓ · |D ∩ [0,n)|`,

and dividing by `n` kills the difference.  The injection `i ↦ (least j < ℓ with D(i+j), i+j)`
into `[0,ℓ) × (D ∩ [0,n))` is what bounds the exceptional window count.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

open NormalNumbers

variable {D : ℕ → Prop} [DecidablePred D]

/-- The window positions that a digit change can disturb: those with a changed digit inside the
window `[i, i+ℓ)`, the window itself lying below `n`. -/
def BadWin (D : ℕ → Prop) (ℓ n : ℕ) (i : ℕ) : Prop := ∃ j, j < ℓ ∧ i + j < n ∧ D (i + j)

noncomputable instance (D : ℕ → Prop) [DecidablePred D] (ℓ n : ℕ) :
    DecidablePred (BadWin D ℓ n) := Classical.decPred _

/-- The least disturbed offset inside the window at `i` (junk `0` if there is none). -/
noncomputable def badIdx (D : ℕ → Prop) [DecidablePred D] (ℓ n i : ℕ) : ℕ :=
  if h : BadWin D ℓ n i then Nat.find h else 0

lemma badIdx_spec {ℓ n i : ℕ} (h : BadWin D ℓ n i) :
    badIdx D ℓ n i < ℓ ∧ i + badIdx D ℓ n i < n ∧ D (i + badIdx D ℓ n i) := by
  unfold badIdx
  rw [dif_pos h]
  exact Nat.find_spec h

/-- **At most `ℓ` disturbed windows per changed digit.** -/
lemma card_badWin_le (ℓ n N : ℕ) :
    ((Finset.range N).filter (BadWin D ℓ n)).card
      ≤ ℓ * ((Finset.range n).filter D).card := by
  classical
  have hcard : (((Finset.range ℓ) ×ˢ ((Finset.range n).filter D)).card)
      = ℓ * ((Finset.range n).filter D).card := by
    rw [Finset.card_product, Finset.card_range]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun i => (badIdx D ℓ n i, i + badIdx D ℓ n i)) ?_ ?_
  · intro i hi
    have hi' := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
    obtain ⟨h1, h2, h3⟩ := badIdx_spec hi'.2
    exact Finset.mem_product.2 ⟨Finset.mem_range.2 h1,
      Finset.mem_filter.2 ⟨Finset.mem_range.2 h2, h3⟩⟩
  · intro i hi i' hi' heq
    have h1 : badIdx D ℓ n i = badIdx D ℓ n i' := congrArg Prod.fst heq
    have h2 : i + badIdx D ℓ n i = i' + badIdx D ℓ n i' := congrArg Prod.snd heq
    omega


/-! ### The window count moves by at most `ℓ` per changed digit -/

variable {sx sy : ℕ → ℕ}

lemma countOcc_le_add (hagree : ∀ j, ¬ D j → sx j = sy j) (w : List ℕ) (n : ℕ) :
    countOccurrences w ((List.range n).map sx)
      ≤ countOccurrences w ((List.range n).map sy)
        + w.length * ((Finset.range n).filter D).card := by
  classical
  rw [countOccurrences_range_map, countOccurrences_range_map]
  have hsub : (Finset.range (n + 1)).filter (fun i => i + w.length ≤ n ∧ MatchesAt sx w i)
      ⊆ ((Finset.range (n + 1)).filter (fun i => i + w.length ≤ n ∧ MatchesAt sy w i))
        ∪ ((Finset.range (n + 1)).filter (BadWin D w.length n)) := by
    intro i hi
    obtain ⟨hr, hfit, hm⟩ := Finset.mem_filter.1 hi
    by_cases hy : MatchesAt sy w i
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hr, hfit, hy⟩)
    · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hr, ?_⟩)
      unfold MatchesAt at hy
      push_neg at hy
      obtain ⟨j, hj, hne⟩ := hy
      refine ⟨j, hj, by omega, ?_⟩
      by_contra hD
      exact hne (by rw [← hagree _ hD]; exact hm j hj)
  calc ((Finset.range (n + 1)).filter (fun i => i + w.length ≤ n ∧ MatchesAt sx w i)).card
      ≤ (((Finset.range (n + 1)).filter (fun i => i + w.length ≤ n ∧ MatchesAt sy w i))
          ∪ ((Finset.range (n + 1)).filter (BadWin D w.length n))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.range (n + 1)).filter (fun i => i + w.length ≤ n ∧ MatchesAt sy w i)).card
          + ((Finset.range (n + 1)).filter (BadWin D w.length n)).card :=
        Finset.card_union_le _ _
    _ ≤ ((Finset.range (n + 1)).filter (fun i => i + w.length ≤ n ∧ MatchesAt sy w i)).card
          + w.length * ((Finset.range n).filter D).card := by
        gcongr
        exact card_badWin_le _ _ _

/-! ### Normality is stable -/

/-- **Normality of a digit sequence is unchanged by a density-zero set of digit changes.** -/
theorem isNormalSequence_congr_of_density_zero {b : ℕ}
    (hD : Tendsto (fun L => ((((Finset.range L).filter D).card : ℝ)) / L) atTop (nhds 0))
    (hagree : ∀ j, ¬ D j → sx j = sy j) (h : IsNormalSequence b sx) : IsNormalSequence b sy := by
  intro w hw hdig
  have hx := h w hw hdig
  have hagree' : ∀ j, ¬ D j → sy j = sx j := fun j hj => (hagree j hj).symm
  have hdiff : Tendsto (fun n => ((countOccurrences w ((List.range n).map sy) : ℝ)) / n
      - ((countOccurrences w ((List.range n).map sx) : ℝ)) / n) atTop (nhds 0) := by
    have hgt : Tendsto (fun n : ℕ =>
        (w.length : ℝ) * (((((Finset.range n).filter D).card : ℝ)) / n)) atTop (nhds 0) := by
      have := hD.const_mul (w.length : ℝ)
      simpa using this
    refine squeeze_zero_norm (fun n => ?_) hgt
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have h1 : ((countOccurrences w ((List.range n).map sx) : ℝ))
            ≤ ((countOccurrences w ((List.range n).map sy) : ℝ))
              + (w.length : ℝ) * ((((Finset.range n).filter D).card : ℝ)) := by
          exact_mod_cast countOcc_le_add hagree w n
        have h2 : ((countOccurrences w ((List.range n).map sy) : ℝ))
            ≤ ((countOccurrences w ((List.range n).map sx) : ℝ))
              + (w.length : ℝ) * ((((Finset.range n).filter D).card : ℝ)) := by
          exact_mod_cast countOcc_le_add hagree' w n
        have key : |((countOccurrences w ((List.range n).map sy) : ℝ))
            - ((countOccurrences w ((List.range n).map sx) : ℝ))|
            ≤ (w.length : ℝ) * ((((Finset.range n).filter D).card : ℝ)) :=
          abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
        calc ‖((countOccurrences w ((List.range n).map sy) : ℝ)) / n
              - ((countOccurrences w ((List.range n).map sx) : ℝ)) / n‖
            = |((countOccurrences w ((List.range n).map sy) : ℝ))
                - ((countOccurrences w ((List.range n).map sx) : ℝ))| / n := by
              rw [div_sub_div_same, Real.norm_eq_abs, abs_div, abs_of_pos hnR]
          _ ≤ ((w.length : ℝ) * ((((Finset.range n).filter D).card : ℝ))) / n := by gcongr
          _ = (w.length : ℝ) * (((((Finset.range n).filter D).card : ℝ)) / n) := by ring
  have hsum := hx.add hdiff
  rw [add_zero] at hsum
  refine hsum.congr fun n => ?_
  ring

/-- **Normality of a real is unchanged by a density-zero set of digit changes.** -/
theorem isNormal_congr_of_density_zero {x y : ℝ}
    (hD : Tendsto (fun L => ((((Finset.range L).filter D).card : ℝ)) / L) atTop (nhds 0))
    (hagree : ∀ j, ¬ D j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j)
    (hx : IsNormal 2 x) : IsNormal 2 y :=
  isNormalSequence_congr_of_density_zero hD hagree hx

/-! ### The barrier's constant is attained -/

/-- **Sharpness.**  For every position set `S` whose complement has density `0`, binary
normality *is* an `S`-local property, in exactly the sense `G4EntropyDensityOne` uses.  So the
threshold `density = 1` in `tendsto_density_one_of_forces_normal` cannot be lowered: at density
one there is a digit-local property that forces normality (namely normality itself), and below
density one there is none. -/
theorem isNormal_local_of_density_one {S : ℕ → Prop} [DecidablePred S]
    (hS : Tendsto (fun L => ((allComp S L : ℝ)) / L) atTop (nhds 0)) :
    ∀ x y : ℝ, (∀ j, S j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) →
      IsNormal 2 x → IsNormal 2 y := by
  intro x y hd hx
  exact isNormal_congr_of_density_zero (D := fun j => ¬ S j) hS
    (fun j hj => hd j (not_not.1 hj)) hx


/-- The complement of a density-one set has density zero. -/
lemma tendsto_compl_zero_of_density_one {S : ℕ → Prop} [DecidablePred S]
    (h : Tendsto (fun L => ((((Finset.range L).filter S).card : ℝ)) / L) atTop (nhds 1)) :
    Tendsto (fun L => ((allComp S L : ℝ)) / L) atTop (nhds 0) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  have hsub := hone.sub h
  rw [sub_self] at hsub
  refine hsub.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with L hL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hc : ((allComp S L : ℝ)) + ((((Finset.range L).filter S).card : ℝ)) = (L : ℝ) := by
    exact_mod_cast allComp_add_card (S := S) L
  field_simp
  linarith

/-- **The locality barrier is an exact characterization.**  Given that a binary normal number
exists in `[0,1)`, the position sets `S` that carry a satisfiable `S`-local hypothesis implying
binary normality are *precisely* the sets of density one.

Forward is `tendsto_density_one_of_forces_normal`; backward is normality itself, which is
`S`-local as soon as `Sᶜ` has density zero. -/
theorem exists_digitLocal_forces_normal_iff {S : ℕ → Prop} [DecidablePred S]
    (hz : ∃ z : ℝ, 0 ≤ z ∧ z < 1 ∧ IsNormal 2 z) :
    (∃ P : ℝ → Prop,
        (∀ x y : ℝ, (∀ j, S j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) →
          P x → P y)
        ∧ (∃ x : ℝ, P x)
        ∧ (∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y))
      ↔ Tendsto (fun L => ((((Finset.range L).filter S).card : ℝ)) / L) atTop (nhds 1) := by
  constructor
  · rintro ⟨P, hloc, ⟨x, hx⟩, hforce⟩
    exact tendsto_density_one_of_forces_normal hloc hx hforce
  · intro hdens
    obtain ⟨z, hz0, hz1, hzn⟩ := hz
    exact ⟨fun x => IsNormal 2 x,
      isNormal_local_of_density_one (tendsto_compl_zero_of_density_one hdens),
      ⟨z, hzn⟩, fun y _ _ hy => hy⟩

/-- The hypothesis of `exists_digitLocal_forces_normal_iff` is discharged by Stoneham's
number `α₂,₃`, proved binary normal in `Stoneham.lean`. -/
theorem exists_isNormal_mem_Ico : ∃ z : ℝ, 0 ≤ z ∧ z < 1 ∧ IsNormal 2 z :=
  ⟨stoneham23, stoneham23_mem_Ico.1, stoneham23_mem_Ico.2, isNormal_two_stoneham23⟩

/-- **The characterization, unconditionally.**  The position sets `S` for which some satisfiable
`S`-local hypothesis implies binary normality are exactly the sets of density one. -/
theorem forces_normal_iff_density_one {S : ℕ → Prop} [DecidablePred S] :
    (∃ P : ℝ → Prop,
        (∀ x y : ℝ, (∀ j, S j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) →
          P x → P y)
        ∧ (∃ x : ℝ, P x)
        ∧ (∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y))
      ↔ Tendsto (fun L => ((((Finset.range L).filter S).card : ℝ)) / L) atTop (nhds 1) :=
  exists_digitLocal_forces_normal_iff exists_isNormal_mem_Ico

end NormalNumbers.G4Entropy


