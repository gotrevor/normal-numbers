/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.G4EntropyBarrier

/-!
# The locality barrier at full strength: a digit-local hypothesis must read density ONE

Lap 9 (`G4EntropyBarrier`) proved that a satisfiable `S`-local hypothesis can imply binary
normality only if `S` has upper density `≥ 1/2`: the *mask* (the digits of `x` on `S`, `0`
elsewhere) satisfies the hypothesis and has at most `dens S` ones.

That is not the end of the argument.  A digit-local hypothesis is insensitive to **every**
filling off `S`, not just the zero filling, and comparing two fillings removes the factor `1/2`
entirely:

* the zero filling `y₀` has ones `= ones(x) ∩ S`;
* the filling `y₁` that puts a `1` at every *even-indexed* position of `Sᶜ` has ones
  `= (ones(x) ∩ S) ⊔ (even-indexed part of Sᶜ)`.

Both satisfy the hypothesis, so both must be normal, so both ones-counts have density exactly
`1/2`.  Subtracting, the even-indexed part of `Sᶜ` has density `0`; and it always carries at
least half of `Sᶜ`, so

> **`tendsto_density_compl_zero`: `Sᶜ` has density `0` — a satisfiable digit-local hypothesis
> forces normality only if it reads a set of positions of density `1`.**

The odd-indexed positions are what keeps the second filling a *proper* binary expansion
(infinitely many zeros), which is why the argument uses the index parity inside `Sᶜ` rather
than the naive all-ones filling.

## Consequence for the expedition

The §6 positive branch needed a sampler reading density `≥ 1/2`; it in fact needs density `1`.
Since the arithmetic sample reads density `≤ 1/4` (`Sched.card_isSampled_le_real`), and every
admissible family over any set of scales reads `≤ 1/8` (`G4EntropyScales`), the gap is not a
constant factor to be improved — the whole complement of the sampled set has to shrink to
density zero.  `exists_nonnormal_of_digitLocal_of_lt_one` states the barrier in the form that
now applies: upper density `< 1` at a single value of `c` already refutes.
-/

open Finset Filter

namespace NormalNumbers.G4Entropy

open NormalNumbers

/-! ### Exact single-digit counts -/

/-- Occurrences of the one-letter word `[1]` in the first `n` digits are exactly the positions
below `n` carrying a `1`. -/
lemma countOcc_one_eq (s : ℕ → ℕ) (n : ℕ) :
    countOccurrences [1] ((List.range n).map s)
      = ((Finset.range n).filter (fun j => s j = 1)).card := by
  rw [countOccurrences_range_map]
  congr 1
  refine Finset.ext fun i => ?_
  constructor
  · intro hi
    rw [Finset.mem_filter] at hi
    simp only [List.length_singleton] at hi
    obtain ⟨-, hle, hm⟩ := hi
    have h0 := hm 0 (by norm_num)
    simp only [Nat.add_zero] at h0
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by simpa using h0⟩
  · intro hmem
    rw [Finset.mem_filter, Finset.mem_range] at hmem
    obtain ⟨hi, hs⟩ := hmem
    rw [Finset.mem_filter]
    simp only [List.length_singleton]
    refine ⟨Finset.mem_range.2 (by omega), by omega, ?_⟩
    intro j hj
    have hj0 : j = 0 := by simp only [List.length_singleton] at hj; omega
    subst hj0
    simpa using hs


/-- Normality pins the density of the digit `1` at `1/2`. -/
lemma tendsto_ones_of_isNormal {y : ℝ} (hy : IsNormal 2 y) :
    Tendsto (fun L => ((((Finset.range L).filter
        (fun j => digitOf 2 (Int.fract y) j = 1)).card : ℝ)) / L) atTop (nhds (1 / 2)) := by
  have h := hy [1] (by simp) (by intro d hd; simp at hd; omega)
  simp only [List.length_singleton, pow_one] at h
  have hval : (((2 : ℕ) : ℝ))⁻¹ = 1 / 2 := by norm_num
  rw [hval] at h
  refine h.congr (fun n => ?_)
  rw [countOcc_one_eq]


/-! ### Grafting an arbitrary filling onto the positions `S` does not read -/

section Graft

variable (S : ℕ → Prop) [DecidablePred S]

/-- The digits of `x` at the positions of `S`, and the filling `g` everywhere else. -/
noncomputable def graftDigits (g : ℕ → ℕ) (x : ℝ) (j : ℕ) : ℕ :=
  if S j then digitOf 2 (Int.fract x) j else g j

lemma graftDigits_lt {g : ℕ → ℕ} (hg : ∀ j, g j < 2) (x : ℝ) (j : ℕ) :
    graftDigits S g x j < 2 := by
  unfold graftDigits
  split
  · exact Nat.mod_lt _ (by omega)
  · exact hg j

/-- The grafted real: `x` on `S`, `g` off `S`. -/
noncomputable def graftReal (g : ℕ → ℕ) (x : ℝ) : ℝ := realOfDigits 2 (graftDigits S g x)

variable {S}

lemma properDigits_graft {g : ℕ → ℕ} {x : ℝ}
    (hz : ∀ M : ℕ, ∃ j, M ≤ j ∧ graftDigits S g x j = 0) :
    ProperDigits 2 (graftDigits S g x) := by
  intro M
  obtain ⟨j, hj, h0⟩ := hz M
  exact ⟨j, hj, by rw [h0]; omega⟩

lemma graftReal_mem_Ico {g : ℕ → ℕ} (hg : ∀ j, g j < 2) {x : ℝ}
    (hz : ∀ M : ℕ, ∃ j, M ≤ j ∧ graftDigits S g x j = 0) :
    graftReal S g x ∈ Set.Ico (0 : ℝ) 1 :=
  realOfDigits_mem_Ico 2 (by norm_num) _ (graftDigits_lt S hg x) (properDigits_graft hz)

lemma digitOf_graftReal {g : ℕ → ℕ} (hg : ∀ j, g j < 2) {x : ℝ}
    (hz : ∀ M : ℕ, ∃ j, M ≤ j ∧ graftDigits S g x j = 0) :
    digitOf 2 (Int.fract (graftReal S g x)) = graftDigits S g x := by
  have h := graftReal_mem_Ico hg hz
  rw [Set.mem_Ico] at h
  rw [Int.fract_eq_self.2 h]
  exact digitOf_realOfDigits 2 (by norm_num) _ (graftDigits_lt S hg x) (properDigits_graft hz)

/-- Every graft agrees with `x` at every position `S` reads, hence satisfies every `S`-local
property `x` satisfies. -/
lemma graft_local {g : ℕ → ℕ} (hg : ∀ j, g j < 2) {x : ℝ}
    (hz : ∀ M : ℕ, ∃ j, M ≤ j ∧ graftDigits S g x j = 0) {j : ℕ} (hj : S j) :
    digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract (graftReal S g x)) j := by
  rw [digitOf_graftReal hg hz]
  unfold graftDigits
  rw [if_pos hj]

end Graft

/-! ### The two fillings -/

section Fillings

variable (S : ℕ → Prop) [DecidablePred S]

/-- The number of positions below `j` that `S` does **not** read: the index of `j` inside `Sᶜ`
when `j ∉ S`. -/
def compIdx (j : ℕ) : ℕ := ((Finset.range j).filter (fun i => ¬ S i)).card

/-- The filling that writes a `1` at the even-indexed positions of `Sᶜ` and a `0` at the
odd-indexed ones.  The zeros keep the graft a proper binary expansion; the ones carry at least
half of `Sᶜ`. -/
def pariFill (j : ℕ) : ℕ := if Even (compIdx S j) then 1 else 0

lemma pariFill_lt (j : ℕ) : pariFill S j < 2 := by unfold pariFill; split <;> omega

/-- The ones of the zero-filled graft: the ones of `x` inside `S`. -/
noncomputable def onesIn (x : ℝ) (L : ℕ) : ℕ :=
  ((Finset.range L).filter (fun j => S j ∧ digitOf 2 (Int.fract x) j = 1)).card

/-- The even-indexed positions of `Sᶜ` below `L`. -/
def evenComp (L : ℕ) : ℕ :=
  ((Finset.range L).filter (fun j => ¬ S j ∧ Even (compIdx S j))).card

/-- All positions of `Sᶜ` below `L`. -/
def allComp (L : ℕ) : ℕ := ((Finset.range L).filter (fun j => ¬ S j)).card

variable {S}

/-- **Half of the complement is even-indexed.** -/
lemma allComp_le_two_mul_evenComp (L : ℕ) : allComp S L ≤ 2 * evenComp S L := by
  induction L with
  | zero => simp [allComp, evenComp]
  | succ L ih =>
    have hidx : compIdx S L = allComp S L := rfl
    have hA : allComp S (L + 1) = allComp S L + (if ¬ S L then 1 else 0) := by
      unfold allComp
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases h : S L
      · simp [h]
      · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
        simp [h]
    have hE : evenComp S (L + 1)
        = evenComp S L + (if ¬ S L ∧ Even (compIdx S L) then 1 else 0) := by
      unfold evenComp
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases h : ¬ S L ∧ Even (compIdx S L)
      · rw [if_pos h, Finset.card_insert_of_notMem (by simp)]
        simp [h]
      · simp [h]
    by_cases hS : S L
    · rw [hA, hE, if_neg (not_not_intro hS), if_neg (by tauto)]
      omega
    · rw [hidx] at hE
      by_cases hev : Even (allComp S L)
      · rw [hA, hE, if_pos hS, if_pos ⟨hS, hev⟩]
        omega
      · rw [hA, hE, if_pos hS, if_neg (by tauto)]
        have : allComp S L % 2 = 1 := Nat.not_even_iff.1 hev
        omega

end Fillings


/-! ### The counts carried by the two grafts -/

section Counts

variable {S : ℕ → Prop} [DecidablePred S]

lemma card_ones_graft {g : ℕ → ℕ} (hg : ∀ j, g j < 2) {x : ℝ}
    (hz : ∀ M : ℕ, ∃ j, M ≤ j ∧ graftDigits S g x j = 0) (L : ℕ) :
    ((Finset.range L).filter
        (fun j => digitOf 2 (Int.fract (graftReal S g x)) j = 1)).card
      = ((Finset.range L).filter (fun j => graftDigits S g x j = 1)).card := by
  congr 1
  apply Finset.filter_congr
  intro j _
  rw [digitOf_graftReal hg hz]

/-- The zero filling has exactly the ones of `x` inside `S`. -/
lemma card_ones_zeroFill (x : ℝ) (L : ℕ) :
    ((Finset.range L).filter (fun j => graftDigits S (fun _ => 0) x j = 1)).card
      = onesIn S x L := by
  unfold onesIn
  congr 1
  apply Finset.filter_congr
  intro j _
  unfold graftDigits
  by_cases h : S j <;> simp [h]

/-- The parity filling adds exactly the even-indexed positions of `Sᶜ`. -/
lemma card_ones_pariFill (x : ℝ) (L : ℕ) :
    ((Finset.range L).filter (fun j => graftDigits S (pariFill S) x j = 1)).card
      = onesIn S x L + evenComp S L := by
  have hset : (Finset.range L).filter (fun j => graftDigits S (pariFill S) x j = 1)
      = ((Finset.range L).filter (fun j => S j ∧ digitOf 2 (Int.fract x) j = 1))
        ∪ ((Finset.range L).filter (fun j => ¬ S j ∧ Even (compIdx S j))) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro j _
    unfold graftDigits pariFill
    by_cases h : S j
    · simp [h]
    · by_cases he : Even (compIdx S j) <;> simp [h, he]
  rw [hset, Finset.card_union_of_disjoint]
  · rfl
  · refine Finset.disjoint_left.2 fun j hj hj' => ?_
    rw [Finset.mem_filter] at hj hj'
    exact hj'.2.1 hj.2.1

/-- `Sᶜ` contains arbitrarily late positions of **odd** index, which is what keeps the parity
graft a proper binary expansion. -/
lemma exists_odd_compIdx (hmiss : ∀ M : ℕ, ∃ j, M ≤ j ∧ ¬ S j) (M : ℕ) :
    ∃ j, M ≤ j ∧ ¬ S j ∧ ¬ Even (compIdx S j) := by
  classical
  obtain ⟨j₁, hj₁, hs₁⟩ := hmiss M
  by_cases he : Even (compIdx S j₁)
  · have hex : ∃ d, ¬ S (j₁ + 1 + d) := by
      obtain ⟨j, hj, hs⟩ := hmiss (j₁ + 1)
      exact ⟨j - (j₁ + 1), by rwa [Nat.add_sub_cancel' hj]⟩
    have hs₂ : ¬ S (j₁ + 1 + Nat.find hex) := Nat.find_spec hex
    have hmin : ∀ i, j₁ < i → i < j₁ + 1 + Nat.find hex → S i := by
      intro i h1 h2
      have hd : i - (j₁ + 1) < Nat.find hex := by omega
      have hns := Nat.find_min hex hd
      rw [Nat.add_sub_cancel' (by omega : j₁ + 1 ≤ i)] at hns
      exact not_not.1 hns
    have hcard : compIdx S (j₁ + 1 + Nat.find hex) = compIdx S j₁ + 1 := by
      unfold compIdx
      have hins : (Finset.range (j₁ + 1 + Nat.find hex)).filter (fun i => ¬ S i)
          = insert j₁ ((Finset.range j₁).filter (fun i => ¬ S i)) := by
        refine Finset.ext fun i => ?_
        constructor
        · intro hi
          rw [Finset.mem_filter, Finset.mem_range] at hi
          rcases lt_trichotomy i j₁ with h | h | h
          · exact Finset.mem_insert.2 (Or.inr
              (Finset.mem_filter.2 ⟨Finset.mem_range.2 h, hi.2⟩))
          · exact Finset.mem_insert.2 (Or.inl h)
          · exact absurd (hmin i h hi.1) hi.2
        · intro hi
          rcases Finset.mem_insert.1 hi with h | h
          · subst h
            exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hs₁⟩
          · rw [Finset.mem_filter, Finset.mem_range] at h
            exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), h.2⟩
      rw [hins, Finset.card_insert_of_notMem (by simp)]
    exact ⟨j₁ + 1 + Nat.find hex, by omega, hs₂, by
      rw [hcard]; simp [Nat.even_add_one, he]⟩
  · exact ⟨j₁, hj₁, hs₁, he⟩

end Counts

/-! ### The theorem: a digit-local hypothesis that forces normality reads density one -/

section Main

variable {S : ℕ → Prop} [DecidablePred S]

/-- **The full-strength locality barrier.**  If a property `P` depends on a real only through
its binary digits at the positions of `S`, holds somewhere, and implies binary normality on
`[0,1)`, then the positions `S` does *not* read have density `0`.

The proof compares two fillings of `Sᶜ`: the zero filling, whose ones are the ones of `x`
inside `S`, and the parity filling, which adds the even-indexed positions of `Sᶜ`.  Both are
grafts of `x`, hence both satisfy `P`, hence both are normal and both ones-densities equal
`1/2`; subtracting kills the even-indexed part of `Sᶜ`, and that part always carries at least
half of `Sᶜ`. -/
theorem tendsto_density_compl_zero {P : ℝ → Prop}
    (hloc : ∀ x y : ℝ, (∀ j, S j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) →
      P x → P y)
    {x : ℝ} (hx : P x)
    (hforce : ∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y) :
    Filter.Tendsto (fun L => ((allComp S L : ℝ)) / L) Filter.atTop (nhds 0) := by
  by_cases hmiss : ∀ M : ℕ, ∃ j, M ≤ j ∧ ¬ S j
  · have hz0 : ∀ M : ℕ, ∃ j, M ≤ j ∧ graftDigits S (fun _ => 0) x j = 0 := by
      intro M
      obtain ⟨j, hj, hs⟩ := hmiss M
      exact ⟨j, hj, by unfold graftDigits; rw [if_neg hs]⟩
    have hz1 : ∀ M : ℕ, ∃ j, M ≤ j ∧ graftDigits S (pariFill S) x j = 0 := by
      intro M
      obtain ⟨j, hj, hs, he⟩ := exists_odd_compIdx hmiss M
      exact ⟨j, hj, by unfold graftDigits pariFill; rw [if_neg hs, if_neg he]⟩
    have hgz : ∀ j : ℕ, (fun _ : ℕ => 0) j < 2 := fun _ => by norm_num
    have hnorm : ∀ (g : ℕ → ℕ), (∀ j, g j < 2) →
        (∀ M : ℕ, ∃ j, M ≤ j ∧ graftDigits S g x j = 0) → IsNormal 2 (graftReal S g x) := by
      intro g hg hz
      have hmem := graftReal_mem_Ico hg hz
      rw [Set.mem_Ico] at hmem
      exact hforce _ hmem.1 hmem.2 (hloc x _ (fun j hj => graft_local hg hz hj) hx)
    have hA : Filter.Tendsto (fun L => ((onesIn S x L : ℝ)) / L) Filter.atTop (nhds (1 / 2)) := by
      refine (tendsto_ones_of_isNormal (hnorm _ hgz hz0)).congr fun L => ?_
      rw [card_ones_graft hgz hz0, card_ones_zeroFill]
    have hAB : Filter.Tendsto (fun L => (((onesIn S x L + evenComp S L : ℕ) : ℝ)) / L)
        Filter.atTop (nhds (1 / 2)) := by
      refine (tendsto_ones_of_isNormal (hnorm _ (pariFill_lt S) hz1)).congr fun L => ?_
      rw [card_ones_graft (pariFill_lt S) hz1, card_ones_pariFill]
    have hB : Filter.Tendsto (fun L => ((evenComp S L : ℝ)) / L) Filter.atTop (nhds 0) := by
      have hsub := hAB.sub hA
      rw [sub_self] at hsub
      refine hsub.congr fun L => ?_
      push_cast
      ring
    have hB2 : Filter.Tendsto (fun L => 2 * (((evenComp S L : ℝ)) / L)) Filter.atTop (nhds 0) := by
      have := hB.const_mul (2 : ℝ)
      simpa using this
    refine squeeze_zero (fun L => ?_) (fun L => ?_) hB2
    · positivity
    · rcases Nat.eq_zero_or_pos L with rfl | hL
      · simp
      · have hLR : (0 : ℝ) < L := by exact_mod_cast hL
        rw [mul_div_assoc']
        gcongr
        exact_mod_cast allComp_le_two_mul_evenComp (S := S) L
  · push_neg at hmiss
    obtain ⟨M, hM⟩ := hmiss
    have hbd : ∀ L, allComp S L ≤ M := by
      intro L
      have hsub : (Finset.range L).filter (fun j => ¬ S j) ⊆ Finset.range M := by
        intro j hj
        rw [Finset.mem_filter] at hj
        exact Finset.mem_range.2 (by by_contra h; exact hj.2 (hM j (by omega)))
      simpa [allComp] using Finset.card_le_card hsub
    refine squeeze_zero (fun L => by positivity) (fun L => ?_)
      (tendsto_const_div_atTop_nhds_zero_nat (M : ℝ))
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp
    · have hLR : (0 : ℝ) < L := by exact_mod_cast hL
      gcongr
      exact_mod_cast hbd L

end Main


/-! ### The barrier in usable form -/

section Corollaries

variable {S : ℕ → Prop} [DecidablePred S]

lemma allComp_add_card (L : ℕ) : allComp S L + ((Finset.range L).filter S).card = L := by
  unfold allComp
  rw [Nat.add_comm]
  simpa using Finset.card_filter_add_card_filter_not (s := Finset.range L) (p := S)

/-- **A digit-local hypothesis that forces normality reads density one.** -/
theorem tendsto_density_one_of_forces_normal {P : ℝ → Prop}
    (hloc : ∀ x y : ℝ, (∀ j, S j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) →
      P x → P y)
    {x : ℝ} (hx : P x)
    (hforce : ∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y) :
    Filter.Tendsto (fun L => ((((Finset.range L).filter S).card : ℝ)) / L)
      Filter.atTop (nhds 1) := by
  have h0 := tendsto_density_compl_zero hloc hx hforce
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hsub := hone.sub h0
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with L hL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hc : ((allComp S L : ℝ)) + ((((Finset.range L).filter S).card : ℝ)) = (L : ℝ) := by
    exact_mod_cast allComp_add_card (S := S) L
  field_simp
  linarith

/-- **The barrier at every density below one.**  If the positions `S` reads have eventual upper
density `c < 1`, then no satisfiable `S`-local property implies normality: it holds at some
nonnormal point of `[0,1)`.  Lap 9 needed `c < 1/2`; the comparison of two fillings removes the
factor `2`. -/
theorem exists_nonnormal_of_digitLocal_of_lt_one {c : ℝ} (hc : c < 1) {L₀ : ℕ}
    (hdens : ∀ L : ℕ, L₀ ≤ L → ((((Finset.range L).filter S).card : ℝ)) ≤ c * L)
    {P : ℝ → Prop}
    (hloc : ∀ x y : ℝ, (∀ j, S j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) →
      P x → P y)
    {x : ℝ} (hx : P x) :
    ∃ y : ℝ, 0 ≤ y ∧ y < 1 ∧ P y ∧ ¬ IsNormal 2 y := by
  by_contra hcon
  push_neg at hcon
  have hforce : ∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y := by
    intro y hy0 hy1 hPy
    by_contra hny
    exact hny (hcon y hy0 hy1 hPy)
  have h1 := tendsto_density_one_of_forces_normal hloc hx hforce
  have hev : ∀ᶠ L : ℕ in Filter.atTop,
      ((((Finset.range L).filter S).card : ℝ)) / L ≤ c := by
    filter_upwards [Filter.eventually_ge_atTop L₀, Filter.eventually_gt_atTop 0] with L hL hL0
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL0
    rw [div_le_iff₀ hLR]
    exact hdens L hL
  have := le_of_tendsto h1 hev
  linarith

/-- **Vacuity at every density below one.** -/
theorem not_satisfiable_of_forces_normal_of_lt_one {c : ℝ} (hc : c < 1) {L₀ : ℕ}
    (hdens : ∀ L : ℕ, L₀ ≤ L → ((((Finset.range L).filter S).card : ℝ)) ≤ c * L)
    {P : ℝ → Prop}
    (hloc : ∀ x y : ℝ, (∀ j, S j → digitOf 2 (Int.fract x) j = digitOf 2 (Int.fract y) j) →
      P x → P y)
    (hforce : ∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y) :
    ∀ x : ℝ, ¬ P x := by
  intro x hx
  obtain ⟨y, hy0, hy1, hPy, hny⟩ := exists_nonnormal_of_digitLocal_of_lt_one hc hdens hloc hx
  exact hny (hforce y hy0 hy1 hPy)

end Corollaries

end NormalNumbers.G4Entropy

/-! ## The implemented schedule through the sharpened barrier

The general theorem is not vacuous: it applies verbatim to the base-four schedule, where it
re-derives lap 8's refutation from a hypothesis (`density < 1`) far weaker than the one lap 9
needed (`density < 1/2`).  What is new is the *converse* reading — the specification any repair
must meet is now `density → 1`, i.e. the sampled positions must be *co-null* in `ℕ`, not merely
half of it. -/

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.G4 NormalNumbers.G4Entropy Filter

/-- **`T_E` through the sharpened barrier.**  Only `density ≤ 1/4 < 1` is used. -/
theorem not_T_E_of_density_lt_one : ¬ T_E := by
  intro hT
  obtain ⟨y, hy0, hy1, hPy, hny⟩ :=
    exists_nonnormal_of_digitLocal_of_lt_one (S := IsSampled) (c := 1 / 4) (by norm_num)
      (L₀ := 0) (fun L _ => card_isSampled_le_real L)
      (P := E0)
      (fun x y hd hx => by
        unfold E0 at hx ⊢
        simpa only [fun i => jointLawAt_congr i hd] using hx)
      E0_primeLambertFour
  exact hny (hT y hy0 hy1 hPy)

/-- **The specification for the §6 positive branch, sharp form.**  If any property of the joint
quantized sample laws implied binary normality, the sampled positions would have density
**one**.  (Together with `card_isSampled_le_real` this is a contradiction, which is
`not_T_E_of_density_lt_one`; stated on its own it is the target a new sampler must hit.) -/
theorem tendsto_density_one_of_jointLocal {P : ℝ → Prop}
    (hloc : ∀ x y : ℝ, (∀ i, jointLawAt i x = jointLawAt i y) → P x → P y)
    {x : ℝ} (hx : P x)
    (hforce : ∀ y : ℝ, 0 ≤ y → y < 1 → P y → IsNormal 2 y) :
    Tendsto (fun L => ((((Finset.range L).filter IsSampled).card : ℝ)) / L) atTop (nhds 1) :=
  tendsto_density_one_of_forces_normal
    (fun x y hd => hloc x y (fun i => jointLawAt_congr i hd)) hx hforce

end NormalNumbers.G4.Sched
