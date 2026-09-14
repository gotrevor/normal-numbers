/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.Counting
import NormalNumbers.SeqDefs
import NormalNumbers.Bridge

/-!
# Entropy expedition — the window-counting layer (rung 1)

`IsNormalSequence` is phrased through `countOccurrences v ((List.range n).map s)`, a
`List.tails.countP`.  Every statement this campaign produces is arithmetic — a count of
*positions* — so this module fixes the arithmetic shape once and for all:

`winCount s v n = #{p < n : v starts a match of s at p}`  (`Counting.MatchesAt`).

* `isNormalSequence_of_tendsto_winCount` — the criterion: if every nonempty base-`b` word has
  `winCount s v n / n → b^{−|v|}`, then `s` is a normal sequence.  The seam between the two
  counting conventions is at most `|v|` windows (`Counting.card_filter_matchesAt_le`), which is
  a constant and so invisible in the limit.
* `card_filter_periodic` — an `L`-periodic predicate has exactly `r` times as many witnesses in
  `[0, rL)` as in `[0, L)`.  This is what makes a *repeated* block cost no seams at all: the
  windows that wrap around a copy boundary are already counted, cyclically, inside one period.

Nothing here mentions `G₄`.  This is the vocabulary rungs 2–3 are stated in.
-/

namespace NormalNumbers

open Filter Finset

/-- **Window count**: the number of start positions `p < n` at which `v` matches `s`.
Windows that begin below `n` but run past it are counted (contrast `countOccurrences`, which
counts only windows fitting inside the length-`n` prefix); the two differ by at most `|v|`. -/
def winCount (s : ℕ → ℕ) (v : List ℕ) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (MatchesAt s v)).card

lemma winCount_le (s : ℕ → ℕ) (v : List ℕ) (n : ℕ) : winCount s v n ≤ n := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp

lemma winCount_zero (s : ℕ → ℕ) (v : List ℕ) : winCount s v 0 = 0 := by
  simp [winCount]

/-- `winCount` splits at any interior point: `[0,n) = [0,a) ⊎ [a,n)`. -/
lemma winCount_split (s : ℕ → ℕ) (v : List ℕ) {a n : ℕ} (han : a ≤ n) :
    winCount s v n
      = winCount s v a + ((Finset.Ico a n).filter (MatchesAt s v)).card := by
  classical
  unfold winCount
  rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le a) han, Finset.filter_union]
  refine (Finset.card_union_of_disjoint ?_)
  refine Finset.disjoint_filter_filter ?_
  exact Finset.Ico_disjoint_Ico_consecutive 0 a n

/-! ### The criterion -/

/-- **Rung 1.**  A digit sequence whose every nonempty base-`b` word has window frequency
`b^{−|v|}` is a normal sequence.  (`countOccurrences` and `winCount` differ by at most `|v|`
boundary windows, a constant.) -/
theorem isNormalSequence_of_tendsto_winCount {b : ℕ} {s : ℕ → ℕ}
    (h : ∀ v : List ℕ, v ≠ [] → (∀ d ∈ v, d < b) →
      Tendsto (fun n => (winCount s v n : ℝ) / n) atTop (nhds (((b : ℝ) ^ v.length)⁻¹))) :
    IsNormalSequence b s := by
  intro v hv hvb
  have hlim := h v hv hvb
  obtain ⟨hle₁, hle₂⟩ :
      (∀ n, countOccurrences v ((List.range n).map s) ≤ winCount s v n)
        ∧ ∀ n, winCount s v n ≤ countOccurrences v ((List.range n).map s) + v.length := by
    refine ⟨fun n => (card_filter_matchesAt_le s v hv n).1,
      fun n => (card_filter_matchesAt_le s v hv n).2⟩
  -- squeeze `countOccurrences/n` between `winCount/n - |v|/n` and `winCount/n`
  have hlow : Tendsto (fun n : ℕ => (winCount s v n : ℝ) / n - (v.length : ℝ) / n)
      atTop (nhds (((b : ℝ) ^ v.length)⁻¹)) := by
    have hC : Tendsto (fun n : ℕ => (v.length : ℝ) / n) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using hlim.sub hC
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hlim ?_ ?_
  · intro n
    dsimp only
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_sub_div_same]
    gcongr
    have hcast : (winCount s v n : ℝ)
        ≤ (countOccurrences v ((List.range n).map s) : ℝ) + v.length := by
      exact_mod_cast hle₂ n
    linarith
  · intro n
    dsimp only
    by_cases hn : n = 0
    · subst hn; simp
    have hnpos : (0 : ℝ) < n := by positivity
    gcongr
    exact_mod_cast hle₁ n

/-! ### Periodic counting -/

/-- An `L`-periodic predicate has exactly `r` times as many witnesses in `[0, r·L)` as in
`[0, L)`.  This is why repeating a block costs **no** seam: the wrap-around windows are already
counted cyclically inside one period. -/
theorem card_filter_periodic {P : ℕ → Prop} [DecidablePred P] {L : ℕ}
    (hper : ∀ p, P (p + L) ↔ P p) (r : ℕ) :
    ((Finset.range (r * L)).filter P).card = r * ((Finset.range L).filter P).card := by
  classical
  have hshift : ∀ r p, P (p + r * L) ↔ P p := by
    intro r
    induction r with
    | zero => intro p; simp
    | succ r ihr =>
      intro p
      have hp : p + (r + 1) * L = (p + r * L) + L := by ring
      rw [hp, hper, ihr]
  induction r with
  | zero => simp
  | succ r ih =>
    have hsplit : (r + 1) * L = r * L + L := by ring
    have hle : r * L ≤ (r + 1) * L := by omega
    have hcard : ((Finset.Ico (r * L) ((r + 1) * L)).filter P).card
        = ((Finset.range L).filter P).card := by
      rw [Finset.card_bij (fun p _ => p - r * L)]
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico, hsplit] at hp
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        have hiff := (hshift r (p - r * L)).symm
        have hp' : p - r * L + r * L = p := by omega
        rw [hp'] at hiff
        exact hiff.mpr hp.2
      · intro p hp q hq hpq
        simp only [Finset.mem_filter, Finset.mem_Ico, hsplit] at hp hq
        omega
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_range] at hq
        refine ⟨q + r * L, ?_, by omega⟩
        simp only [Finset.mem_filter, Finset.mem_Ico, hsplit]
        exact ⟨by omega, (hshift r q).mpr hq.2⟩
    have hrw : ((Finset.range ((r + 1) * L)).filter P).card
        = ((Finset.range (r * L)).filter P).card
          + ((Finset.Ico (r * L) ((r + 1) * L)).filter P).card := by
      classical
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le (r * L)) hle, Finset.filter_union]
      refine (Finset.card_union_of_disjoint ?_)
      exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive 0 (r * L) _)
    rw [hrw, ih, hcard]
    ring

/-- A normal sequence never sticks at `b − 1`: the word `[0]` has positive frequency. -/
theorem properDigits_of_isNormalSequence {b : ℕ} (hb : 2 ≤ b) {s : ℕ → ℕ}
    (hn : IsNormalSequence b s) : ProperDigits b s := by
  classical
  intro N
  by_contra hcon
  push_neg at hcon
  have hlim := hn [0] (by simp) (by intro x hx; simp only [List.mem_singleton] at hx; omega)
  have hbound : ∀ n, countOccurrences [0] ((List.range n).map s) ≤ N := by
    intro n
    rw [countOccurrences_range_map]
    refine le_trans (Finset.card_le_card (t := Finset.range N) ?_) (by simp)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    by_contra hiN
    have hNi : N ≤ i := by omega
    have h0 : s (i + 0) = ([0] : List ℕ).getD 0 0 := hi.2.2 0 (by simp)
    simp only [List.getD_cons_zero, Nat.add_zero] at h0
    rw [hcon i hNi] at h0
    omega
  have hzero : Tendsto
      (fun n : ℕ => (countOccurrences [0] ((List.range n).map s) : ℝ) / n) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat (N : ℝ)) (fun n => ?_) (fun n => ?_)
    · positivity
    · dsimp only
      rcases Nat.eq_zero_or_pos n with hn0 | hn0
      · subst hn0; simp
      have : (0 : ℝ) < n := by exact_mod_cast hn0
      gcongr
      exact_mod_cast hbound n
  have huniq := tendsto_nhds_unique hlim hzero
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  simp only [List.length_singleton, pow_one] at huniq
  have : (0 : ℝ) < ((b : ℝ))⁻¹ := by positivity
  rw [huniq] at this
  exact lt_irrefl _ this

/-! ### Splitting a range into equal blocks -/

/-- `[0, P·A)` is `P` consecutive blocks of length `A`. -/
lemma sum_range_mul {β : Type*} [AddCommMonoid β] (g : ℕ → β) (P A : ℕ) :
    ∑ w ∈ Finset.range (P * A), g w
      = ∑ a ∈ Finset.range P, ∑ e ∈ Finset.range A, g (a * A + e) := by
  induction P with
  | zero => simp
  | succ P ih =>
    have hsplit : (P + 1) * A = P * A + A := by ring
    rw [Finset.sum_range_succ, ← ih, hsplit]
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive g (Nat.zero_le (P * A)) (Nat.le_add_right (P * A) A),
      ← Finset.range_eq_Ico]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    simp

/-- The same split for a count. -/
lemma card_filter_range_mul {Q : ℕ → Prop} [DecidablePred Q] (P A : ℕ) :
    ((Finset.range (P * A)).filter Q).card
      = ∑ a ∈ Finset.range P, ((Finset.range A).filter (fun e => Q (a * A + e))).card := by
  classical
  simp only [Finset.card_filter]
  rw [sum_range_mul (fun w => if Q w then 1 else 0) P A]

end NormalNumbers
