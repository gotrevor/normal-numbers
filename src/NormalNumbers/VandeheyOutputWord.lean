/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NormalNumbers.VandeheyOutputFreq
import NormalNumbers.VandeheyRescale
import NormalNumbers.OccurrenceCountEquiv

/-!
# The abstract output word of a transducer, and its occurrence counts

`VandeheyOutputFreq` proves that trigger counts over the first `n` INPUT digits have an
`x`-independent Cesàro limit; `VandeheyRescale` transports a Cesàro limit from input indices to
output indices.  The piece between them is the *output word itself*: Vandehey's transducer emits,
at each input digit, a (possibly empty) block of output digits, and CF-normality of the image is a
statement about the resulting output stream.

This file builds that layer abstractly — for any `out : S → ℕ → List ℕ` — and proves the parts
that are pure combinatorics:

* `outWord`, `outLen`: the output of the first `n` input digits and its length.  `outWord` grows
  by prefix (`outWord_prefix`), so `outLen` is monotone.
* `outDigit`: the output *stream*, well defined as soon as the output is unbounded, and agreeing
  with `outWord` wherever both are defined (`outWord_eq_map_outDigit`).
* `countOccurrences_le_of_prefix`: occurrence counts are monotone along prefixes, so
  `outCount v m = countOccurrences v (first m output digits)` is a monotone counting function —
  exactly the hypothesis `VandeheyRescale` needs.
* `tendsto_outCount_div`: the assembled statement.  Given (i) `outCount v (outLen n) / n → L`
  (what the trigger engine supplies, once §5's trigger family is identified) and (ii)
  `outLen n / n → c > 0` (Vandehey's Lemma 6.1), the output word frequency of `v` converges to
  `L / c` — with no reference to `x` beyond those two inputs.

What is NOT here is the identification of the trigger family with `v`'s occurrences, and the
proof that `outDigit` is the CF expansion of `p·x`; those are the automaton's own obligations
(`PENDING_WORK.md`).
-/

namespace NormalNumbers.VandeheyOut

open Filter VandeheyAut

variable {S : Type*} [DecidableEq S]

/-! ## Prefix monotonicity of occurrence counts -/

/-- `List.range` grows by prefix. -/
lemma range_prefix {m m' : ℕ} (h : m ≤ m') : List.range m <+: List.range m' := by
  induction m' with
  | zero => simpa using Nat.le_zero.mp h
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with hk | hk
    · exact (ih (by omega)).trans ⟨[k], (List.range_succ).symm⟩
    · rw [hk]
  
/-- **Occurrence counts only grow.**  Appending to the right cannot destroy an occurrence, and
each occurrence of the shorter list survives at the same position. -/
lemma countOccurrences_append_le (v l r : List ℕ) :
    countOccurrences v l ≤ countOccurrences v (l ++ r) := by
  induction l with
  | nil =>
    rcases eq_or_ne v [] with rfl | hv
    · have hall : ∀ t ∈ (([] : List ℕ) ++ r).tails, ([] : List ℕ).isPrefixOf t = true := by
        simp
      have : countOccurrences ([] : List ℕ) (([] : List ℕ) ++ r) = (r.tails).length := by
        simp only [countOccurrences, List.nil_append]
        exact List.countP_eq_length.mpr (by simpa using hall)
      rw [this]
      have h1 : countOccurrences ([] : List ℕ) ([] : List ℕ) = 1 := by
        simp [countOccurrences]
      rw [h1, List.length_tails]
      omega
    · have h0 : countOccurrences v ([] : List ℕ) = 0 := by
        have : ¬ (v.isPrefixOf ([] : List ℕ) = true) := by
          cases v with
          | nil => exact absurd rfl hv
          | cons a s => simp [List.isPrefixOf]
        simp [countOccurrences, this]
      simp [h0]
  | cons a t ih =>
    simp only [countOccurrences, List.cons_append, List.tails_cons, List.countP_cons] at *
    have hpref : v.isPrefixOf (a :: t) = true → v.isPrefixOf (a :: (t ++ r)) = true := by
      intro h
      have h1 : v <+: a :: t := List.isPrefixOf_iff_prefix.mp h
      have h2 : v <+: a :: (t ++ r) := h1.trans ⟨r, by simp⟩
      exact List.isPrefixOf_iff_prefix.mpr h2
    by_cases hv : v.isPrefixOf (a :: t) = true
    · rw [if_pos hv, if_pos (hpref hv)]
      omega
    · rw [if_neg hv]
      split_ifs <;> omega

lemma countOccurrences_le_of_prefix {v l l' : List ℕ} (h : l <+: l') :
    countOccurrences v l ≤ countOccurrences v l' := by
  obtain ⟨r, rfl⟩ := h
  exact countOccurrences_append_le v l r

/-! ## The output word -/

variable (δ : S → ℕ → S) (out : S → ℕ → List ℕ) (s₀ : S)

/-- The output block emitted while reading input digit `i`. -/
noncomputable def outBlock (x : ℝ) (i : ℕ) : List ℕ :=
  out (stateAt δ s₀ x i) (cfDigit x i)

/-- The output produced by the first `n` input digits. -/
noncomputable def outWord (x : ℝ) (n : ℕ) : List ℕ :=
  (List.range n).flatMap (outBlock δ out s₀ x)

/-- The length of the output produced by the first `n` input digits — Vandehey's `ℓ(n)`. -/
noncomputable def outLen (x : ℝ) (n : ℕ) : ℕ := (outWord δ out s₀ x n).length

lemma outWord_succ (x : ℝ) (n : ℕ) :
    outWord δ out s₀ x (n + 1) = outWord δ out s₀ x n ++ outBlock δ out s₀ x n := by
  simp [outWord, List.range_succ]

lemma outWord_prefix (x : ℝ) {n n' : ℕ} (h : n ≤ n') :
    outWord δ out s₀ x n <+: outWord δ out s₀ x n' := by
  simp only [outWord]
  exact (range_prefix h).flatMap _

lemma outLen_mono (x : ℝ) : Monotone (outLen δ out s₀ x) := fun n n' h =>
  (outWord_prefix δ out s₀ x h).length_le

/-! ## The output stream -/

variable {δ out s₀}

/-- The `j`-th output digit, read off any `outWord` long enough to contain it.  `outDigit` needs
the output to be unbounded; that is Vandehey's Lemma 6.1 in its weakest form. -/
noncomputable def outDigit (x : ℝ) (hcof : ∀ j, ∃ n, j < outLen δ out s₀ x n) (j : ℕ) : ℕ :=
  (outWord δ out s₀ x (Nat.find (hcof j))).getD j 0

/-- The stream agrees with every long enough `outWord`: prefixes determine digits. -/
lemma outDigit_eq (x : ℝ) (hcof : ∀ j, ∃ n, j < outLen δ out s₀ x n) {j n : ℕ}
    (hn : j < outLen δ out s₀ x n) :
    outDigit x hcof j = (outWord δ out s₀ x n).getD j 0 := by
  classical
  set n₀ : ℕ := Nat.find (hcof j) with hn₀
  have hn₀spec : j < outLen δ out s₀ x n₀ := Nat.find_spec (hcof j)
  -- both indices work, so compare each with their max
  have key : ∀ p q : ℕ, p ≤ q → j < outLen δ out s₀ x p →
      (outWord δ out s₀ x p).getD j 0 = (outWord δ out s₀ x q).getD j 0 := by
    intro p q hpq hjp
    obtain ⟨r, hr⟩ := outWord_prefix δ out s₀ x hpq
    rw [← hr, List.getD_append _ _ _ _ hjp]
  rcases le_total n₀ n with h | h
  · rw [outDigit, ← hn₀, key n₀ n h hn₀spec]
  · rw [outDigit, ← hn₀, ← key n n₀ h hn]

/-- **The output word is the stream's prefix.**  This is what lets an occurrence count over the
output word be read as a count over the stream. -/
lemma outWord_eq_map_outDigit (x : ℝ) (hcof : ∀ j, ∃ n, j < outLen δ out s₀ x n) (n : ℕ) :
    outWord δ out s₀ x n = (List.range (outLen δ out s₀ x n)).map (outDigit x hcof) := by
  refine List.ext_getElem (by simp [outLen]) ?_
  intro j h1 h2
  have hj : j < outLen δ out s₀ x n := by simpa [outLen] using h1
  have hd : outDigit x hcof j = (outWord δ out s₀ x n).getD j 0 := outDigit_eq x hcof hj
  rw [List.getElem_map, List.getElem_range, hd, List.getD_eq_getElem _ _ hj]
  rfl

/-! ## The occurrence count, and the assembled frequency statement -/

/-- The number of occurrences of `v` in the first `m` OUTPUT digits. -/
noncomputable def outCount (x : ℝ) (hcof : ∀ j, ∃ n, j < outLen δ out s₀ x n)
    (v : List ℕ) (m : ℕ) : ℝ :=
  (countOccurrences v ((List.range m).map (outDigit x hcof)) : ℝ)

lemma outCount_mono (x : ℝ) (hcof : ∀ j, ∃ n, j < outLen δ out s₀ x n) (v : List ℕ) :
    Monotone (outCount x hcof v) := by
  intro m m' h
  have : countOccurrences v ((List.range m).map (outDigit x hcof))
      ≤ countOccurrences v ((List.range m').map (outDigit x hcof)) :=
    countOccurrences_le_of_prefix ((range_prefix h).map _)
  simp only [outCount]
  exact_mod_cast this

/-- The count over the output of `n` input digits is the count over `outWord`. -/
lemma outCount_outLen (x : ℝ) (hcof : ∀ j, ∃ n, j < outLen δ out s₀ x n) (v : List ℕ) (n : ℕ) :
    outCount x hcof v (outLen δ out s₀ x n)
      = (countOccurrences v (outWord δ out s₀ x n) : ℝ) := by
  rw [outCount, ← outWord_eq_map_outDigit x hcof n]

/-- **The assembled output-frequency statement.**  The two inputs are exactly Vandehey's §6:
`hcount` is the trigger count's Cesàro limit (his `c_r n(1+o(1))`) and `hlen` is his Lemma 6.1
(`ℓ(n) = c₁ n(1+o(1))`).  The conclusion is the window frequency of `v` in the OUTPUT stream,
which is what CF-normality of the image asks for. -/
theorem tendsto_outCount_div (x : ℝ) (hcof : ∀ j, ∃ n, j < outLen δ out s₀ x n)
    (v : List ℕ) {L c : ℝ} (hc : 0 < c)
    (hlen : Tendsto (fun n => (outLen δ out s₀ x n : ℝ) / n) atTop (nhds c))
    (hcount : Tendsto
      (fun n => (countOccurrences v (outWord δ out s₀ x n) : ℝ) / n) atTop (nhds L)) :
    Tendsto (fun m => outCount x hcof v m / m) atTop (nhds (L / c)) := by
  refine Rescale.tendsto_div_of_tendsto_comp_of_monotone (outCount_mono x hcof v)
    (outLen_mono δ out s₀ x) hc hlen ?_
  refine hcount.congr ?_
  intro n
  rw [outCount_outLen]

/-! ## The §5 bucketing: occurrences split by the block they start in

`occStart` (from `OccurrenceCountEquiv`) counts START positions, reading the stream past the end
of the window — which is exactly the convention in which an occurrence belongs unambiguously to
the block it starts in.  So the split by block is an EXACT identity, and Vandehey's "up to
`O(1)`" is then supplied once and for all by `occStart_le_countOccurrences_add`. -/

/-- The number of occurrences of `v` starting inside the block emitted at input digit `i`. -/
noncomputable def fireOut (x : ℝ) (hcof : ∀ j, ∃ n, j < outLen δ out s₀ x n)
    (v : List ℕ) (i : ℕ) : ℕ :=
  ((Finset.Ico (outLen δ out s₀ x i) (outLen δ out s₀ x (i + 1))).filter
    (fun p => v = (List.range' p v.length).map (outDigit x hcof))).card

@[simp] lemma outWord_zero (x : ℝ) : outWord δ out s₀ x 0 = [] := by simp [outWord]

@[simp] lemma outLen_zero (x : ℝ) : outLen δ out s₀ x 0 = 0 := by simp [outLen]

/-- **The exact block decomposition.**  Every occurrence in the output of the first `n` input
digits starts in exactly one of the `n` blocks. -/
theorem occStart_eq_sum_fireOut (x : ℝ) (hcof : ∀ j, ∃ n, j < outLen δ out s₀ x n)
    (v : List ℕ) (n : ℕ) :
    occStart v (outDigit x hcof) (outLen δ out s₀ x n)
      = ∑ i ∈ Finset.range n, fireOut x hcof v i := by
  classical
  induction n with
  | zero => simp [occStart]
  | succ n ih =>
    have hle : outLen δ out s₀ x n ≤ outLen δ out s₀ x (n + 1) :=
      outLen_mono δ out s₀ x (Nat.le_succ n)
    have hsplit : Finset.range (outLen δ out s₀ x (n + 1))
        = Finset.range (outLen δ out s₀ x n)
          ∪ Finset.Ico (outLen δ out s₀ x n) (outLen δ out s₀ x (n + 1)) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hle]
    have hdisj : Disjoint (Finset.range (outLen δ out s₀ x n))
        (Finset.Ico (outLen δ out s₀ x n) (outLen δ out s₀ x (n + 1))) := by
      rw [Finset.disjoint_left]
      intro p hp hp'
      simp only [Finset.mem_range] at hp
      simp only [Finset.mem_Ico] at hp'
      omega
    rw [occStart, hsplit, Finset.filter_union,
      Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _)
        (Finset.filter_subset _ _)),
      Finset.sum_range_succ, ← occStart, ih, fireOut]

/-- **Vandehey §5, abstractly.**  The occurrence count in the output word and the positionwise
firing count differ by at most `|v|` — a constant, so they have the same Cesàro limit. -/
theorem abs_countOccurrences_sub_sum_fireOut_le (x : ℝ)
    (hcof : ∀ j, ∃ n, j < outLen δ out s₀ x n) {v : List ℕ} (hv : v ≠ []) (n : ℕ) :
    |(countOccurrences v (outWord δ out s₀ x n) : ℝ)
        - (∑ i ∈ Finset.range n, fireOut x hcof v i : ℕ)| ≤ (v.length : ℝ) := by
  have hrw : countOccurrences v (outWord δ out s₀ x n)
      = countOccurrences v ((List.range (outLen δ out s₀ x n)).map (outDigit x hcof)) := by
    rw [← outWord_eq_map_outDigit x hcof n]
  have h1 := countOccurrences_le_occStart v hv (outDigit x hcof) (outLen δ out s₀ x n)
  have h2 := occStart_le_countOccurrences_add v hv (outDigit x hcof) (outLen δ out s₀ x n)
  rw [occStart_eq_sum_fireOut x hcof v n] at h1 h2
  rw [hrw]
  have h1r : (countOccurrences v ((List.range (outLen δ out s₀ x n)).map (outDigit x hcof)) : ℝ)
      ≤ (∑ i ∈ Finset.range n, fireOut x hcof v i : ℕ) := by exact_mod_cast h1
  have h2r : ((∑ i ∈ Finset.range n, fireOut x hcof v i : ℕ) : ℝ)
      ≤ (countOccurrences v ((List.range (outLen δ out s₀ x n)).map (outDigit x hcof)) : ℝ)
        + (v.length : ℝ) := by exact_mod_cast h2
  rw [abs_le]
  constructor <;> linarith

/-- **The §5 bridge in Cesàro form.**  If the positionwise firing count has an `x`-independent
Cesàro limit — which is precisely what `exists_tendsto_trigTotal` delivers — then so does the
occurrence count in the output word, with the SAME limit. -/
theorem tendsto_countOccurrences_outWord_of_fireOut (x : ℝ)
    (hcof : ∀ j, ∃ n, j < outLen δ out s₀ x n) {v : List ℕ} (hv : v ≠ []) {L : ℝ}
    (h : Tendsto (fun n => ((∑ i ∈ Finset.range n, fireOut x hcof v i : ℕ) : ℝ) / n)
      atTop (nhds L)) :
    Tendsto (fun n => (countOccurrences v (outWord δ out s₀ x n) : ℝ) / n) atTop (nhds L) := by
  have hkey : Tendsto (fun n : ℕ =>
      (countOccurrences v (outWord δ out s₀ x n) : ℝ) / n
        - ((∑ i ∈ Finset.range n, fireOut x hcof v i : ℕ) : ℝ) / n) atTop (nhds 0) := by
    have hconst : Tendsto (fun n : ℕ => (v.length : ℝ) / n) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (v.length : ℝ)
    refine squeeze_zero_norm' ?_ hconst
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_sub_div_same, Real.norm_eq_abs, abs_div, abs_of_pos hnr]
    exact div_le_div_of_nonneg_right
      (abs_countOccurrences_sub_sum_fireOut_le x hcof hv n) hnr.le
  have hsum := h.add hkey
  rw [add_zero] at hsum
  refine hsum.congr ?_
  intro n
  ring


end NormalNumbers.VandeheyOut

section
open NormalNumbers.VandeheyOut
#print axioms countOccurrences_le_of_prefix
#print axioms outWord_eq_map_outDigit
#print axioms tendsto_outCount_div
#print axioms occStart_eq_sum_fireOut
#print axioms tendsto_countOccurrences_outWord_of_fireOut
end
