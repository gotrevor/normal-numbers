/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.LiteratureCampbell
import NormalNumbers.JointLambertQuantitative
import NormalNumbers.AdderEscape

/-!
# Campbell's question on the binary digits of `E`, answered

`jointWords_quantitative` with the single base `{2}` puts any binary word at `≥ N^{1−o(1)}`
positions below `N` in the digits of `E₂ = Σ 1/(2ⁿ − 1)`, hence infinitely often.  Route:
`erdosBorweinE = CastingOut.erdosBorweinAtBase 2` (reindex `n ↦ n + 1`, the `n = 0` term is `0`);
the counted predicate `⌊2^L · orbit 2 E n⌋ = v` is "the word with value `v` starts at digit `n`";
an unbounded count gives occurrences past every `N`.

Frozen statement (do not edit; prove it): `campbellEQuestion_holds`.
-/

namespace NormalNumbers.Literature.Campbell


/-- `E = E₂` in the repo's base-`b` normalization (reindex; the `n = 0` term is `1/0 = 0`). -/
theorem erdosBorweinE_eq : erdosBorweinE = CastingOut.erdosBorweinAtBase 2 := by
  unfold erdosBorweinE CastingOut.erdosBorweinAtBase
  push_cast
  refine ((Nat.succ_injective).tsum_eq (f := fun n : ℕ => (1 : ℝ) / (2 ^ n - 1)) ?_).symm
  intro n hn
  cases n with
  | zero => exact absurd (by norm_num) hn
  | succ m => exact ⟨m, rfl⟩

/-- The value of a binary word, most significant digit first. -/
def wordVal : List ℕ → ℕ
  | [] => 0
  | a :: t => a * 2 ^ t.length + wordVal t

theorem wordVal_lt (w : List ℕ) (hw : ∀ d ∈ w, d < 2) : wordVal w < 2 ^ w.length := by
  induction w with
  | nil => simp [wordVal]
  | cons a t ih =>
    have ha : a ≤ 1 := by have := hw a (by simp); omega
    have ht := ih (fun d hd => hw d (by simp [hd]))
    simp only [wordVal, List.length_cons, pow_succ]
    nlinarith

/-- **Floor window ⇒ digits.**  If `⌊2^{|w|} · orbit 2 x n⌋ = wordVal w`, then the binary digits
of `{x}` at positions `n, …, n + |w| − 1` spell `w`. -/
theorem digits_of_floor_window (w : List ℕ) (hw : ∀ d ∈ w, d < 2) (x : ℝ) (n : ℕ)
    (h : ⌊(2 : ℝ) ^ w.length * orbit 2 x n⌋ = (wordVal w : ℤ)) :
    ∀ j (hj : j < w.length), digitOf 2 (Int.fract x) (n + j) = w[j] := by
  induction w generalizing n with
  | nil => intro j hj; simp at hj
  | cons a t ih =>
    have ha : a < 2 := hw a (by simp)
    have hwt : ∀ d ∈ t, d < 2 := fun d hd => hw d (by simp [hd])
    have hvt := wordVal_lt t hwt
    set o := orbit 2 x n with ho
    set P : ℝ := (2 : ℝ) ^ t.length with hP
    have hP0 : (0 : ℝ) < P := by positivity
    have hh : ⌊(2 * P) * o⌋ = ((a * 2 ^ t.length + wordVal t : ℕ) : ℤ) := by
      simpa [wordVal, pow_succ, mul_comm, mul_left_comm, mul_assoc, hP] using h
    have hlo := Int.floor_le ((2 * P) * o)
    have hhi := Int.lt_floor_add_one ((2 * P) * o)
    rw [hh] at hlo hhi
    have hvtR : (wordVal t : ℝ) + 1 ≤ P := by
      rw [hP]; exact_mod_cast hvt
    push_cast at hlo hhi
    -- the leading digit
    have hfl : ⌊(2 : ℝ) * o⌋ = (a : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast
      constructor
      · nlinarith [Nat.cast_nonneg (α := ℝ) (wordVal t)]
      · nlinarith
    -- the tail window
    have htail : ⌊(2 : ℝ) ^ t.length * orbit 2 x (n + 1)⌋ = (wordVal t : ℤ) := by
      rw [Mahler.orbit_succ, ← ho, Int.fract]
      push_cast
      rw [hfl, Int.floor_eq_iff, ← hP]
      push_cast
      constructor <;> nlinarith
    intro j hj
    cases j with
    | zero =>
      have := Adder.digitOf_eq_floor_orbit 2 le_rfl x n
      rw [← ho] at this; push_cast at this
      rw [hfl] at this
      simpa using this
    | succ k =>
      have := ih hwt (n + 1) htail k (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

/-- An occurrence of the floor window past every `N` (from the power count with `ε = 1/2`). -/
theorem exists_late_window (w : List ℕ) (hw : ∀ d ∈ w, d < 2) (N : ℕ) :
    ∃ n, N ≤ n ∧ ⌊(2 : ℝ) ^ w.length * orbit 2 (CastingOut.erdosBorweinAtBase 2) n⌋
      = (wordVal w : ℤ) := by
  classical
  rcases Nat.eq_zero_or_pos w.length with hL | hL
  · refine ⟨N, le_rfl, ?_⟩
    rw [List.length_eq_zero_iff.mp hL]
    have := orbit_mem_Ico 2 (CastingOut.erdosBorweinAtBase 2) N
    simp [wordVal, Int.floor_eq_zero_iff, this.1, this.2]
  obtain ⟨N0, hN0⟩ := JointLambert.jointWords_power_count {2} (by simp)
    (fun _ => w.length) (fun _ => wordVal w)
    (fun b hb => ⟨hL, by simp at hb; subst hb; exact wordVal_lt w hw⟩) (1 / 2) (by norm_num)
  by_contra hcon
  push Not at hcon
  set M := max N0 ((N + 1) ^ 2)
  have hM := hN0 M (le_max_left _ _)
  have hcount : JointLambert.jointWordCount {2} (fun _ => w.length) (fun _ => wordVal w) M ≤ N := by
    rw [JointLambert.jointWordCount_eq_card_filter]
    refine le_trans (Finset.card_le_card (t := Finset.range N) ?_) (by simp)
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_singleton, forall_eq] at hm
    by_contra hmN
    simp only [Finset.mem_range, not_lt] at hmN
    exact hcon m hmN (by exact_mod_cast hm.2)
  have hMR : ((N + 1 : ℕ) : ℝ) ^ (2 : ℝ) ≤ (M : ℝ) := by
    rw [Real.rpow_two]; exact_mod_cast le_max_right _ _
  have hsq : ((N + 1 : ℕ) : ℝ) ≤ (M : ℝ) ^ (1 - (1 / 2 : ℝ)) := by
    rw [show (1 - (1 / 2 : ℝ)) = 2⁻¹ by norm_num]
    calc ((N + 1 : ℕ) : ℝ) = (((N + 1 : ℕ) : ℝ) ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
          rw [← Real.rpow_mul (by positivity)]; norm_num
      _ ≤ (M : ℝ) ^ (2⁻¹ : ℝ) := Real.rpow_le_rpow (by positivity) hMR (by norm_num)
  have : ((N + 1 : ℕ) : ℝ) ≤ (N : ℝ) := le_trans hsq (le_trans hM (by exact_mod_cast hcount))
  push_cast at this; linarith

/-- **Every binary string occurs infinitely often in the base-2 expansion of `E`**, answering
Campbell, arXiv:2605.24160, §4. -/
theorem campbellEQuestion_holds : CampbellEQuestion := by
  classical
  intro w hw N
  obtain ⟨n, hn, hocc⟩ := exists_late_window w hw N
  refine ⟨n, hn, fun j hj => ?_⟩
  rw [erdosBorweinE_eq]
  exact digits_of_floor_window w hw _ n hocc j hj

end NormalNumbers.Literature.Campbell
