/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerBaseLimit

/-!
# Blocking a normal sequence: `IsNormalSequence b s → IsNormalSequence (b^K) (blockOf b K s)`

`tendsto_resCount` is the analytic content; what remains is bookkeeping between a base-`b^K`
word and its base-`b` **flattening**.

* `valOf B w` — the numeric value of the base-`B` word `w`; inverse to `wordOf` on valid words
  (`wordOf_valOf`, `valOf_wordOf`).
* `flat b K w` — replace each base-`b^K` letter by its `K` base-`b` digits.  `flat_wordOf` says
  this is compatible with `wordOf`: `flat b K (wordOf (b^K) ℓ k) = wordOf b (K*ℓ) k`.
* `blockOf b K s j` — the `j`-th base-`b^K` digit of `s`, i.e. the value of the `K`-block of `s`
  starting at `K*j`.
* `matchesAt_blockOf` — `w` occurs in `blockOf` at `j` iff `flat w` occurs in `s` at `K*j`.
* `winCount_blockOf` — hence the window count of `w` is a residue-restricted window count of
  `flat w`, and `tendsto_resCount` finishes.
-/

open Filter Finset

namespace NormalNumbers.PowerBase

open NormalNumbers

/-! ### §1  `wordOf` is a two-sided digit expansion -/

/-- Splitting a word into its high `m₁` and low `m₂` digits. -/
lemma wordOf_split (b m₁ m₂ k : ℕ) :
    wordOf b (m₁ + m₂) k = wordOf b m₁ (k / b ^ m₂) ++ wordOf b m₂ k := by
  sorry

/-- `wordOf` only sees `k` modulo `b ^ m`. -/
lemma wordOf_mod (b m k : ℕ) (hb : 0 < b) : wordOf b m (k % b ^ m) = wordOf b m k := by
  sorry

/-- The numeric value of a base-`B` word. -/
def valOf (B : ℕ) (w : List ℕ) : ℕ := w.foldl (fun a d => a * B + d) 0

@[simp] lemma valOf_nil (B : ℕ) : valOf B [] = 0 := rfl

lemma valOf_append (B : ℕ) (w : List ℕ) (d : ℕ) :
    valOf B (w ++ [d]) = valOf B w * B + d := by
  sorry

lemma valOf_lt {B : ℕ} (hB : 0 < B) (w : List ℕ) (hw : ∀ d ∈ w, d < B) :
    valOf B w < B ^ w.length := by
  sorry

lemma wordOf_valOf {B : ℕ} (hB : 0 < B) (w : List ℕ) (hw : ∀ d ∈ w, d < B) :
    wordOf B w.length (valOf B w) = w := by
  sorry

lemma valOf_wordOf {B : ℕ} (hB : 0 < B) (m k : ℕ) (hk : k < B ^ m) :
    valOf B (wordOf B m k) = k := by
  sorry

/-! ### §2  Flattening -/

/-- Replace each base-`b^K` letter by its `K` base-`b` digits. -/
def flat (b K : ℕ) : List ℕ → List ℕ
  | [] => []
  | d :: w => wordOf b K d ++ flat b K w

@[simp] lemma length_flat (b K : ℕ) (w : List ℕ) : (flat b K w).length = K * w.length := by
  induction w with
  | nil => simp [flat]
  | cons d w ih => simp [flat, ih]; ring

lemma flat_wordOf (b K : ℕ) (hb : 0 < b) (ℓ k : ℕ) :
    flat b K (wordOf (b ^ K) ℓ k) = wordOf b (K * ℓ) k := by
  sorry

/-! ### §3  Matching -/

lemma matchesAt_append_list (s : ℕ → ℕ) (u v : List ℕ) (p : ℕ) :
    MatchesAt s (u ++ v) p ↔ MatchesAt s u p ∧ MatchesAt s v (p + u.length) := by
  sorry

/-- The `j`-th base-`b^K` digit of `s`. -/
def blockOf (b K : ℕ) (s : ℕ → ℕ) (j : ℕ) : ℕ :=
  valOf b ((List.range K).map (fun t => s (K * j + t)))

lemma matchesAt_block {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hs : ∀ j, s j < b) (d j : ℕ)
    (hd : d < b ^ K) :
    MatchesAt s (wordOf b K d) (K * j) ↔ blockOf b K s j = d := by
  sorry

lemma matchesAt_blockOf {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hs : ∀ j, s j < b)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b ^ K) (j : ℕ) :
    MatchesAt (blockOf b K s) w j ↔ MatchesAt s (flat b K w) (K * j) := by
  sorry

/-! ### §4  Counting, and the theorem -/

lemma winCount_blockOf {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hK : 0 < K) (hs : ∀ j, s j < b)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b ^ K) (N : ℕ) :
    winCount (blockOf b K s) w N = resCount K 0 s (flat b K w) (K * N) := by
  sorry

/-- 🎯 **Blocking preserves normality.** -/
theorem isNormalSequence_pow {b K : ℕ} {s : ℕ → ℕ} (hb : 0 < b) (hK : 0 < K)
    (hs : ∀ j, s j < b) (hnorm : IsNormalSequence b s) :
    IsNormalSequence (b ^ K) (blockOf b K s) := by
  sorry

end NormalNumbers.PowerBase
