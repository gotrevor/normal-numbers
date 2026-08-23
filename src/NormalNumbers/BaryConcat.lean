/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.BaryBlockCount

/-!
# W4 b-ary side — Becher–Yuhjtman Lemma 9 (discrepancy concatenation)

B–Y Lemma 9 (= Becher–Heiber–Slaman Lemma 3.1): simple b-ary discrepancy
survives concatenation.  Blocks are `List (Fin b)`; discrepancy is kept in
*deviation form* — `HasDiscLt u ε` says every digit count deviates from
`|u|/b` by less than `ε·|u|` — which avoids division and makes each part a
triangle inequality:

* `HasDiscLt.append` (part 1): good `u` and good `v` give good `u ++ v`, at
  the same `ε`.
* `hasDiscLt_append_take` (part 2a): good `v` plus a *short* tail `u`
  (`|u| < ε·|v|`) gives every extension `v ++ u.take ℓ` discrepancy `< 2ε`.
* `hasDiscLt_short_append` (part 2b): a short *prefix* `u` before good `v`
  gives `u ++ v` discrepancy `< 2ε`.

`digitCount_eq_count_ofFn` bridges to the block representation
`Fin k → Fin b` used by Lemma 8 (`card_baryDiscrepancy_ge_le`).
-/

namespace NormalNumbers

open Finset

/-- Deviation-form simple discrepancy bound: every digit count of the block
`u` is within `ε·|u|` of the fair share `|u|/b` (strictly). -/
def HasDiscLt {b : ℕ} (u : List (Fin b)) (ε : ℝ) : Prop :=
  ∀ s : Fin b, |(u.count s : ℝ) - u.length / b| < ε * u.length

/-- Digit counts are bounded by the block length. -/
theorem count_le_length_real {b : ℕ} (u : List (Fin b)) (s : Fin b) :
    (u.count s : ℝ) ≤ u.length := by
  exact_mod_cast u.count_le_length

/-- Crude deviation bound: `|count − n/b| ≤ n` always (for `1 ≤ b`). -/
theorem abs_count_sub_le_length {b : ℕ} (hb : 1 ≤ b) (u : List (Fin b))
    (s : Fin b) :
    |(u.count s : ℝ) - u.length / b| ≤ u.length := by
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have h0 : (0 : ℝ) ≤ (u.count s : ℝ) := by positivity
  have h1 := count_le_length_real u s
  have h2 : (0 : ℝ) ≤ (u.length : ℝ) / b := by positivity
  have h3 : (u.length : ℝ) / b ≤ u.length := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Nat.cast_nonneg (α := ℝ) u.length]
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- **B–Y Lemma 9, part 1**: discrepancy `< ε` survives concatenation. -/
theorem HasDiscLt.append {b : ℕ} {u v : List (Fin b)} {ε : ℝ}
    (hu : HasDiscLt u ε) (hv : HasDiscLt v ε) :
    HasDiscLt (u ++ v) ε := by
  intro s
  have hcu := hu s
  have hcv := hv s
  have hcount : ((u ++ v).count s : ℝ) = (u.count s : ℝ) + v.count s := by
    push_cast [List.count_append]; ring
  have hlen : ((u ++ v).length : ℝ) = (u.length : ℝ) + v.length := by
    push_cast [List.length_append]; ring
  rw [hcount, hlen]
  calc |(u.count s : ℝ) + v.count s - ((u.length : ℝ) + v.length) / b|
      = |((u.count s : ℝ) - u.length / b) + ((v.count s : ℝ) - v.length / b)| := by
        ring_nf
    _ ≤ |(u.count s : ℝ) - u.length / b| + |(v.count s : ℝ) - v.length / b| :=
        abs_add_le _ _
    _ < ε * u.length + ε * v.length := by exact add_lt_add hcu hcv
    _ = ε * ((u.length : ℝ) + v.length) := by ring

/-- **B–Y Lemma 9, part 2a**: appending any prefix of a short block `u`
(`|u| < ε·|v|`) to a good block `v` keeps discrepancy `< 2ε`. -/
theorem hasDiscLt_append_take {b : ℕ} (hb : 1 ≤ b) {u v : List (Fin b)}
    {ε : ℝ} (hv : HasDiscLt v ε) (hshort : (u.length : ℝ) < ε * v.length)
    (l : ℕ) (hl : l ≤ u.length) :
    HasDiscLt (v ++ u.take l) (2 * ε) := by
  intro s
  have hcv := hv s
  have htake := abs_count_sub_le_length hb (u.take l) s
  have hltake : ((u.take l).length : ℝ) ≤ u.length := by
    have h : (u.take l).length ≤ u.length := by
      rw [List.length_take]; exact min_le_right _ _
    exact_mod_cast h
  have hcount : ((v ++ u.take l).count s : ℝ)
      = (v.count s : ℝ) + (u.take l).count s := by
    push_cast [List.count_append]; ring
  have hlen : ((v ++ u.take l).length : ℝ)
      = (v.length : ℝ) + (u.take l).length := by
    push_cast [List.length_append]; ring
  have hlv0 : (0 : ℝ) ≤ v.length := Nat.cast_nonneg _
  have hε0 : 0 ≤ ε := by
    by_contra h
    push Not at h
    nlinarith [Nat.cast_nonneg (α := ℝ) u.length]
  rw [hcount, hlen]
  calc |(v.count s : ℝ) + (u.take l).count s
        - ((v.length : ℝ) + (u.take l).length) / b|
      = |((v.count s : ℝ) - v.length / b)
          + (((u.take l).count s : ℝ) - (u.take l).length / b)| := by ring_nf
    _ ≤ |(v.count s : ℝ) - v.length / b|
          + |((u.take l).count s : ℝ) - (u.take l).length / b| := abs_add_le _ _
    _ < ε * v.length + ε * v.length := by
        have : ((u.take l).length : ℝ) < ε * v.length := lt_of_le_of_lt hltake hshort
        exact add_lt_add_of_lt_of_le hcv (htake.trans (by linarith))
    _ ≤ 2 * ε * ((v.length : ℝ) + (u.take l).length) := by
        have h0 : (0 : ℝ) ≤ (u.take l).length := Nat.cast_nonneg _
        nlinarith
  -- (the final step uses `ε·Lv + ε·Lv = 2ε·Lv ≤ 2ε·(Lv + ℓ)`)

/-- **B–Y Lemma 9, part 2b**: a short foreign prefix `u` (`|u| < ε·|v|`)
before a good block `v` keeps discrepancy `< 2ε`. -/
theorem hasDiscLt_short_append {b : ℕ} (hb : 1 ≤ b) {u v : List (Fin b)}
    {ε : ℝ} (hv : HasDiscLt v ε) (hshort : (u.length : ℝ) < ε * v.length) :
    HasDiscLt (u ++ v) (2 * ε) := by
  intro s
  have hcv := hv s
  have hu := abs_count_sub_le_length hb u s
  have hcount : ((u ++ v).count s : ℝ) = (u.count s : ℝ) + v.count s := by
    push_cast [List.count_append]; ring
  have hlen : ((u ++ v).length : ℝ) = (u.length : ℝ) + v.length := by
    push_cast [List.length_append]; ring
  have hε0 : 0 ≤ ε := by
    by_contra h
    push Not at h
    nlinarith [Nat.cast_nonneg (α := ℝ) u.length,
      Nat.cast_nonneg (α := ℝ) v.length]
  rw [hcount, hlen]
  calc |(u.count s : ℝ) + v.count s - ((u.length : ℝ) + v.length) / b|
      = |((u.count s : ℝ) - u.length / b) + ((v.count s : ℝ) - v.length / b)| := by
        ring_nf
    _ ≤ |(u.count s : ℝ) - u.length / b| + |(v.count s : ℝ) - v.length / b| :=
        abs_add_le _ _
    _ < ε * v.length + ε * v.length := by
        exact add_lt_add_of_le_of_lt (hu.trans hshort.le) hcv
    _ ≤ 2 * ε * ((u.length : ℝ) + v.length) := by
        have h0 : (0 : ℝ) ≤ (u.length : ℝ) := Nat.cast_nonneg _
        nlinarith

/-- Bridge between the two block representations: `digitCount` on
`u : Fin k → Fin b` (Lemma 8) is `List.count` on `List.ofFn u` (Lemma 9). -/
theorem digitCount_eq_count_ofFn {b : ℕ} (s : Fin b) :
    ∀ {k : ℕ} (u : Fin k → Fin b), digitCount s u = (List.ofFn u).count s := by
  intro k
  induction k with
  | zero => intro u; simp [digitCount]
  | succ n ih =>
    intro u
    rw [digitCount, Fin.sum_univ_succ, List.ofFn_succ, List.count_cons,
      ← ih (fun i => u i.succ)]
    simp [digitCount, beq_iff_eq, add_comm]

end NormalNumbers
