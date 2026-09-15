/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.PowerBaseBlock
import NormalNumbers.G4EntropyWSqueeze

/-!
# `IsNormal b x → IsNormal (b^K) x`

The real-level form of `isNormalSequence_pow`.  The only thing to check is that the digit
sequence of `x` in base `b^K` **is** the blocking of its base-`b` digit sequence:
`digitOf (b^K) z j = blockOf b K (digitOf b z) j`, which is the statement that the `K`-block of
base-`b` digits starting at `K·j` is the base-`b^K` digit at `j`.  Both sides are read off the
same integer `⌊z·b^{K(j+1)}⌋`, so the proof is the nested-floor identity
`⌊z·b^e⌋ = ⌊z·b^{e+r}⌋ / b^r` together with `wordOf`/`valOf` inversion.

Corollaries: **`IsNormal 4 fullRealW`** and **`IsNormal (2^k) fullRealW`** for every `k ≥ 1`,
the base-`2^k` upgrade of `isNormal_fullRealW`.
-/

open Filter

namespace NormalNumbers.PowerBase

open NormalNumbers

/-! ### §1  Nested floors -/

lemma floorNat_step {b : ℕ} (hb : 0 < b) (z : ℝ) (e : ℕ) :
    ⌊z * (b : ℝ) ^ e⌋₊ = ⌊z * (b : ℝ) ^ (e + 1)⌋₊ / b := by
  have hbne : (b : ℝ) ≠ 0 := by positivity
  have hz : z * (b : ℝ) ^ e = (z * (b : ℝ) ^ (e + 1)) / (b : ℕ) := by
    push_cast
    field_simp
    ring
  rw [hz, Nat.floor_div_natCast]

lemma floorNat_pow {b : ℕ} (hb : 0 < b) (z : ℝ) (r : ℕ) : ∀ e : ℕ,
    ⌊z * (b : ℝ) ^ e⌋₊ = ⌊z * (b : ℝ) ^ (e + r)⌋₊ / b ^ r := by
  induction r with
  | zero => intro e; simp
  | succ r ih =>
      intro e
      rw [show e + (r + 1) = e + 1 + r from by omega, floorNat_step hb z e, ih (e + 1),
        Nat.div_div_eq_div_mul, ← pow_succ]

/-! ### §2  The digit identity -/

lemma digitOf_eq_floorNat (b : ℕ) (z : ℝ) (i : ℕ) :
    digitOf b z i = ⌊z * (b : ℝ) ^ (i + 1)⌋₊ % b := by
  rw [digitOf, Int.floor_toNat]

/-- **The `K`-block of base-`b` digits at `K·j` is the base-`b^K` digit at `j`.** -/
theorem blockOf_digitOf {b K : ℕ} (hb : 0 < b) (hK : 0 < K) (z : ℝ) (j : ℕ) :
    blockOf b K (digitOf b z) j = digitOf (b ^ K) z j := by
  set M : ℕ := ⌊z * (b : ℝ) ^ (K * (j + 1))⌋₊ with hM
  have hMK : digitOf (b ^ K) z j = M % b ^ K := by
    rw [digitOf_eq_floorNat, hM]
    congr 2
    push_cast
    rw [← pow_mul]
  have hlist : (List.range K).map (fun t => digitOf b z (K * j + t)) = wordOf b K M := by
    rw [wordOf]
    refine List.map_congr_left fun t ht => ?_
    rw [List.mem_range] at ht
    have hKj : K * (j + 1) = K * j + K := by ring
    have hexp : K * j + t + 1 + (K - 1 - t) = K * (j + 1) := by omega
    rw [digitOf_eq_floorNat]
    congr 1
    rw [hM, floorNat_pow hb z (K - 1 - t) (K * j + t + 1), hexp]
  rw [blockOf, hlist, ← wordOf_mod b K M hb,
    valOf_wordOf hb K (M % b ^ K) (Nat.mod_lt _ (by positivity)), hMK]

/-! ### §3  Normality in base `b^K` -/

/-- 🎯 **A number normal to base `b` is normal to base `b^K`.** -/
theorem isNormal_pow {b K : ℕ} (hb : 0 < b) (hK : 0 < K) {x : ℝ} (h : IsNormal b x) :
    IsNormal (b ^ K) x := by
  have hdig : ∀ j, digitOf b (Int.fract x) j < b := by
    intro j
    rw [digitOf]
    exact Nat.mod_lt _ hb
  have hseq := isNormalSequence_pow hb hK hdig h
  have hfun : blockOf b K (digitOf b (Int.fract x)) = digitOf (b ^ K) (Int.fract x) := by
    funext j
    exact blockOf_digitOf hb hK _ j
  rw [hfun] at hseq
  exact hseq

end NormalNumbers.PowerBase

namespace NormalNumbers.G4.Sched

open NormalNumbers NormalNumbers.PowerBase

/-- 🎯 **`fullRealW` is normal in base four.** -/
theorem isNormal_four_fullRealW : IsNormal 4 fullRealW := by
  have := isNormal_pow (b := 2) (K := 2) (by norm_num) (by norm_num) isNormal_fullRealW
  norm_num at this
  exact this

/-- 🎯 **`fullRealW` is normal in every base `2^k`, `k ≥ 1`.** -/
theorem isNormal_two_pow_fullRealW (k : ℕ) (hk : 0 < k) : IsNormal (2 ^ k) fullRealW :=
  isNormal_pow (by norm_num) hk isNormal_fullRealW

end NormalNumbers.G4.Sched
