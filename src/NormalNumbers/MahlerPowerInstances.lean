/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerLowerBoundPower
import NormalNumbers.MahlerMultiplierStrict

/-!
# The power family across bases: the universal Mahler constant is `≥ 0.84` 🧮

`mahler_lower_bound_power` gives `M(g,k) ≥ t(gᵏ − 1)` whenever `t·c = g^L` and
every guard block `s·c` (`s < t`) avoids the digit `g − 1`.  Scanning `L ≤ 5`
(`experiments/mahler_power_family_scan.py`) the best admissible `t` **matches
the exact adder-machine value of `M(g,1)`** at 13 of the 20 composite bases
`4 ≤ g ≤ 28`: `g = 4, 6, 8, 9, 10, 14, 15, 16, 18, 20, 22, 24, 26`.  So on
composite bases this family is not merely a lower bound — it appears to *be*
the extremal construction.

| `g` | `t`, `c`, `L` | `M(g,k) ≥` | `k = 1` | `/g²` | divisor family |
|---|---|---|---|---|---|
| 18 | `16, 6561, 4`  | `16(18ᵏ−1)` | `272` | **0.840** | `153` |
| 20 | `16, 25, 2`    | `16(20ᵏ−1)` | `304` | 0.760 | `190` |
| 22 | `16, 14641, 4` | `16(22ᵏ−1)` | `336` | 0.694 | `242` |
| 24 | `18, 32, 2`    | `18(24ᵏ−1)` | `414` | 0.719 | `276` |
| 26 | `16, 28561, 4` | `16(26ᵏ−1)` | `400` | 0.592 | `338` |

(`k = 1` column = the exact value of `M(g,1)`; the divisor column is
`mahler_lower_bound_divisor`'s `(g/2)(g−1)`.)

## The universal constant

`mahler_multiplier_lt` gives `M(g,k) < g^(k+1)` for every base — Berend–
Boshernitzan's open question, answered on the previous lap.  Base 18 gives the
matching lower side: `M(18,1) ≥ 272 = 0.840 · 18²`.  So writing

    C := sup over (g,k) of  M(g,k) / g^(k+1),

we now know `0.840 ≤ C ≤ 1` (`mahler_universal_constant_ge`).  Before this file
the best universal lower witness was the even-base divisor family's
`(g/2)(gᵏ − 1)`, i.e. `C ≥ 1/2 − o(1)`: the room for the universal constant is
cut by a factor `1.19`.
-/

namespace NormalNumbers.Mahler

/-- **`M(18,k) ≥ 16(18ᵏ − 1)`.**  `16 · 6561 = 18⁴` and none of the sixteen
guard blocks `s · 3⁸` (`s < 16`) has a base-18 digit `17`.  At `k = 1` this is
`272`, the exact value of `M(18,1)`, and `272 / 18² = 0.840`. -/
theorem mahler_lower_bound_base18 (k : ℕ) (hk : 1 ≤ k) :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < 18) ∧
      ∀ m : ℕ, 1 ≤ m → m + 1 ≤ 16 * (18 ^ k - 1) →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt 18 ((m : ℝ) * α) w n :=
  mahler_lower_bound_power 18 16 6561 k 4 (by norm_num) hk (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide)

/-- **`M(20,k) ≥ 16(20ᵏ − 1)`** (`16 · 25 = 20²`); `304` at `k = 1`, exact. -/
theorem mahler_lower_bound_base20 (k : ℕ) (hk : 1 ≤ k) :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < 20) ∧
      ∀ m : ℕ, 1 ≤ m → m + 1 ≤ 16 * (20 ^ k - 1) →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt 20 ((m : ℝ) * α) w n :=
  mahler_lower_bound_power 20 16 25 k 2 (by norm_num) hk (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide)

/-- **`M(22,k) ≥ 16(22ᵏ − 1)`** (`16 · 11⁴ = 22⁴`); `336` at `k = 1`, exact. -/
theorem mahler_lower_bound_base22 (k : ℕ) (hk : 1 ≤ k) :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < 22) ∧
      ∀ m : ℕ, 1 ≤ m → m + 1 ≤ 16 * (22 ^ k - 1) →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt 22 ((m : ℝ) * α) w n :=
  mahler_lower_bound_power 22 16 14641 k 4 (by norm_num) hk (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide)

/-- **`M(24,k) ≥ 18(24ᵏ − 1)`** (`18 · 32 = 24²`); `414` at `k = 1`, exact. -/
theorem mahler_lower_bound_base24 (k : ℕ) (hk : 1 ≤ k) :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < 24) ∧
      ∀ m : ℕ, 1 ≤ m → m + 1 ≤ 18 * (24 ^ k - 1) →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt 24 ((m : ℝ) * α) w n :=
  mahler_lower_bound_power 24 18 32 k 2 (by norm_num) hk (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide)

/-- **`M(26,k) ≥ 16(26ᵏ − 1)`** (`16 · 13⁴ = 26⁴`); `400` at `k = 1`, exact. -/
theorem mahler_lower_bound_base26 (k : ℕ) (hk : 1 ≤ k) :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = k ∧ (∀ d ∈ w, d < 26) ∧
      ∀ m : ℕ, 1 ≤ m → m + 1 ≤ 16 * (26 ^ k - 1) →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt 26 ((m : ℝ) * α) w n :=
  mahler_lower_bound_power 26 16 28561 k 4 (by norm_num) hk (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide)

/-- **The universal Mahler constant is at least `272/324 = 0.840…`.**  There is
an irrational `α` and a single base-18 digit `w` such that no multiplier
`m ≤ 271` puts `w` infinitely often into `m·α`.  Against
`mahler_multiplier_lt`'s `M(g,k) < g^(k+1)` this pins

    0.840 · g^(k+1)  ≤  sup M(g,k)  <  g^(k+1)

— the even-base divisor family only gave the factor `1/2`. -/
theorem mahler_universal_constant_ge :
    ∃ (α : ℝ) (w : List ℕ), Irrational α ∧ w.length = 1 ∧ (∀ d ∈ w, d < 18) ∧
      ∀ m : ℕ, 1 ≤ m → m ≤ 271 →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt 18 ((m : ℝ) * α) w n := by
  obtain ⟨α, w, hirr, hlen, hdig, hmain⟩ := mahler_lower_bound_base18 1 le_rfl
  exact ⟨α, w, hirr, hlen, hdig, fun m hm1 hm => hmain m hm1 (by norm_num; omega)⟩

end NormalNumbers.Mahler
