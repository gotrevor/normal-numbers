/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerLowerBoundBackground

/-!
# `M(g,1)` for prime bases: the `Θ(g²)` lower side 🧮

Berend–Boshernitzan 1994 give, for odd `g ≥ 5`, the lower bound
`M(g,1) ≥ (3/2)(g − 1)` (their Theorem 3.3) — linear in `g` — and their only
super-linear bound, Theorem 3.1's `t(gᵏ − 1)`, needs a proper divisor `t ∣ g`
and so says nothing for prime bases.  Whether the true order for primes is
`g` or `g²` was the open half of this chapter.

**It is `g²`.**  The background+burst family `bgLiouville g a B` of
`MahlerLowerBoundBackground.lean` supplies quadratic witnesses, and the
certificates below are checked in the kernel:

| base `g` | witness `a`, `B`, digit `W` | bound proved | true `M(g,1)` | B–B Thm 3.3 |
|---|---|---|---|---|
| 5  | `2, 1, 1`     | `M(5,1)  ≥ 6`   | 6   | 6  |
| 7  | `2, 1, 1`     | `M(7,1)  ≥ 9`   | 9   | 9  |
| 11 | `2, 73, 10`   | `M(11,1) ≥ 24`  | 25  | 15 |
| 13 | `2, 958, 12`  | `M(13,1) ≥ 35`  | 35  | 18 |
| 23 | `2, 2549, 22` | `M(23,1) ≥ 120` | 120 | 33 |

("true `M(g,1)`" is the exact adder-machine value of
`experiments/mahler_exact_M.py`; it is *not* used in any proof.)  So the family
is **exact** at `g = 5, 7, 13, 23` and one short at `g = 11`, and at `g = 23`
it beats the linear bound by a factor `3.6` — `120 / 23² ≈ 0.227 ≈ 1/4`,
matching the empirical `M(g,1) ≈ ((g−1)/2)²`.

## Why `a = 2` is the right background

For odd `g` the background digit of `m · bgLiouville g 2 B` is
`b = 2m mod (g − 1)`, which is **even and `< g − 1`**.  Hence the digit
`W = g − 1` never arises from the background at all, for any `m`: the whole
multiplier budget is spent on the burst `m·B`, and `B` can be tuned to make
that budget quadratic.  This is exactly the mechanism `a = 0` (the pure
Liouville multiple of `MahlerLowerBoundGeneral.lean`) cannot use.
-/

namespace NormalNumbers.Mahler

/-- Certificate wrapper: package `mahler_lower_bound_bg_digit` for a fixed
base, background, burst, digit and budget. -/
theorem mahler_bg_witness (g a B M W D K : ℕ) (hg : 2 ≤ g) (ha : a + 2 ≤ g)
    (hB : 1 ≤ B) (hW : W < g) (hMK : M * B ≤ g ^ K)
    (hstab : ∀ m, m ≤ M → (m * a % (g - 1)) * repunit g D + m * B < g ^ D)
    (hdig : ∀ m, m ≤ M → ∀ d, d ≤ D → 1 ≤ d → bgResidue g a B m d / g ^ (d - 1) ≠ W)
    (hback : ∀ m, m ≤ M → m * a % (g - 1) ≠ W) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * α) [W] n := by
  obtain ⟨hirr, hmain⟩ :=
    mahler_lower_bound_bg_digit g a B M W D K hg ha hB hW hMK hstab hdig hback
  exact ⟨_, hirr, hmain⟩

/-- **`M(5,1) ≥ 6`** — exact.  Witness `2/4 + Σ 5^(−i!)`, digit `1`. -/
theorem mahler_lower_bound_base5 :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 5 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 5 ((m : ℝ) * α) [1] n :=
  mahler_bg_witness 5 2 1 5 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide)

/-- **`M(7,1) ≥ 9`** — exact.  Witness `2/6 + Σ 7^(−i!)`, digit `1`. -/
theorem mahler_lower_bound_base7 :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 8 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 7 ((m : ℝ) * α) [1] n :=
  mahler_bg_witness 7 2 1 8 1 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide) (by decide) (by decide)

/-- **`M(11,1) ≥ 24`** (true value 25), against B–B Thm 3.3's `15`. -/
theorem mahler_lower_bound_base11 :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 23 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 11 ((m : ℝ) * α) [10] n :=
  mahler_bg_witness 11 2 73 23 10 4 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **`M(13,1) ≥ 35`** — exact, against B–B Thm 3.3's `18`. -/
theorem mahler_lower_bound_base13 :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 34 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 13 ((m : ℝ) * α) [12] n :=
  mahler_bg_witness 13 2 958 34 12 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- **`M(23,1) ≥ 120`** — exact, against B–B Thm 3.3's `33`.  `120/23² ≈ 0.227`:
the quadratic order for a prime base, in the kernel. -/
theorem mahler_lower_bound_base23 :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 119 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 23 ((m : ℝ) * α) [22] n :=
  mahler_bg_witness 23 2 2549 119 22 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end NormalNumbers.Mahler
