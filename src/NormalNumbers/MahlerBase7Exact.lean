/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerBase7Cert0
import NormalNumbers.MahlerBase7Cert1
import NormalNumbers.MahlerBase7Cert2
import NormalNumbers.MahlerBase7Cert3
import NormalNumbers.MahlerBase7Cert4
import NormalNumbers.MahlerBase7Cert5
import NormalNumbers.MahlerBase7Cert6
import NormalNumbers.MahlerPrimeLowerBound

/-!
# `M(7,1) = 9`: the Mahler constant, pinned exactly at a second prime base 🧮

`MahlerPrimeLowerBound.lean` proves `M(7,1) ≥ 9` (background+burst witness
`2/6 + 8·Σ 7^(−i!)`, digit `1`).  This file proves the matching **upper** half,

    for every irrational `X` and every base-7 digit `w`, some `m ≤ 9`
    has `w` occurring infinitely often in the base-7 expansion of `m·X`,

so `M(7,1) = 9` exactly, joining `M(3,1) = 2` (Berend–Boshernitzan 1994) and
`M(5,1) = 6` (`MahlerBase5Exact.lean`).  The general sandwich gives only
`5 ≤ M(7,1) ≤ 49`.

## The per-digit subset trick

The naive certificate uses all nine channels `x, 2x, …, 9x`, ambient
`9! = 362880` — `2.5M` kernel `gfamPred` evaluations per digit, far past what
one `decide +kernel` finishes (measured `> 45` min, no result).  But the
statement quantifies the multiplier *after* the digit: for each `w` separately
it suffices that **some** subset of `{1, …, 9}` collapses.  Searching per digit
(`experiments/mahler_subset_hunt_perdigit.py 7 9`) the minimal collapsing
subsets are

| `w` | multipliers | ambient | live |
|---|---|---|---|
| 0, 3, 6 | `1,2,3,4,5,6,8` | `5760` | `12, 18, 12` |
| 1, 5 | `1,3,4,5,6,9` | `3240` | `27` |
| 2, 4 | `1,2,3,4,5,6` | `720` | `16` |

for a total ambient of `25200` instead of `7 × 362880 = 2540160` — a **100×**
cut, which brings every digit back inside a single kernel `decide`.  (The
uniform-subset hunt had found nothing under `30000`, and correctly so: no
*single* subset that small works for all seven digits.  The gain is entirely in
letting the family depend on `w`.)

Emitted and independently re-verified by
`experiments/mahler_collapse_cert_perdigit.py`.
-/

namespace NormalNumbers.Adder

open NormalNumbers

/-- **`M(7,1) ≤ 9`.**  For every irrational `X` and every base-7 digit `w`
there is a multiplier `1 ≤ m ≤ 9` such that `w` occurs infinitely often in the
base-7 expansion of `m·X`. -/
theorem m7_mahler_upper (X : ℝ) (hX : Irrational X) (w : ℕ) (hw : w < 7) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 9 ∧ ∀ N, ∃ n, N ≤ n ∧ OccursAt 7 ((m : ℝ) * X) [w] n := by
  interval_cases w
  · obtain ⟨ch, hch, hio⟩ := signed_engine_g_single 7 (by norm_num) (m7Chans0 0) rfl
      m7_cert0 X hX (by decide) (by decide) (by decide)
    fin_cases hch <;>
      first
        | exact ⟨1, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨2, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨3, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨4, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨5, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨6, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨8, by norm_num, by norm_num, by simpa using hio⟩
  · obtain ⟨ch, hch, hio⟩ := signed_engine_g_single 7 (by norm_num) (m7Chans1 1) rfl
      m7_cert1 X hX (by decide) (by decide) (by decide)
    fin_cases hch <;>
      first
        | exact ⟨1, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨3, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨4, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨5, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨6, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨9, by norm_num, by norm_num, by simpa using hio⟩
  · obtain ⟨ch, hch, hio⟩ := signed_engine_g_single 7 (by norm_num) (m7Chans2 2) rfl
      m7_cert2 X hX (by decide) (by decide) (by decide)
    fin_cases hch <;>
      first
        | exact ⟨1, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨2, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨3, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨4, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨5, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨6, by norm_num, by norm_num, by simpa using hio⟩
  · obtain ⟨ch, hch, hio⟩ := signed_engine_g_single 7 (by norm_num) (m7Chans3 3) rfl
      m7_cert3 X hX (by decide) (by decide) (by decide)
    fin_cases hch <;>
      first
        | exact ⟨1, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨2, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨3, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨4, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨5, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨6, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨8, by norm_num, by norm_num, by simpa using hio⟩
  · obtain ⟨ch, hch, hio⟩ := signed_engine_g_single 7 (by norm_num) (m7Chans4 4) rfl
      m7_cert4 X hX (by decide) (by decide) (by decide)
    fin_cases hch <;>
      first
        | exact ⟨1, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨2, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨3, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨4, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨5, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨6, by norm_num, by norm_num, by simpa using hio⟩
  · obtain ⟨ch, hch, hio⟩ := signed_engine_g_single 7 (by norm_num) (m7Chans5 5) rfl
      m7_cert5 X hX (by decide) (by decide) (by decide)
    fin_cases hch <;>
      first
        | exact ⟨1, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨3, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨4, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨5, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨6, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨9, by norm_num, by norm_num, by simpa using hio⟩
  · obtain ⟨ch, hch, hio⟩ := signed_engine_g_single 7 (by norm_num) (m7Chans6 6) rfl
      m7_cert6 X hX (by decide) (by decide) (by decide)
    fin_cases hch <;>
      first
        | exact ⟨1, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨2, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨3, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨4, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨5, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨6, by norm_num, by norm_num, by simpa using hio⟩
        | exact ⟨8, by norm_num, by norm_num, by simpa using hio⟩

/-- **`M(7,1) = 9`, both halves.**  `9` multipliers always suffice
(`m7_mahler_upper`), and `8` do not (`Mahler.mahler_lower_bound_base7`, the
background+burst witness `2/6 + 8·Σ 7^(−i!)` with digit `1`).  So the optimal
universal Mahler multiplier for base 7, block length 1, is exactly `9`. -/
theorem mahler_M_seven_eq_nine :
    (∀ X : ℝ, Irrational X → ∀ w < 7, ∃ m : ℕ, 1 ≤ m ∧ m ≤ 9 ∧
        ∀ N, ∃ n, N ≤ n ∧ OccursAt 7 ((m : ℝ) * X) [w] n) ∧
    (∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 8 →
        ∃ N, ∀ n, N ≤ n → ¬ OccursAt 7 ((m : ℝ) * α) [1] n) :=
  ⟨fun X hX w hw => m7_mahler_upper X hX w hw, Mahler.mahler_lower_bound_base7⟩

end NormalNumbers.Adder
