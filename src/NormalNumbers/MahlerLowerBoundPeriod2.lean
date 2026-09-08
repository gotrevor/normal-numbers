/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerPrimeLowerBound
import NormalNumbers.Pillai

/-!
# Period-2 backgrounds: `M(19,1) ≥ 80` via base `g²` 🧮

The background+burst family `bgLiouville g a B = a/(g−1) + B·Σ g^(−i!)` has a
*single* repeating background digit.  For prime `p` the good background is
`1/Q`, `Q = (p−1)/2` (digit `2`, whose multiples `2r` are even and so never
`p − 1`).  The exact extremal automaton at `p = 19`, however, shadows
`9/10 = 1/(Q+1)`: a **period-2** background `(17, 1)` whose multiples
`(2r − 1, p − 2r)` never contain `p − 1` either.  The `1/Q` burst family
caps at `55 < 80` there; the `1/(Q+1)` family is exact.

No new engine is needed: a period-2 background in base `g` is a single-digit
background in base `g²`, and a base-`g` digit at position `2q + s` is a
sub-digit of the base-`g²` digit at `q` (`digitOf_pow_digitAt`, the Pillai
bridge).  So "digit `W` never occurs in base `g`" follows from "no base-`g²`
digit `c` with `c / g = W` or `c % g = W` occurs", a finite conjunction of
`mahler_lower_bound_bg_digit` certificates in base `g²` sharing one witness.

    mahler_lower_bound_base19 :  M(19,1) ≥ 80      (exact; census 80)

with `α = 36/360 + 22510·Σ 361^(−i!)`, i.e. background `1/10`.
-/

namespace NormalNumbers.Mahler

open scoped Nat

/-- A one-digit block occurs at `n` iff the digit at `n` is it. -/
theorem occursAt_singleton_iff (b : ℕ) (x : ℝ) (W n : ℕ) :
    OccursAt b x [W] n ↔ digitOf b (Int.fract x) n = W := by
  constructor
  · intro h
    have := h 0 (by simp)
    simpa using this
  · intro h j hj
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    simpa using h

/-- **Bridge.**  If digit `W` occurs in base `g` at position `n`, then the
base-`g²` digit at position `n / 2` is some `c < g²` with `c / g = W` or
`c % g = W`, and it occurs there. -/
theorem occursAt_sq_of_occursAt (g : ℕ) (hg : 2 ≤ g) (x : ℝ) (W n : ℕ)
    (h : OccursAt g x [W] n) :
    ∃ c, c < g ^ 2 ∧ (c / g = W ∨ c % g = W) ∧ OccursAt (g ^ 2) x [c] (n / 2) := by
  rw [occursAt_singleton_iff] at h
  set y := Int.fract x with hy
  have hy01 : y ∈ Set.Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  have hg2 : 2 ≤ g ^ 2 := by nlinarith
  refine ⟨digitOf (g ^ 2) y (n / 2), digitOf_lt _ hg2 _ _, ?_, ?_⟩
  · have hkey := digitOf_pow_digitAt g 2 hg (by norm_num) y hy01 (n / 2) (n % 2)
      (Nat.mod_lt _ (by norm_num))
    rw [show 2 * (n / 2) + n % 2 = n from Nat.div_add_mod n 2, h] at hkey
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · left
      rw [h0, show (2 : ℕ) - 1 - 0 = 1 from rfl, pow_one] at hkey
      have hlt : digitOf (g ^ 2) y (n / 2) / g < g := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc digitOf (g ^ 2) y (n / 2) < g ^ 2 := digitOf_lt _ hg2 _ _
          _ = g * g := pow_two g
      rw [Nat.mod_eq_of_lt hlt] at hkey
      exact hkey
    · right
      rw [h1] at hkey
      simpa using hkey
  · rw [occursAt_singleton_iff]

/-- **Period-2 background, `k = 1`.**  A base-`g²` background `a` (a two-digit
block) and burst `B` with the finite certificate checked against every
base-`g²` digit `c` containing `W` (`c / g = W` or `c % g = W`) gives an
irrational `α` none of whose multiples `1 ≤ m ≤ M` has digit `W` infinitely
often in base `g`. -/
theorem mahler_lower_bound_bg2_digit (g a B M W D K : ℕ) (hg : 2 ≤ g) (ha : a + 2 ≤ g ^ 2)
    (hB : 1 ≤ B) (hMK : M * B ≤ (g ^ 2) ^ K)
    (hstab : ∀ m, m ≤ M → (m * a % (g ^ 2 - 1)) * repunit (g ^ 2) D + m * B < (g ^ 2) ^ D)
    (hdig : ∀ m, m ≤ M → ∀ d, d ≤ D → 1 ≤ d →
      bgResidue (g ^ 2) a B m d / (g ^ 2) ^ (d - 1) / g ≠ W ∧
      bgResidue (g ^ 2) a B m d / (g ^ 2) ^ (d - 1) % g ≠ W)
    (hback : ∀ m, m ≤ M → m * a % (g ^ 2 - 1) / g ≠ W ∧ m * a % (g ^ 2 - 1) % g ≠ W) :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * α) [W] n := by
  have hg2 : 2 ≤ g ^ 2 := by nlinarith
  refine ⟨bgLiouville (g ^ 2) a B, irrational_bgLiouville _ a B hg2 hB, ?_⟩
  intro m hm1 hmM
  -- per base-`g²` digit `c` containing `W`, a threshold
  have hcert : ∀ c, c < g ^ 2 → (c / g = W ∨ c % g = W) →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt (g ^ 2) ((m : ℝ) * bgLiouville (g ^ 2) a B) [c] n := by
    intro c hc hcW
    refine (mahler_lower_bound_bg_digit (g ^ 2) a B M c D K hg2 ha hB hc hMK hstab ?_ ?_).2
      m hm1 hmM
    · intro m' hm' d hd hd1 heq
      rcases hcW with h | h
      · exact (hdig m' hm' d hd hd1).1 (by rw [heq, h])
      · exact (hdig m' hm' d hd hd1).2 (by rw [heq, h])
    · intro m' hm' heq
      rcases hcW with h | h
      · exact (hback m' hm').1 (by rw [heq, h])
      · exact (hback m' hm').2 (by rw [heq, h])
  classical
  let Nf : ℕ → ℕ := fun c =>
    if h : c < g ^ 2 ∧ (c / g = W ∨ c % g = W) then Classical.choose (hcert c h.1 h.2) else 0
  refine ⟨2 * (Finset.range (g ^ 2)).sup Nf + 2, fun n hn hocc => ?_⟩
  obtain ⟨c, hc, hcW, hocc2⟩ := occursAt_sq_of_occursAt g hg _ W n hocc
  have hspec := Classical.choose_spec (hcert c hc hcW)
  have hNc : Nf c = Classical.choose (hcert c hc hcW) := by
    simp only [Nf, dif_pos (And.intro hc hcW)]
  have hle : Nf c ≤ (Finset.range (g ^ 2)).sup Nf :=
    Finset.le_sup (f := Nf) (Finset.mem_range.2 hc)
  exact hspec (n / 2) (by omega) hocc2

/-- **`M(19,1) ≥ 80`** — exact (census `80`), against B–B Thm 3.3's `27` and
the `1/Q` family's `55`.  Background `36/360 = 1/10` (block `(1,17)` in base
`19`), burst `22510 = [3, 5, 6, 14]₁₉`, digit `18`. -/
theorem mahler_lower_bound_base19 :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 79 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 19 ((m : ℝ) * α) [18] n :=
  mahler_lower_bound_bg2_digit 19 36 22510 79 18 3 3 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end NormalNumbers.Mahler
