/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.MahlerLowerBoundBackground

/-!
# Lower bounds for blocks of length `k ≥ 2` from a finite certificate 🧮

`mahler_lower_bound_bg_digit` (`MahlerLowerBoundBackground.lean`) turns the
background+burst family into a `decide`-able certificate for a single DIGIT.
This file does the same for a BLOCK of any length `k`: once the
background-plus-burst fits in `D` digits, the top `k` digits at every distance
`d ≥ D + k` are all the background digit `b`, so the infinite family of cell
conditions is a finite check over `d ≤ D + k` plus "the all-`b` block is not
`W`" (`mahler_lower_bound_bg_block`).

First instance, the first prime-base lower bound at `k = 2`:

* `mahler_lower_bound_base5_k2` — **`M(5,2) ≥ 44`** (exact value `48`; the
  witness `2/4 + 105·Σ 5^(−i!)`, block `44`).
* `mahler_lower_bound_base7_k2` — **`M(7,2) ≥ 103`** (witness
  `4/6 + 42·Σ 7^(−i!)`, block `16`).

Why it matters: `MahlerQuarter.lean` proves `M(g,1) ≤ g²/4 + O(g)` and the
exact census sits there, but at `k = 2` the exact values `M(3,2) = 8`,
`M(5,2) = 48` and `M_{00}(7,2) ≥ 176` are `0.30, 0.38, 0.51` of `g^(k+1)` —
ABOVE `1/4` and climbing.  The `k ≥ 2` constant is a different question, and
its lower side starts here.
-/

namespace NormalNumbers.Mahler

/-- `repunit g (e + k) = repunit g e + g^e · repunit g k`. -/
theorem repunit_add (g e k : ℕ) :
    repunit g (e + k) = repunit g e + g ^ e * repunit g k := by
  induction k with
  | zero => simp [repunit]
  | succ k ih =>
      rw [show e + (k + 1) = (e + k) + 1 from rfl]
      simp only [repunit, Finset.sum_range_succ] at ih ⊢
      rw [ih, pow_add]; ring

/-- The background block is below `g^k`. -/
theorem background_block_lt (g b k : ℕ) (hg : 2 ≤ g) (hbg : b + 1 ≤ g) :
    b * repunit g k < g ^ k := by
  have h := repunit_mul g k (by omega)
  have : b * repunit g k ≤ (g - 1) * repunit g k := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **The stabilized block.**  At distance `j + k` with `j ≥ D`, the top `k`
digits of the order-`(j+k)` residue are all the background digit `b`. -/
theorem bgResidue_block_stab (g b N D k j : ℕ) (hg : 2 ≤ g) (hbg : b + 1 ≤ g)
    (hD : b * repunit g D + N < g ^ D) (hj : D ≤ j) :
    ((b * repunit g (j + k) + N) % g ^ (j + k)) / g ^ j = b * repunit g k := by
  have hlt : b * repunit g j + N < g ^ j := repunit_burst_lt g b N D hg hbg hD j hj
  have hblk : b * repunit g k < g ^ k := background_block_lt g b k hg hbg
  have hsplit : b * repunit g (j + k) + N = g ^ j * (b * repunit g k) + (b * repunit g j + N) := by
    rw [repunit_add]; ring
  have hbnd : g ^ j * (b * repunit g k) + (b * repunit g j + N) < g ^ (j + k) := by
    rw [pow_add]
    have h1 : g ^ j * (b * repunit g k) + g ^ j ≤ g ^ j * g ^ k := by
      calc g ^ j * (b * repunit g k) + g ^ j = g ^ j * (b * repunit g k + 1) := by ring
        _ ≤ g ^ j * g ^ k := Nat.mul_le_mul_left _ hblk
    omega
  rw [hsplit, Nat.mod_eq_of_lt hbnd, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hlt]
  omega

/-- **Block lower bound from a finite certificate.**  `hcheck` is a bounded
check over `1 ≤ d ≤ D + k`, `m ≤ M`; `hstab` says the background-plus-burst
fits in `D` digits; `hback` says the all-background block is never the target.
Conclusion: `M(g,k) > M`. -/
theorem mahler_lower_bound_bg_block (g k a B M W D K : ℕ) (hg : 2 ≤ g) (hk : 1 ≤ k)
    (ha : a + 2 ≤ g) (hB : 1 ≤ B) (w : List ℕ) (hlen : w.length = k) (hwd : ∀ e ∈ w, e < g)
    (hWval : blockNatVal g w = W) (hMK : M * B ≤ g ^ K)
    (hstab : ∀ m, m ≤ M → (m * a % (g - 1)) * repunit g D + m * B < g ^ D)
    (hcheck : ∀ m, m ≤ M → ∀ d, 1 ≤ d → d ≤ D + k →
      (bgResidue g a B m d + 1) * g ^ k ≤ W * g ^ d ∨
      (W + 1) * g ^ d ≤ bgResidue g a B m d * g ^ k)
    (hback : ∀ m, m ≤ M → (m * a % (g - 1)) * repunit g k ≠ W) :
    Irrational (bgLiouville g a B) ∧ ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt g ((m : ℝ) * bgLiouville g a B) w n := by
  refine mahler_lower_bound_bg g k a B M K hg hk ha hB hMK w hlen hwd ?_
  intro m hm1 hmM d hd1
  rw [hWval]
  rcases le_or_gt d (D + k) with h | h
  · exact hcheck m hmM d hd1 h
  · obtain ⟨j, rfl⟩ : ∃ j, d = j + k := ⟨d - k, by omega⟩
    have hbg1 : m * a % (g - 1) + 1 ≤ g := by
      have : m * a % (g - 1) < g - 1 := Nat.mod_lt _ (by omega)
      omega
    have hT : bgResidue g a B m (j + k) / g ^ j = (m * a % (g - 1)) * repunit g k := by
      unfold bgResidue
      exact bgResidue_block_stab g (m * a % (g - 1)) (m * B) D k j hg hbg1 (hstab m hmM) (by omega)
    have hne : bgResidue g a B m (j + k) / g ^ j ≠ W := by rw [hT]; exact hback m hmM
    have hgj : 0 < g ^ j := by positivity
    have hpow : g ^ (j + k) = g ^ j * g ^ k := pow_add g j k
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      have : bgResidue g a B m (j + k) < W * g ^ j := by
        rw [Nat.div_lt_iff_lt_mul hgj] at hlt; omega
      rw [hpow]
      calc (bgResidue g a B m (j + k) + 1) * g ^ k ≤ (W * g ^ j) * g ^ k :=
            Nat.mul_le_mul_right _ (by omega)
        _ = W * (g ^ j * g ^ k) := by ring
    · right
      have : (W + 1) * g ^ j ≤ bgResidue g a B m (j + k) := by
        have h' : W + 1 ≤ bgResidue g a B m (j + k) / g ^ j := hgt
        rw [Nat.le_div_iff_mul_le hgj] at h'; omega
      rw [hpow]
      calc (W + 1) * (g ^ j * g ^ k) = ((W + 1) * g ^ j) * g ^ k := by ring
        _ ≤ bgResidue g a B m (j + k) * g ^ k := Nat.mul_le_mul_right _ this

/-- **`M(5,2) ≥ 44`** — the first prime-base lower bound at `k = 2` (exact
value `48`, so `0.35·g³` in the kernel against the `1/4` of `k = 1`).
Witness `2/4 + 105·Σ 5^(−i!)`, block `44`. -/
theorem mahler_lower_bound_base5_k2 :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 43 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 5 ((m : ℝ) * α) [4, 4] n :=
  ⟨_, mahler_lower_bound_bg_block 5 2 2 105 43 24 6 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) [4, 4] rfl (by decide) (by decide) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

/-- **`M(7,2) ≥ 103`** — `0.30·g³`.  Witness `4/6 + 42·Σ 7^(−i!)`, block `16`.
(The exact instrument gives `M_{00}(7,2) ≥ 176`, so at `k = 2` the extremal
orbit is NOT of background+burst shape — the family is exact at `k = 1` for
`g = 5, 7, 13, 23` but caps at `102` here.) -/
theorem mahler_lower_bound_base7_k2 :
    ∃ α : ℝ, Irrational α ∧ ∀ m : ℕ, 1 ≤ m → m ≤ 102 →
      ∃ N, ∀ n, N ≤ n → ¬ OccursAt 7 ((m : ℝ) * α) [1, 6] n :=
  ⟨_, mahler_lower_bound_bg_block 7 2 4 42 102 13 5 5 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) [1, 6] rfl (by decide) (by decide) (by norm_num)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

end NormalNumbers.Mahler
