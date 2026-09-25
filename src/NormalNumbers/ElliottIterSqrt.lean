import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The iterated integer square root

Leaf 2, Case B.  The repair of the dichotomy-scale obstruction truncates the window from below at
a scale `Z` which is a fixed *root* of `W`: small enough that the discarded harmonic mass
`≈ log Z` is a small fraction of `log W`, but large enough that `W ≤ (Z+1)^(2^j)` — which is what
makes the truncated thin scale a fixed power of `X` and hence bounds the Mertens loss.

Rather than introduce real `rpow` roots, `iterSqrt j` iterates `Nat.sqrt` `j` times, which gives
both bounds exactly and keeps everything in `ℕ`.

## Main results

* `iterSqrt_pow_le` — `(iterSqrt j W)^(2^j) ≤ W`.
* `lt_iterSqrt_succ_pow` — `W < (iterSqrt j W + 1)^(2^j)`.
-/

namespace NormalNumbers.ElliottIterSqrt

/-- `Nat.sqrt` iterated `j` times: an integer `2^j`-th root of `W`. -/
def iterSqrt : ℕ → ℕ → ℕ
  | 0, W => W
  | (j + 1), W => iterSqrt j (Nat.sqrt W)

@[simp] theorem iterSqrt_zero (W : ℕ) : iterSqrt 0 W = W := rfl

theorem iterSqrt_succ (j W : ℕ) : iterSqrt (j + 1) W = iterSqrt j (Nat.sqrt W) := rfl

/-- `(iterSqrt j W)^(2^j) ≤ W`. -/
theorem iterSqrt_pow_le (j : ℕ) : ∀ W : ℕ, (iterSqrt j W) ^ (2 ^ j) ≤ W := by
  induction j with
  | zero => intro W; simp
  | succ j ih =>
      intro W
      have h1 : (iterSqrt j (Nat.sqrt W)) ^ (2 ^ j) ≤ Nat.sqrt W := ih (Nat.sqrt W)
      have h2 : (Nat.sqrt W) ^ 2 ≤ W := by
        exact Nat.sqrt_le' W
      calc (iterSqrt (j + 1) W) ^ (2 ^ (j + 1))
          = ((iterSqrt j (Nat.sqrt W)) ^ (2 ^ j)) ^ 2 := by
            rw [iterSqrt_succ, ← pow_mul, pow_succ]
        _ ≤ (Nat.sqrt W) ^ 2 := Nat.pow_le_pow_left h1 2
        _ ≤ W := h2

/-- `W < (iterSqrt j W + 1)^(2^j)`. -/
theorem lt_iterSqrt_succ_pow (j : ℕ) : ∀ W : ℕ, W < (iterSqrt j W + 1) ^ (2 ^ j) := by
  induction j with
  | zero => intro W; simp
  | succ j ih =>
      intro W
      have h1 : Nat.sqrt W < (iterSqrt j (Nat.sqrt W) + 1) ^ (2 ^ j) := ih (Nat.sqrt W)
      have h2 : W < (Nat.sqrt W + 1) ^ 2 := by
        exact Nat.lt_succ_sqrt' W
      have h3 : Nat.sqrt W + 1 ≤ (iterSqrt j (Nat.sqrt W) + 1) ^ (2 ^ j) := h1
      calc W < (Nat.sqrt W + 1) ^ 2 := h2
        _ ≤ (((iterSqrt j (Nat.sqrt W) + 1) ^ (2 ^ j)) : ℕ) ^ 2 := Nat.pow_le_pow_left h3 2
        _ = (iterSqrt (j + 1) W + 1) ^ (2 ^ (j + 1)) := by
            rw [iterSqrt_succ, ← pow_mul, pow_succ]

theorem iterSqrt_le (j W : ℕ) : iterSqrt j W ≤ W := by
  have h := iterSqrt_pow_le j W
  by_contra hc
  push_neg at hc
  have h1 : iterSqrt j W ≤ (iterSqrt j W) ^ (2 ^ j) :=
    Nat.le_self_pow (by positivity) _
  omega

theorem one_le_iterSqrt {j W : ℕ} (hW : 1 ≤ W) : 1 ≤ iterSqrt j W := by
  by_contra hc
  push_neg at hc
  have hz : iterSqrt j W = 0 := by omega
  have := lt_iterSqrt_succ_pow j W
  rw [hz] at this
  simp at this
  omega

end NormalNumbers.ElliottIterSqrt
