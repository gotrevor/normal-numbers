import NormalNumbers.CastingOut

/-!
# The exact digit identity for a Lambert value

`windowDigitSum_lambert_modEq` (in `CastingOut`) says the window digit sum is the weight sum plus
a boundary carry difference, MODULO `b − 1`.  Here we record the sharper, unreduced fact at window
length one:

    d_n = w(n+1) + c_{n+1} − b · c_n                              (`digitOf_lambertVal`)

with `c_N = carry b w N = ⌊Σ_{k>N} w(k) b^{N−k}⌋` — an identity in `ℤ`, no modulus.  This is what
decides which arithmetic input the `L = 1` rung of C1-log needs: the digit is NOT `w(n+1)` plus a
small error.  `c_n` is of size `Σ_k w(n+k) b^{−k}`, which for `w = ω` is of size `log log n`, so the
carry difference is a difference of two large, strongly correlated quantities.  Moreover `c_n` is
a *floor*, hence depends on `w(n+1), w(n+2), …` to depth `K` with `b^{−K} · max w → 0`, i.e.
`K ≍ log log n` for `w = ω`.  See `SwingC1Log.lean` for the resulting hypothesis.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

variable {b : ℕ} {w : ℕ → ℕ}

theorem lambertVal_nonneg (b : ℕ) (w : ℕ → ℕ) : 0 ≤ lambertVal b w := by
  unfold lambertVal
  exact tsum_nonneg fun m => by positivity

/-- With at most linear weights and `b ≥ 3` the Lambert value lies in `[0,1)`:
`Σ m/bᵐ = b/(b−1)² ≤ 3/4`. -/
theorem lambertVal_lt_one (b : ℕ) (hb : 3 ≤ b) (w : ℕ → ℕ) (hw : ∀ m, w m ≤ m) :
    lambertVal b w < 1 := by
  have hb3 : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  set r : ℝ := 1 / (b : ℝ) with hr
  have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
  have hr0 : 0 ≤ r := by positivity
  have hrlt : r < 1 := by rw [hr, div_lt_one hb0]; linarith
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hgeom : ∑' n : ℕ, (n : ℝ) * r ^ n = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hsum : Summable (fun n : ℕ => (n : ℝ) * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hnorm |>.congr (fun n => by rw [pow_one])
  have hle : lambertVal b w ≤ ∑' n : ℕ, (n : ℝ) * r ^ n := by
    unfold lambertVal
    refine Summable.tsum_le_tsum (fun m => ?_) (summable_lambert b (by omega) w hw) hsum
    have hwm : (w m : ℝ) ≤ m := by exact_mod_cast hw m
    have : (m : ℝ) * r ^ m = (m : ℝ) / (b : ℝ) ^ m := by
      rw [hr, div_pow, one_pow]; ring
    rw [this]
    gcongr
  refine lt_of_le_of_lt hle ?_
  rw [hgeom, hr]
  rw [div_lt_one (by positivity)]
  have h1 : (1 : ℝ) - 1 / (b : ℝ) = ((b : ℝ) - 1) / (b : ℝ) := by field_simp
  rw [h1, div_pow]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hb3]

theorem fract_lambertVal (b : ℕ) (hb : 3 ≤ b) (w : ℕ → ℕ) (hw : ∀ m, w m ≤ m) :
    Int.fract (lambertVal b w) = lambertVal b w :=
  Int.fract_eq_self.mpr ⟨lambertVal_nonneg b w, (lambertVal_lt_one b hb w hw)⟩

/-- The integer head `H_N = Σ_{m ≤ N} w(m) b^{N−m}` satisfies `H_{N+1} = b·H_N + w(N+1)`. -/
theorem head_succ (b : ℕ) (w : ℕ → ℕ) (N : ℕ) :
    (∑ m ∈ range (N + 2), w m * b ^ (N + 1 - m))
      = b * (∑ m ∈ range (N + 1), w m * b ^ (N - m)) + w (N + 1) := by
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [show N + 1 - m = (N - m) + 1 by omega, pow_succ]
    ring
  · simp

/-- **The exact digit identity.**  For `x = Σ w(m)/bᵐ` with `w m ≤ m` and `b ≥ 3`, the `n`-th
base-`b` digit of `x` is `w(n+1) + c_{n+1} − b·c_n`, an identity in `ℤ` with no modulus. -/
theorem digitOf_lambertVal (b : ℕ) (hb : 3 ≤ b) (w : ℕ → ℕ) (hw : ∀ m, w m ≤ m) (n : ℕ) :
    (digitOf b (Int.fract (lambertVal b w)) n : ℤ)
      = (w (n + 1) : ℤ) + carry b w (n + 1) - (b : ℤ) * carry b w n := by
  have hb2 : 2 ≤ b := by omega
  set x := lambertVal b w with hx
  rw [fract_lambertVal b hb w hw]
  have hrec := floor_mul_pow_succ b hb2 x (lambertVal_nonneg b w) n
  have h1 := floor_lambertVal_mul_pow b hb2 w hw (n + 1)
  have h2 := floor_lambertVal_mul_pow b hb2 w hw n
  have hhead : ((∑ m ∈ range (n + 2), w m * b ^ (n + 1 - m) : ℕ) : ℤ)
      = (b : ℤ) * ((∑ m ∈ range (n + 1), w m * b ^ (n - m) : ℕ) : ℤ) + (w (n + 1) : ℤ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℤ)) (head_succ b w n)
  have h1' : ⌊x * (b : ℝ) ^ (n + 1)⌋
      = (b : ℤ) * ((∑ m ∈ range (n + 1), w m * b ^ (n - m) : ℕ) : ℤ) + (w (n + 1) : ℤ)
        + carry b w (n + 1) := by
    rw [h1, show n + 1 + 1 = n + 2 by omega, hhead]
  rw [h1', h2] at hrec
  linarith [hrec]

end NormalNumbers.CastingOut
