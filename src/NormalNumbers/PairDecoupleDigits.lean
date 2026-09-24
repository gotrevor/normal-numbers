import NormalNumbers.PairDecoupleVdC

/-!
# The `b`-adic digit form: the crux is a root-of-unity correlation along shifted forms

`omegaTail b N = Σ_{k≥0} ω(N+1+k)·b^{−(k+1)}` is, by definition, a `b`-adic digit sum.  So the
pair difference is

`pairTail b p q n = Σ_{k≥0} (ω(pn+1+k) − ω(qn+1+k))·b^{−(k+1)}`,

and with `t = m/b` the phase of the `k`-th digit is a power of the ROOT OF UNITY
`ζ_k = e(m·b^{−(k+2)})`:

`e(t·(ω(pn+1+k) − ω(qn+1+k))·b^{−(k+1)}) = ζ_k^{ω(pn+1+k)} · conj(ζ_k^{ω(qn+1+k)})`.

Hence `e(t·pairTail)` is, after truncating the digits at `K`, a product of `2K` root-of-unity
powers of `ω` along the `2K` linear forms `pn+1+k`, `qn+1+k`.  Its mean is therefore a
**multi-point Elliott correlation** for the non-pretentious multiplicative function `ζ^ω`.

⚠️ **Correction to the lap-6 record.**  Only the LEADING digit is a two-point correlation (the
case Tao 2016 settles in logarithmic average).  The full statement needs all `K` digits, i.e. a
`2K`-point Elliott correlation, which is open even logarithmically.  The digit weights decay like
`b^{−k}` but `ω` is unbounded, so `K` must grow (slowly) with the range: `K ≳ log log log R`.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- `e(n·x) = e(x)^n`. -/
lemma phase_nat_mul (n : ℕ) (x : ℝ) : phase ((n : ℝ) * x) = (phase x) ^ n := by
  induction n with
  | zero => simp [phase]
  | succ n ih =>
      have : ((n + 1 : ℕ) : ℝ) * x = (n : ℝ) * x + x := by push_cast; ring
      rw [this, phase_add, ih, pow_succ, mul_comm]

/-- The `k`-th digit root of unity for the frequency `t`. -/
noncomputable def digitRoot (b : ℕ) (t : ℝ) (k : ℕ) : ℂ := phase (t / (b : ℝ) ^ (k + 1))

/-- **One digit of the pair phase is a root-of-unity correlation.** -/
theorem phase_digit (b : ℕ) (t : ℝ) (p q n k : ℕ) :
    phase (t * (((omegaNat (p * n + 1 + k) : ℝ) - omegaNat (q * n + 1 + k)) / (b : ℝ) ^ (k + 1)))
      = digitRoot b t k ^ omegaNat (p * n + 1 + k)
        * (starRingEnd ℂ) (digitRoot b t k ^ omegaNat (q * n + 1 + k)) := by
  have hsplit : t * (((omegaNat (p * n + 1 + k) : ℝ) - omegaNat (q * n + 1 + k))
        / (b : ℝ) ^ (k + 1))
      = (omegaNat (p * n + 1 + k) : ℝ) * (t / (b : ℝ) ^ (k + 1))
        - (omegaNat (q * n + 1 + k) : ℝ) * (t / (b : ℝ) ^ (k + 1)) := by
    ring
  rw [hsplit, ← phase_mul_conj_phase, phase_nat_mul, phase_nat_mul, digitRoot, map_pow]

/-- The digit truncation of the pair difference. -/
noncomputable def digitTrunc (b p q K n : ℕ) : ℝ :=
  ∑ k ∈ range K, (((omegaNat (p * n + 1 + k) : ℝ) - omegaNat (q * n + 1 + k))
    / (b : ℝ) ^ (k + 1))

/-- **The truncated pair phase is a `2K`-point root-of-unity correlation.**  This is the
machine-checked form of the identification: the crux is an Elliott-type correlation of the
non-pretentious multiplicative function `ζ^ω` along the `2K` linear forms `pn+1+k`, `qn+1+k`. -/
theorem phase_digitTrunc (b : ℕ) (t : ℝ) (p q K n : ℕ) :
    phase (t * digitTrunc b p q K n)
      = ∏ k ∈ range K, (digitRoot b t k ^ omegaNat (p * n + 1 + k)
          * (starRingEnd ℂ) (digitRoot b t k ^ omegaNat (q * n + 1 + k))) := by
  rw [digitTrunc, Finset.mul_sum, phase_sum]
  exact Finset.prod_congr rfl fun k _ => phase_digit b t p q n k

/-- **The pair difference in digit form.** -/
theorem pairTail_eq_tsum_digit (b : ℕ) (hb : 2 ≤ b) (p q n : ℕ) :
    pairTail b p q n
      = ∑' k : ℕ, (((omegaNat (p * n + 1 + k) : ℝ) - omegaNat (q * n + 1 + k))
          / (b : ℝ) ^ (k + 1)) := by
  have h1 := summable_omegaTail b hb (p * n)
  have h2 := summable_omegaTail b hb (q * n)
  rw [pairTail, omegaTail, omegaTail, ← h1.tsum_sub h2]
  exact tsum_congr fun k => by ring

/-! ### The truncation error -/

private lemma summable_digit (b : ℕ) (hb : 2 ≤ b) (p q n : ℕ) :
    Summable (fun k : ℕ => ((omegaNat (p * n + 1 + k) : ℝ) - omegaNat (q * n + 1 + k))
      / (b : ℝ) ^ (k + 1)) := by
  have h1 := summable_omegaTail b hb (p * n)
  have h2 := summable_omegaTail b hb (q * n)
  exact (h1.sub h2).congr fun k => by ring

/-- **The digit truncation error is exactly the tail of the digit series.** -/
theorem pairTail_sub_digitTrunc (b : ℕ) (hb : 2 ≤ b) (p q K n : ℕ) :
    pairTail b p q n - digitTrunc b p q K n
      = ∑' k : ℕ, (((omegaNat (p * n + 1 + (k + K)) : ℝ) - omegaNat (q * n + 1 + (k + K)))
          / (b : ℝ) ^ ((k + K) + 1)) := by
  have hsum := summable_digit b hb p q n
  have h := Summable.sum_add_tsum_nat_add (f := fun k : ℕ =>
    ((omegaNat (p * n + 1 + k) : ℝ) - omegaNat (q * n + 1 + k)) / (b : ℝ) ^ (k + 1)) K hsum
  rw [pairTail_eq_tsum_digit b hb p q n, digitTrunc, ← h]
  ring

/-- **The truncation error is bounded by the tail `ω`-mass.**  Everything beyond digit `K` is
controlled by `Σ_{k ≥ K} (ω(pn+1+k) + ω(qn+1+k))·b^{−(k+1)}`. -/
theorem norm_pairTail_sub_digitTrunc_le (b : ℕ) (hb : 2 ≤ b) (p q K n : ℕ)
    (hmass : Summable (fun k : ℕ => ((omegaNat (p * n + 1 + (k + K)) : ℝ)
      + omegaNat (q * n + 1 + (k + K))) / (b : ℝ) ^ ((k + K) + 1))) :
    |pairTail b p q n - digitTrunc b p q K n|
      ≤ ∑' k : ℕ, (((omegaNat (p * n + 1 + (k + K)) : ℝ) + omegaNat (q * n + 1 + (k + K)))
          / (b : ℝ) ^ ((k + K) + 1)) := by
  rw [pairTail_sub_digitTrunc b hb p q K n]
  have hsum : Summable (fun k : ℕ => ((omegaNat (p * n + 1 + (k + K)) : ℝ)
      - omegaNat (q * n + 1 + (k + K))) / (b : ℝ) ^ ((k + K) + 1)) :=
    (summable_nat_add_iff (f := fun k : ℕ =>
      ((omegaNat (p * n + 1 + k) : ℝ) - omegaNat (q * n + 1 + k)) / (b : ℝ) ^ (k + 1)) K).mpr
      (summable_digit b hb p q n)
  have habs := hsum.abs
  have step1 : |∑' k : ℕ, ((omegaNat (p * n + 1 + (k + K)) : ℝ)
      - omegaNat (q * n + 1 + (k + K))) / (b : ℝ) ^ ((k + K) + 1)|
      ≤ ∑' k : ℕ, |((omegaNat (p * n + 1 + (k + K)) : ℝ)
        - omegaNat (q * n + 1 + (k + K))) / (b : ℝ) ^ ((k + K) + 1)| := by
    have h := norm_tsum_le_tsum_norm (f := fun k : ℕ =>
      ((omegaNat (p * n + 1 + (k + K)) : ℝ) - omegaNat (q * n + 1 + (k + K)))
        / (b : ℝ) ^ ((k + K) + 1)) (by simp only [Real.norm_eq_abs]; exact habs)
    simp only [Real.norm_eq_abs] at h
    exact h
  refine step1.trans (Summable.tsum_le_tsum (fun k => ?_) habs hmass)
  have h1 : (0:ℝ) ≤ (omegaNat (p * n + 1 + (k + K)) : ℝ) := by positivity
  have h2 : (0:ℝ) ≤ (omegaNat (q * n + 1 + (k + K)) : ℝ) := by positivity
  rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (b : ℝ) ^ ((k + K) + 1))]
  have hbp : (0:ℝ) < (b : ℝ) ^ ((k + K) + 1) := by
    have : (0:ℝ) < (b:ℝ) := by
      have : (2:ℝ) ≤ (b:ℝ) := by exact_mod_cast hb
      linarith
    positivity
  rw [div_le_div_iff_of_pos_right hbp, abs_sub_le_iff]
  constructor <;> linarith

end NormalNumbers.CastingOut
