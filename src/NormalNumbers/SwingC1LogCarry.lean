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

/-! ## The carry is unbounded

This is the machine-checked reason no FIXED-depth arithmetic input can determine the digits of
`G4_b`: the carry `c_N` is unbounded, so the digit `d_n = w(n+1) + c_{n+1} − b·c_n` is not
`w(n+1)` plus a bounded error, and `c_N = ⌊Σ_k w(N+k) b^{−k}⌋` genuinely depends on the weights
to a depth that grows with `N`. -/

theorem summable_carry_tail (b : ℕ) (hb : 2 ≤ b) (w : ℕ → ℕ) (hw : ∀ m, w m ≤ m) (N : ℕ) :
    Summable (fun k : ℕ => (w (N + 1 + k) : ℝ) / (b : ℝ) ^ (k + 1)) := by
  have hb0 : (0 : ℝ) < b := by
    have : (2 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  have hs := ((summable_lambert b hb w hw).mul_right ((b : ℝ) ^ N)).comp_injective
    (f := fun m : ℕ => (w m : ℝ) / (b : ℝ) ^ m * (b : ℝ) ^ N)
    (i := fun k : ℕ => N + 1 + k) (fun k k' h => by simpa using h)
  refine hs.congr fun k => ?_
  simp only [Function.comp_apply]
  rw [show N + 1 + k = N + (k + 1) by omega, pow_add]
  have h1 : ((b : ℝ) ^ N) ≠ 0 := by positivity
  have h2 : ((b : ℝ) ^ (k + 1)) ≠ 0 := by positivity
  field_simp

theorem le_carry (b : ℕ) (hb : 2 ≤ b) (w : ℕ → ℕ) (hw : ∀ m, w m ≤ m) (N : ℕ) :
    ⌊(w (N + 1) : ℝ) / (b : ℝ)⌋ ≤ carry b w N := by
  unfold carry
  refine Int.floor_le_floor ?_
  have hs := summable_carry_tail b hb w hw N
  have h0 := hs.le_tsum 0 (fun k _ => by positivity)
  simpa using h0

/-- `ω` takes arbitrarily large values. -/
theorem exists_card_primeFactors_ge (C : ℕ) : ∃ m : ℕ, C ≤ m.primeFactors.card := by
  obtain ⟨S, hSsub, hScard⟩ := Nat.infinite_setOf_prime.exists_subset_card_eq C
  refine ⟨∏ p ∈ S, p, ?_⟩
  rw [Nat.primeFactors_prod (fun p hp => hSsub hp), hScard]

/-- **The carry is unbounded** for the prime-Lambert weight `ω`. -/
theorem carry_unbounded (b : ℕ) (hb : 2 ≤ b) (C : ℕ) :
    ∃ N : ℕ, (C : ℤ) ≤ carry b (fun m => m.primeFactors.card) N := by
  obtain ⟨m, hm⟩ := exists_card_primeFactors_ge (b * C + b)
  have hm1 : 1 ≤ m := by
    by_contra h
    interval_cases m <;> simp_all
  refine ⟨m - 1, le_trans ?_ (le_carry b hb _ NormalNumbers.PrimeLambert.card_primeFactors_le_self (m - 1))⟩
  rw [show m - 1 + 1 = m by omega]
  refine Int.le_floor.mpr ?_
  have hbR : (0 : ℝ) < b := by positivity
  have : ((b * C + b : ℕ) : ℝ) ≤ (m.primeFactors.card : ℝ) := by exact_mod_cast hm
  push_cast at this ⊢
  rw [le_div_iff₀ hbR]
  nlinarith [this]

/-- **The carry correction is unbounded.**  The digit at `n` is `< b`, while `w(n+1) = ω(n+1)` is
unbounded, so by `digitOf_lambertVal` the correction `b·c_n − c_{n+1} = w(n+1) − d_n` takes
arbitrarily large values.  Hence the digit is NOT the weight up to a bounded error: any route to
the `L = 1` rung that treats the carries as a bounded perturbation of `ω(n+1)` is dead. -/
theorem carry_correction_unbounded (b : ℕ) (hb : 3 ≤ b) (C : ℕ) :
    ∃ n : ℕ, (C : ℤ) ≤ (b : ℤ) * carry b (fun m => m.primeFactors.card) n
        - carry b (fun m => m.primeFactors.card) (n + 1) := by
  obtain ⟨m, hm⟩ := exists_card_primeFactors_ge (C + b)
  set w : ℕ → ℕ := fun m => m.primeFactors.card with hwdef
  have hw : ∀ m, w m ≤ m := fun m => NormalNumbers.PrimeLambert.card_primeFactors_le_self m
  have hm1 : 1 ≤ m := by
    by_contra h
    interval_cases m <;> simp_all
  refine ⟨m - 1, ?_⟩
  rw [show m - 1 + 1 = m by omega]
  have hid := digitOf_lambertVal b hb w hw (m - 1)
  rw [show m - 1 + 1 = m by omega] at hid
  have hdlt : digitOf b (Int.fract (lambertVal b w)) (m - 1) < b := by
    unfold digitOf
    exact Nat.mod_lt _ (by omega)
  have hdlt' : (digitOf b (Int.fract (lambertVal b w)) (m - 1) : ℤ) < (b : ℤ) := by
    exact_mod_cast hdlt
  have hmC : ((C + b : ℕ) : ℤ) ≤ (w m : ℤ) := by exact_mod_cast hm
  push_cast at hmC
  linarith [hid, hdlt', hmC]

end NormalNumbers.CastingOut
