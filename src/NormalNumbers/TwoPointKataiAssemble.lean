import NormalNumbers.TwoPointKataiRearrange

/-!
# Assembling the Kátai/BSZ inequality from its four obligations

Laps 7–9 proved, sorry-free, the four ingredients:

* `turanKubilius_abs` — `Σ_{n ≤ N} |ω_w(n) − L(w)| ≤ N √(2L(w))`;
* `sum_kataiOmega_mul_complex` — `Σ_n ω_w(n) F(n) = Σ_{p≤w} Σ_{m ≤ N/p} F(pm)`;
* `kataiMultiplicativeError` — peeling `f(pm) = f(p)f(m)` costs at most `2N`;
* `katai_cauchySchwarz` — the Cauchy–Schwarz whose diagonal is `Σ_p ⌊N/p⌋ = N L(w)`.

This file combines them into `katai_master`.  The pair term that comes out is the **truncated**
Gram sum `kataiPairGram`: the correlation of `a(p·)` with `a(q·)` over `m ≤ min(N/p, N/q)`, which
is what the argument genuinely produces — not the full-range `pairSum` of `TwoPointKataiSharp`.
That distinction is recorded honestly rather than papered over; see the note at the end.

The shape is the point:

    L(w)·‖Σ_{n≤N} f(n)a(n)‖  ≤  √( (N+1)·(N·L(w) + G) )  +  2N  +  N√(2 L(w)) ,

so after dividing by `N·L(w)` the pair term `G` is divided by `N·L(w)²` — the `L(w)²`
normalisation that laps 4–6 identified, now derived end-to-end in kernel.
-/

open Finset Filter Topology

namespace NormalNumbers.CastingOut

/-- `a(p·)` truncated to the range the Kátai argument sees. -/
noncomputable def kataiTrunc (a : ℕ → ℂ) (N p m : ℕ) : ℂ :=
  if m ∈ Finset.Ioc 0 (N / p) then a (p * m) else 0

lemma norm_kataiTrunc_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (N p m : ℕ) :
    ‖kataiTrunc a N p m‖ ≤ 1 := by
  unfold kataiTrunc; split
  · exact ha _
  · simpa using zero_le_one

/-- The truncated pair Gram sum: what the Cauchy–Schwarz actually leaves behind. -/
noncomputable def kataiPairGram (a : ℕ → ℂ) (w N : ℕ) : ℝ :=
  ∑ p ∈ primesLe w, ∑ q ∈ primesLe w,
    if p = q then 0 else ‖csGram (kataiTrunc a N) (N + 1) p q‖

lemma Ioc_div_subset_range (N p : ℕ) : Finset.Ioc 0 (N / p) ⊆ Finset.range (N + 1) := by
  intro m hm
  simp only [Finset.mem_Ioc] at hm
  simp only [Finset.mem_range]
  have := Nat.div_le_self N p
  omega

lemma sum_trunc_eq (a f : ℕ → ℂ) (N p : ℕ) :
    ∑ m ∈ Finset.range (N + 1), f m * kataiTrunc a N p m
      = ∑ m ∈ Finset.Ioc 0 (N / p), f m * a (p * m) := by
  classical
  rw [← Finset.sum_subset (Ioc_div_subset_range N p)
    (fun m _ hnot => by simp [kataiTrunc, hnot])]
  exact Finset.sum_congr rfl fun m hm => by simp [kataiTrunc, hm]

/-- The diagonal of the Cauchy–Schwarz is `Σ_{p ≤ w} ⌊N/p⌋ ≤ N·L(w)`. -/
lemma kataiDiagonal_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (w N : ℕ) :
    ∑ p ∈ primesLe w, ∑ m ∈ Finset.range (N + 1), ‖kataiTrunc a N p m‖ ^ 2
      ≤ (N : ℝ) * kataiPrimeRecip w := by
  classical
  have hrow : ∀ p ∈ primesLe w,
      ∑ m ∈ Finset.range (N + 1), ‖kataiTrunc a N p m‖ ^ 2 ≤ (N : ℝ) / p := by
    intro p hp
    have hppos : 0 < p := (prime_of_mem_primesLe hp).pos
    calc ∑ m ∈ Finset.range (N + 1), ‖kataiTrunc a N p m‖ ^ 2
        = ∑ m ∈ Finset.Ioc 0 (N / p), ‖a (p * m)‖ ^ 2 := by
          rw [← Finset.sum_subset (Ioc_div_subset_range N p)
            (fun m _ hnot => by simp [kataiTrunc, hnot])]
          exact Finset.sum_congr rfl fun m hm => by simp [kataiTrunc, hm]
      _ ≤ ∑ _m ∈ Finset.Ioc 0 (N / p), (1 : ℝ) := by
          refine Finset.sum_le_sum fun m _ => ?_
          nlinarith [ha (p * m), norm_nonneg (a (p * m))]
      _ = (((N / p : ℕ)) : ℝ) := by simp
      _ ≤ (N : ℝ) / p := Nat.cast_div_le
  calc ∑ p ∈ primesLe w, ∑ m ∈ Finset.range (N + 1), ‖kataiTrunc a N p m‖ ^ 2
      ≤ ∑ p ∈ primesLe w, (N : ℝ) / p := Finset.sum_le_sum hrow
    _ = (N : ℝ) * kataiPrimeRecip w := by
        rw [kataiPrimeRecip, Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by rw [mul_one_div]

/-- **THE KÁTAI/BSZ INEQUALITY, ASSEMBLED.** -/
theorem katai_master (w N : ℕ) (a f : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n)
    (hN : 2 * (primesLe w).card ≤ N) :
    kataiPrimeRecip w * ‖∑ n ∈ Finset.Ioc 0 N, f n * a n‖
      ≤ Real.sqrt (((N : ℝ) + 1)
            * ((N : ℝ) * kataiPrimeRecip w + kataiPairGram a w N))
        + 2 * (N : ℝ) + (N : ℝ) * Real.sqrt (2 * kataiPrimeRecip w) := by
  classical
  set L := kataiPrimeRecip w with hL
  set S : ℂ := ∑ n ∈ Finset.Ioc 0 N, f n * a n with hS
  set W : ℂ := ∑ n ∈ Finset.Ioc 0 N, (kataiOmega w n : ℂ) * (f n * a n) with hW
  set V : ℂ := ∑ p ∈ primesLe w, f p * ∑ m ∈ Finset.Ioc 0 (N / p), f m * a (p * m) with hV
  have hLnn : 0 ≤ L := Finset.sum_nonneg fun p _ => by positivity
  -- (1) Turán–Kubilius: `W` is close to `L · S`
  have h1 : ‖W - (L : ℂ) * S‖ ≤ (N : ℝ) * Real.sqrt (2 * L) := by
    have hrw : W - (L : ℂ) * S
        = ∑ n ∈ Finset.Ioc 0 N, ((kataiOmega w n : ℂ) - (L : ℂ)) * (f n * a n) := by
      rw [hW, hS, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hrw]
    refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum ?_) (turanKubilius_abs w N hN))
    intro n _
    rw [norm_mul, norm_mul]
    have hc : ‖(kataiOmega w n : ℂ) - (L : ℂ)‖ = |(kataiOmega w n : ℝ) - L| := by
      rw [show ((kataiOmega w n : ℂ) - (L : ℂ)) = (((kataiOmega w n : ℝ) - L : ℝ) : ℂ) by
        push_cast; ring]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hc, ← hL]
    calc |(kataiOmega w n : ℝ) - L| * (‖f n‖ * ‖a n‖)
        ≤ |(kataiOmega w n : ℝ) - L| * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact le_trans (mul_le_mul (hf n) (ha n) (norm_nonneg _) zero_le_one)
            (by norm_num)
      _ = |(kataiOmega w n : ℝ) - L| := by ring
  -- (2) + (3): `W` is close to `V`
  have h2 : ‖W - V‖ ≤ 2 * (N : ℝ) := by
    have hre : W = ∑ p ∈ primesLe w, ∑ m ∈ Finset.Ioc 0 (N / p), f (p * m) * a (p * m) :=
      sum_kataiOmega_mul_complex w N (fun n => f n * a n)
    rw [hre, hV]
    exact kataiMultiplicativeError w N a f ha hf hmul
  -- (4) Cauchy–Schwarz on `V`
  have h4 : ‖V‖ ^ 2 ≤ ((N : ℝ) + 1) * ((N : ℝ) * L + kataiPairGram a w N) := by
    have hVeq : V = ∑ p ∈ primesLe w, f p
        * ∑ m ∈ Finset.range (N + 1), f m * kataiTrunc a N p m := by
      rw [hV]
      exact Finset.sum_congr rfl fun p _ => by rw [sum_trunc_eq]
    rw [hVeq]
    refine le_trans (katai_cauchySchwarz (primesLe w) (N + 1) f f (kataiTrunc a N) hf hf) ?_
    have hcast : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := kataiDiagonal_le a ha w N
    simp only [kataiPairGram]
    linarith
  -- assemble
  have hVnn : (0 : ℝ) ≤ ‖V‖ := norm_nonneg _
  have hVle : ‖V‖ ≤ Real.sqrt (((N : ℝ) + 1) * ((N : ℝ) * L + kataiPairGram a w N)) := by
    have hrhs : 0 ≤ ((N : ℝ) + 1) * ((N : ℝ) * L + kataiPairGram a w N) :=
      le_trans (by positivity) h4
    calc ‖V‖ = Real.sqrt (‖V‖ ^ 2) := (Real.sqrt_sq hVnn).symm
      _ ≤ _ := Real.sqrt_le_sqrt h4
  have hLS : L * ‖S‖ = ‖(L : ℂ) * S‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLnn]
  rw [hLS]
  have hid : (L : ℂ) * S = V + (W - V) - (W - (L : ℂ) * S) := by ring
  rw [hid]
  calc ‖V + (W - V) - (W - (L : ℂ) * S)‖
      ≤ ‖V + (W - V)‖ + ‖W - (L : ℂ) * S‖ := norm_sub_le _ _
    _ ≤ ‖V‖ + ‖W - V‖ + ‖W - (L : ℂ) * S‖ := by linarith [norm_add_le V (W - V)]
    _ ≤ _ := by linarith [hVle, h2, h1]

end NormalNumbers.CastingOut
