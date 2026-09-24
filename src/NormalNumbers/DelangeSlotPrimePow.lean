import NormalNumbers.DelangeSlotIdentity

/-!
# L2's engine: summing a von-Mangoldt weight over the prime-power rectangle

The L2 error splits into two pieces, both of the shape `∑_{d ≤ N} Λ d · w d` with `w ≥ 0`.
Neither is termwise summable over `ℕ` (the chain `d = 2^j` decays only geometrically in `d`),
so the sums must be reindexed by the pair `(p, j)` with `d = p^j`.  `sum_le_primePow_rectangle`
does that once and for all: `d ↦ (d.minFac, Nat.log d.minFac d)` is injective on prime powers,
lands in `T ×ˢ Icc 1 J` with `J = Nat.log 2 N`, and every weight is nonnegative, so the sum is
bounded by the sum over the whole rectangle.  The rectangle then factorises into a geometric
series in `j` times `∑_n log n / n²` (resp. `∑_{n ≤ P} log n / n`).
-/

open Finset ArithmeticFunction

namespace NormalNumbers.DelangeSlot

/-- The exponent of a prime power, read off as `Nat.log minFac`. -/
lemma primePow_spec {d : ℕ} (hd : IsPrimePow d) :
    ∃ k, 0 < k ∧ k ≤ Nat.log 2 d ∧ d = d.minFac ^ k ∧ Nat.log d.minFac d = k := by
  obtain ⟨k, hkle, hk0, hk⟩ := (isPrimePow_nat_iff_bounded_log_minFac d).1 hd
  have hp : d.minFac.Prime := Nat.minFac_prime hd.ne_one
  have h1 : 1 < d.minFac := hp.one_lt
  refine ⟨k, hk0, hkle, hk, ?_⟩
  nth_rewrite 2 [hk]
  exact Nat.log_pow h1 k

/-- A prime power is recovered from `(minFac, Nat.log minFac)`. -/
lemma primePow_minFac_pow_log {d : ℕ} (hd : IsPrimePow d) :
    d.minFac ^ (Nat.log d.minFac d) = d := by
  obtain ⟨k, _, _, hk, hlog⟩ := primePow_spec hd
  rw [hlog, ← hk]

/-- The exponent `Nat.log minFac d` of a prime power `d ≤ N` lies in `[1, Nat.log 2 N]`. -/
lemma primePow_log_mem {d N : ℕ} (hd : IsPrimePow d) (hdN : d ≤ N) :
    1 ≤ Nat.log d.minFac d ∧ Nat.log d.minFac d ≤ Nat.log 2 N := by
  obtain ⟨k, hk0, hkle, _, hlog⟩ := primePow_spec hd
  exact ⟨by omega, by rw [hlog]; exact le_trans hkle (Nat.log_mono_right hdN)⟩

/-- **The rectangle bound.**  Any nonnegative weight supported on prime powers `≤ N` is
dominated by the sum over the rectangle `T ×ˢ Icc 1 (Nat.log 2 N)`, where `T` collects the
admissible minimal prime factors. -/
lemma sum_le_primePow_rectangle {N J : ℕ} (hJ : Nat.log 2 N ≤ J)
    {s T : Finset ℕ} (hs : s ⊆ Ioc 0 N) (f : ℕ → ℝ) (G : ℕ → ℕ → ℝ)
    (hG : ∀ p i, 0 ≤ G p i)
    (hf0 : ∀ d ∈ s, ¬ IsPrimePow d → f d ≤ 0)
    (hfT : ∀ d ∈ s, IsPrimePow d → d.minFac ∈ T)
    (hfG : ∀ d ∈ s, IsPrimePow d → f d ≤ G d.minFac (Nat.log d.minFac d)) :
    ∑ d ∈ s, f d ≤ ∑ q ∈ T ×ˢ Icc 1 J, G q.1 q.2 := by
  classical
  set s' : Finset ℕ := s.filter (fun d => IsPrimePow d) with hs'
  have hstep1 : ∑ d ∈ s, f d ≤ ∑ d ∈ s', f d := by
    rw [hs', Finset.sum_filter]
    refine Finset.sum_le_sum fun d hd ↦ ?_
    by_cases h : IsPrimePow d
    · simp [h]
    · simpa [h] using hf0 d hd h
  have hinj : ∀ x ∈ s', ∀ y ∈ s',
      (fun d : ℕ => (d.minFac, Nat.log d.minFac d)) x
        = (fun d : ℕ => (d.minFac, Nat.log d.minFac d)) y → x = y := by
    intro x hx y hy hxy
    have hx' : IsPrimePow x := (Finset.mem_filter.1 hx).2
    have hy' : IsPrimePow y := (Finset.mem_filter.1 hy).2
    simp only [Prod.mk.injEq] at hxy
    calc x = x.minFac ^ Nat.log x.minFac x := (primePow_minFac_pow_log hx').symm
      _ = y.minFac ^ Nat.log y.minFac y := by rw [hxy.2, hxy.1]
      _ = y := primePow_minFac_pow_log hy'
  have hstep2 : ∑ d ∈ s', f d
      ≤ ∑ q ∈ s'.image (fun d : ℕ => (d.minFac, Nat.log d.minFac d)), G q.1 q.2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_le_sum fun d hd ↦ ?_
    exact hfG d (Finset.mem_filter.1 hd).1 (Finset.mem_filter.1 hd).2
  have hsubset : s'.image (fun d : ℕ => (d.minFac, Nat.log d.minFac d)) ⊆ T ×ˢ Icc 1 J := by
    intro q hq
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hq
    have hd' : IsPrimePow d := (Finset.mem_filter.1 hd).2
    have hds : d ∈ s := (Finset.mem_filter.1 hd).1
    have hdN : d ≤ N := (Finset.mem_Ioc.1 (hs hds)).2
    obtain ⟨h1, h2⟩ := primePow_log_mem hd' hdN
    exact Finset.mem_product.2 ⟨hfT d hds hd', Finset.mem_Icc.2 ⟨h1, le_trans h2 hJ⟩⟩
  exact le_trans (le_trans hstep1 hstep2)
    (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun q _ _ ↦ hG q.1 q.2))


/-! ### The two numerical inputs: a geometric series in `j`, and `∑ log n / n² < ∞`. -/

lemma geom_Icc_mul (r : ℝ) : ∀ J : ℕ, (1 - r) * ∑ i ∈ Icc 1 J, r ^ i = r - r ^ (J + 1) := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

/-- `∑_{i=1}^{J} r^i ≤ 2r` for `0 ≤ r ≤ 1/2`. -/
lemma geom_Icc_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (J : ℕ) :
    ∑ i ∈ Icc 1 J, r ^ i ≤ 2 * r := by
  have hid := geom_Icc_mul r J
  have hnn : 0 ≤ ∑ i ∈ Icc 1 J, r ^ i :=
    Finset.sum_nonneg fun i _ ↦ pow_nonneg hr0 i
  have htail : 0 ≤ r ^ (J + 1) := pow_nonneg hr0 _
  nlinarith [hid, hnn, htail]

/-- `∑_{i=1}^{J} r^{i+1} ≤ 2r²`. -/
lemma geom_Icc_succ_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (J : ℕ) :
    ∑ i ∈ Icc 1 J, r ^ (i + 1) ≤ 2 * r ^ 2 := by
  have h : ∑ i ∈ Icc 1 J, r ^ (i + 1) = r * ∑ i ∈ Icc 1 J, r ^ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [h]
  nlinarith [geom_Icc_le hr0 hr J, hr0]

/-- The pointwise telescoping majorant `log n / n² ≤ 4(1/√(n−1) − 1/√n)`. -/
lemma log_div_sq_le_telescope {n : ℕ} (hn : 2 ≤ n) :
    Real.log n / (n : ℝ) ^ 2 ≤ 4 * (1 / Real.sqrt ((n : ℝ) - 1) - 1 / Real.sqrt n) := by
  have hn2 : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := Real.sqrt n with hsdef
  set t : ℝ := Real.sqrt ((n : ℝ) - 1) with htdef
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
  have ht2 : t ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have ht0 : 0 < t := Real.sqrt_pos.2 (by linarith)
  have hts : t ≤ s := Real.sqrt_le_sqrt (by linarith)
  -- Step A: `log n ≤ 2 s`
  have hlogA : Real.log (n : ℝ) ≤ 2 * s := by
    have h1 : Real.log s = Real.log (n : ℝ) / 2 := Real.log_sqrt (by linarith)
    have h2 : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
    linarith
  -- Step B: `log n / n² ≤ 2 / (n s)`
  have hB : Real.log (n : ℝ) / (n : ℝ) ^ 2 ≤ 2 / ((n : ℝ) * s) := by
    have hn0 : (0:ℝ) < (n : ℝ) := by linarith
    have hss : s * s = (n : ℝ) := by rw [← sq]; exact hs2
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : Real.log (n : ℝ) * ((n : ℝ) * s) ≤ 2 * s * ((n : ℝ) * s) :=
      mul_le_mul_of_nonneg_right hlogA (by positivity)
    have h4 : 2 * s * ((n : ℝ) * s) = 2 * (n : ℝ) ^ 2 := by
      calc 2 * s * ((n : ℝ) * s) = 2 * (n : ℝ) * (s * s) := by ring
        _ = 2 * (n : ℝ) * (n : ℝ) := by rw [hss]
        _ = 2 * (n : ℝ) ^ 2 := by ring
    linarith
  -- Step C: `2 / (n s) ≤ 4 (1/t − 1/s)`
  have hst : (s - t) * (s + t) = 1 := by nlinarith [hs2, ht2]
  have hts2 : t * s ≤ (n : ℝ) := by nlinarith [hs2, hts, hs0, ht0]
  have hkey : t ≤ 2 * (s - t) * (n : ℝ) := by nlinarith [hst, hts2, hs0, ht0]
  have hC : 2 / ((n : ℝ) * s) ≤ 4 * (1 / t - 1 / s) := by
    have e : 4 * (1 / t - 1 / s) = 4 * (s - t) / (t * s) := by field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hkey, hs0]
  linarith

/-- `∑_{2 ≤ n ≤ N} log n / n² ≤ 4`, uniformly in `N`. -/
lemma sum_log_div_sq_le (N : ℕ) : ∑ n ∈ Icc 2 N, Real.log n / (n : ℝ) ^ 2 ≤ 4 := by
  rcases lt_or_ge N 2 with h | h
  · rw [Finset.Icc_eq_empty (by omega)]; norm_num
  have key : ∀ M : ℕ, 2 ≤ M →
      ∑ n ∈ Icc 2 M, Real.log n / (n : ℝ) ^ 2 ≤ 4 - 4 / Real.sqrt M := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      have hc : ((2:ℕ) : ℝ) = 2 := by norm_num
      have hmul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      have hs0 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      have hb : 4 / Real.sqrt 2 ≤ 3 := by
        rw [div_le_iff₀ hs0]; nlinarith
      have hset : (Icc 2 2 : Finset ℕ) = {2} := rfl
      rw [hset, Finset.sum_singleton, hc]
      linarith [Real.log_two_lt_d9, hb]
    | succ M hM ih =>
      have hstep := log_div_sq_le_telescope (n := M + 1) (by omega)
      have hcast : (((M + 1 : ℕ) : ℝ) - 1) = (M : ℝ) := by push_cast; ring
      rw [hcast] at hstep
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hM0 : (0:ℝ) < (M : ℝ) := by
        have : (2:ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        linarith
      have e1 : 4 * (1 / Real.sqrt (M : ℝ)) = 4 / Real.sqrt (M : ℝ) := by ring
      have e2 : 4 * (1 / Real.sqrt ((M + 1 : ℕ) : ℝ)) = 4 / Real.sqrt ((M + 1 : ℕ) : ℝ) := by
        ring
      have hstep' : Real.log ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) ^ 2
          ≤ 4 / Real.sqrt (M : ℝ) - 4 / Real.sqrt ((M + 1 : ℕ) : ℝ) := by
        calc Real.log ((M + 1 : ℕ) : ℝ) / ((M + 1 : ℕ) : ℝ) ^ 2
            ≤ 4 * (1 / Real.sqrt (M : ℝ) - 1 / Real.sqrt ((M + 1 : ℕ) : ℝ)) := hstep
          _ = 4 / Real.sqrt (M : ℝ) - 4 / Real.sqrt ((M + 1 : ℕ) : ℝ) := by ring
      linarith [ih, hstep']
  have h4 : (0:ℝ) ≤ 4 / Real.sqrt N := by positivity
  linarith [key N h]


/-! ### The two L2 error sums -/

private lemma G_nonneg (N : ℕ) (p i : ℕ) : 0 ≤ Real.log p * ((N : ℝ) / (p : ℝ) ^ i) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · have h1 : (1:ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have : 0 ≤ Real.log p := Real.log_nonneg h1
    positivity

/-- **The large-prime error sum.**  `∑_{d = p^j ≤ N} Λ d · ⌊N/(d p)⌋ ≤ 4 N`: the extra factor
`1/p` beyond `1/d` is exactly what makes this converge, and the `(p, j)` rectangle turns it into
`(∑_j 2^{-j}) · (∑_n log n/n²)`. -/
theorem sum_vonMangoldt_mul_div_minFac_le (N : ℕ) :
    ∑ d ∈ Ioc 0 N, Λ d * ((N / (d * d.minFac) : ℕ) : ℝ) ≤ 8 * N := by
  classical
  have hrect := sum_le_primePow_rectangle (N := N) (J := Nat.log 2 N) le_rfl
    (s := Ioc 0 N) (T := Icc 2 N) (subset_refl _)
    (f := fun d => Λ d * ((N / (d * d.minFac) : ℕ) : ℝ))
    (G := fun p i => Real.log p * ((N : ℝ) / (p : ℝ) ^ (i + 1)))
    (fun p i => G_nonneg N p (i + 1))
    (by
      intro d _ hd
      rw [vonMangoldt_eq_zero_iff.2 hd]
      simp)
    (by
      intro d hd hdp
      have hp : d.minFac.Prime := Nat.minFac_prime hdp.ne_one
      have hd0 : 0 < d := (Finset.mem_Ioc.1 hd).1
      have hdN : d ≤ N := (Finset.mem_Ioc.1 hd).2
      exact Finset.mem_Icc.2 ⟨hp.two_le, le_trans (Nat.minFac_le hd0) hdN⟩)
    (by
      intro d hd hdp
      have hp : d.minFac.Prime := Nat.minFac_prime hdp.ne_one
      have hpow : d.minFac ^ (Nat.log d.minFac d) = d := primePow_minFac_pow_log hdp
      have hlog : Λ d = Real.log d.minFac := by rw [vonMangoldt_apply, if_pos hdp]
      have hmul : d * d.minFac = d.minFac ^ (Nat.log d.minFac d + 1) := by
        rw [pow_succ, hpow]
      have hcast : ((N / (d * d.minFac) : ℕ) : ℝ)
          ≤ (N : ℝ) / ((d.minFac : ℝ) ^ (Nat.log d.minFac d + 1)) := by
        rw [hmul]
        calc ((N / (d.minFac ^ (Nat.log d.minFac d + 1)) : ℕ) : ℝ)
            ≤ (N : ℝ) / ((d.minFac ^ (Nat.log d.minFac d + 1) : ℕ) : ℝ) := Nat.cast_div_le
          _ = (N : ℝ) / ((d.minFac : ℝ) ^ (Nat.log d.minFac d + 1)) := by push_cast; ring
      rw [hlog]
      exact mul_le_mul_of_nonneg_left hcast (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)))
  refine hrect.trans ?_
  rw [Finset.sum_product]
  have hinner : ∀ n ∈ Icc 2 N,
      ∑ i ∈ Icc 1 (Nat.log 2 N), Real.log n * ((N : ℝ) / (n : ℝ) ^ (i + 1))
        ≤ 2 * (N : ℝ) * (Real.log n / (n : ℝ) ^ 2) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.1 hn).1
    have hn2R : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hr0 : (0:ℝ) ≤ 1 / (n : ℝ) := by positivity
    have hr : 1 / (n : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
    have hrw : ∀ i : ℕ, Real.log n * ((N : ℝ) / (n : ℝ) ^ (i + 1))
        = (Real.log n * N) * (1 / (n : ℝ)) ^ (i + 1) := by
      intro i; rw [div_pow]; ring
    rw [Finset.sum_congr rfl (fun i _ ↦ hrw i), ← Finset.mul_sum]
    calc (Real.log n * N) * ∑ i ∈ Icc 1 (Nat.log 2 N), (1 / (n : ℝ)) ^ (i + 1)
        ≤ (Real.log n * N) * (2 * (1 / (n : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left (geom_Icc_succ_le hr0 hr _) (by positivity)
      _ = 2 * (N : ℝ) * (Real.log n / (n : ℝ) ^ 2) := by
          rw [div_pow]; ring
  calc ∑ n ∈ Icc 2 N, ∑ i ∈ Icc 1 (Nat.log 2 N), Real.log n * ((N : ℝ) / (n : ℝ) ^ (i + 1))
      ≤ ∑ n ∈ Icc 2 N, 2 * (N : ℝ) * (Real.log n / (n : ℝ) ^ 2) := Finset.sum_le_sum hinner
    _ = 2 * (N : ℝ) * ∑ n ∈ Icc 2 N, Real.log n / (n : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 2 * (N : ℝ) * 4 :=
        mul_le_mul_of_nonneg_left (sum_log_div_sq_le N) (by positivity)
    _ = 8 * N := by ring


/-- **The small-prime error sum.**  The block of prime powers with `minFac ≤ P` costs
`O_P(N)`: here `P` is fixed, so the whole `∑_{n ≤ P} log n / n` is a constant. -/
theorem sum_vonMangoldt_smooth_le (N P : ℕ) :
    ∑ d ∈ Ioc 0 N, (if d.minFac ≤ P then Λ d * ((N / d : ℕ) : ℝ) else 0)
      ≤ 2 * (N : ℝ) * ∑ n ∈ Icc 2 P, Real.log n / (n : ℝ) := by
  classical
  have hrect := sum_le_primePow_rectangle (N := N) (J := Nat.log 2 N) le_rfl
    (s := Ioc 0 N) (T := Icc 2 N) (subset_refl _)
    (f := fun d => if d.minFac ≤ P then Λ d * ((N / d : ℕ) : ℝ) else 0)
    (G := fun p i => if p ≤ P then Real.log p * ((N : ℝ) / (p : ℝ) ^ i) else 0)
    (by
      intro p i
      by_cases h : p ≤ P
      · simpa [h] using G_nonneg N p i
      · simp [h])
    (by
      intro d _ hd
      rw [vonMangoldt_eq_zero_iff.2 hd]
      by_cases h : d.minFac ≤ P <;> simp [h])
    (by
      intro d hd hdp
      have hp : d.minFac.Prime := Nat.minFac_prime hdp.ne_one
      have hd0 : 0 < d := (Finset.mem_Ioc.1 hd).1
      have hdN : d ≤ N := (Finset.mem_Ioc.1 hd).2
      exact Finset.mem_Icc.2 ⟨hp.two_le, le_trans (Nat.minFac_le hd0) hdN⟩)
    (by
      intro d hd hdp
      have hp : d.minFac.Prime := Nat.minFac_prime hdp.ne_one
      have hpow : d.minFac ^ (Nat.log d.minFac d) = d := primePow_minFac_pow_log hdp
      have hlog : Λ d = Real.log d.minFac := by rw [vonMangoldt_apply, if_pos hdp]
      by_cases h : d.minFac ≤ P
      · simp only [h, if_pos, hlog]
        have hcast : ((N / d : ℕ) : ℝ)
            ≤ (N : ℝ) / ((d.minFac : ℝ) ^ (Nat.log d.minFac d)) := by
          have hdc : ((d.minFac : ℝ)) ^ (Nat.log d.minFac d) = (d : ℝ) := by
            exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hpow
          calc ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / (d : ℝ) := Nat.cast_div_le
            _ = (N : ℝ) / ((d.minFac : ℝ) ^ (Nat.log d.minFac d)) := by rw [hdc]
        exact mul_le_mul_of_nonneg_left hcast
          (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
      · simp [h])
  refine hrect.trans ?_
  rw [Finset.sum_product]
  have hinner : ∀ n ∈ Icc 2 N,
      ∑ i ∈ Icc 1 (Nat.log 2 N), (if n ≤ P then Real.log n * ((N : ℝ) / (n : ℝ) ^ i) else 0)
        ≤ (if n ≤ P then 2 * (N : ℝ) * (Real.log n / (n : ℝ)) else 0) := by
    intro n hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.1 hn).1
    have hn2R : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    by_cases h : n ≤ P
    · simp only [h, if_pos]
      have hr0 : (0:ℝ) ≤ 1 / (n : ℝ) := by positivity
      have hr : 1 / (n : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
      have hrw : ∀ i : ℕ, Real.log n * ((N : ℝ) / (n : ℝ) ^ i)
          = (Real.log n * N) * (1 / (n : ℝ)) ^ i := by
        intro i; rw [div_pow]; ring
      rw [Finset.sum_congr rfl (fun i _ ↦ hrw i), ← Finset.mul_sum]
      calc (Real.log n * N) * ∑ i ∈ Icc 1 (Nat.log 2 N), (1 / (n : ℝ)) ^ i
          ≤ (Real.log n * N) * (2 * (1 / (n : ℝ))) :=
            mul_le_mul_of_nonneg_left (geom_Icc_le hr0 hr _) (by positivity)
        _ = 2 * (N : ℝ) * (Real.log n / (n : ℝ)) := by field_simp
    · simp [h]
  calc ∑ n ∈ Icc 2 N, ∑ i ∈ Icc 1 (Nat.log 2 N),
          (if n ≤ P then Real.log n * ((N : ℝ) / (n : ℝ) ^ i) else 0)
      ≤ ∑ n ∈ Icc 2 N, (if n ≤ P then 2 * (N : ℝ) * (Real.log n / (n : ℝ)) else 0) :=
        Finset.sum_le_sum hinner
    _ = ∑ n ∈ (Icc 2 N).filter (fun n => n ≤ P), 2 * (N : ℝ) * (Real.log n / (n : ℝ)) := by
        rw [Finset.sum_filter]
    _ ≤ ∑ n ∈ Icc 2 P, 2 * (N : ℝ) * (Real.log n / (n : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
          exact ⟨hn.1.1, hn.2⟩
        · intro n hn _
          have : (2:ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hn).1
          have : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
          positivity
    _ = 2 * (N : ℝ) * ∑ n ∈ Icc 2 P, Real.log n / (n : ℝ) := by rw [Finset.mul_sum]

end NormalNumbers.DelangeSlot
