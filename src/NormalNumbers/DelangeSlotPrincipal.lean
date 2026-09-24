import NormalNumbers.DelangeSlotAP

/-!
# Rung 2, layer 3: the principal-character branch

The character decomposition of an additive twist mod `Q` leaves one piece that the
`ψ(x,χ) = o(x)` argument of `DelangeSlotChar` cannot handle: the **principal** character, where
`ψ(x,χ₀)` still has the main term `x`.  That piece is rung 1 run again with the extra
restriction `gcd(n,Q) = 1`, so it needs the full recursion (L4, L6, L7) — but all three of those
proofs used only `‖h k‖ ≤ 1`, so they transfer to `gfun` verbatim.

What is genuinely new here is the comparison `ψ(x,χ₀) = ψ(x) − O_Q(log x)`: the discarded
von-Mangoldt mass sits on the prime powers `p^j` with `p ∣ Q`, and for each such `p` it totals
`⌊log_p x⌋ · log p ≤ log x`.  Since `∑_{k ≤ N} log(N/k) ≤ N` (`sum_log_div_le`), the whole
correction is `O_Q(N)` and is absorbed by the chain's existing `O(N)` budget.
-/

open Finset ArithmeticFunction Filter Topology

namespace NormalNumbers.DelangeSlot

variable (χ : ℕ → ℂ) (z : ℂ) (P : ℕ)

/-- `m_g N = ∑_{k ≤ N} g k / k`. -/
noncomputable def mSumg (χ : ℕ → ℂ) (z : ℂ) (P N : ℕ) : ℂ := ∑ k ∈ Ioc 0 N, gfun χ z P k / k

/-- `σ_g k = S_g k / k`. -/
noncomputable def sigmaMeang (χ : ℕ → ℂ) (z : ℂ) (P k : ℕ) : ℂ := Sgsum χ z P k / k

lemma norm_sigmaMeang_le {χ : ℕ → ℂ} {z : ℂ} {P : ℕ} (hχ : ∀ n, ‖χ n‖ ≤ 1) (hz : ‖z‖ = 1)
    (k : ℕ) : ‖sigmaMeang χ z P k‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [sigmaMeang]
  · rw [sigmaMeang, norm_div, Complex.norm_natCast, div_le_one (by positivity)]
    exact norm_Sgsum_le hχ hz k

/-- **L4 for `g`.**  Identical to `exists_L4`; the proof only ever used `‖h k‖ ≤ 1`. -/
theorem exists_L4g {χ : ℕ → ℂ} {z : ℂ} {P : ℕ} (hχ : ∀ n, ‖χ n‖ ≤ 1) (hz : ‖z‖ = 1) :
    ∃ C : ℝ, ∀ N : ℕ,
      ‖(∑ k ∈ Ioc 0 N, gfun χ z P k * (psiN (N / k) : ℂ)) - (N : ℂ) * mSumg χ z P N‖
        ≤ C * N := by
  obtain ⟨C, hC0, hC⟩ := exists_sum_psi_sub_le
  refine ⟨C, fun N ↦ ?_⟩
  have hrw : (∑ k ∈ Ioc 0 N, gfun χ z P k * (psiN (N / k) : ℂ)) - (N : ℂ) * mSumg χ z P N
      = ∑ k ∈ Ioc 0 N, gfun χ z P k * ((psiN (N / k) - (N : ℝ) / (k : ℝ) : ℝ) : ℂ) := by
    rw [mSumg, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk0 : 0 < k := (mem_Ioc.1 hk).1
    have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk0.ne'
    push_cast
    field_simp
  rw [hrw]
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum (fun k _ ↦ ?_)) (hC N)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (abs_nonneg _) (norm_gfun_le hχ hz k)

lemma Sgsum_succ (χ : ℕ → ℂ) (z : ℂ) (P N : ℕ) :
    Sgsum χ z P (N + 1) = Sgsum χ z P N + gfun χ z P (N + 1) := by
  simp [Sgsum, Finset.sum_Ioc_succ_top (Nat.zero_le _)]

/-- **L6 for `g`.**  Discrete Abel summation. -/
theorem mSumg_eq (χ : ℕ → ℂ) (z : ℂ) (P N : ℕ) :
    mSumg χ z P N = sigmaMeang χ z P N + ∑ k ∈ Ico 1 N, sigmaMeang χ z P k / (k + 1 : ℂ) := by
  induction N with
  | zero => simp [mSumg, sigmaMeang, Sgsum]
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [mSumg, sigmaMeang, Sgsum, Finset.sum_Ioc_succ_top]
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hN1 : ((N : ℂ) + 1) ≠ 0 := by
      have : ((N : ℝ) + 1) ≠ 0 := by positivity
      exact_mod_cast fun h => this (by exact_mod_cast h)
    have hm : mSumg χ z P (N + 1) = mSumg χ z P N + gfun χ z P (N + 1) / ((N : ℂ) + 1) := by
      simp [mSumg, Finset.sum_Ioc_succ_top (Nat.zero_le _)]
    have hIco : ∑ k ∈ Ico 1 (N + 1), sigmaMeang χ z P k / (k + 1 : ℂ)
        = (∑ k ∈ Ico 1 N, sigmaMeang χ z P k / (k + 1 : ℂ))
          + sigmaMeang χ z P N / ((N : ℂ) + 1) := by
      rw [Finset.sum_Ico_succ_top hN]
    rw [hm, ih, hIco]
    simp only [sigmaMeang, Sgsum_succ, Nat.cast_add, Nat.cast_one]
    field_simp
    ring


/-! ### The principal character and the `ψ(x,χ₀) = ψ(x) − O_Q(log x)` comparison -/

/-- The principal character mod `Q`, as a function on `ℕ`. -/
noncomputable def chiZero (Q n : ℕ) : ℂ := if Nat.Coprime n Q then 1 else 0

lemma chiZero_mul (Q a b : ℕ) : chiZero Q (a * b) = chiZero Q a * chiZero Q b := by
  simp only [chiZero, Nat.coprime_mul_iff_left]
  split_ifs <;> simp_all

lemma norm_chiZero_le (Q n : ℕ) : ‖chiZero Q n‖ ≤ 1 := by
  rw [chiZero]; split_ifs <;> simp

/-- The discarded von-Mangoldt mass: `∑_{d ≤ X, gcd(d,Q) > 1} Λ d`. -/
noncomputable def corrQ (Q X : ℕ) : ℝ :=
  ∑ d ∈ (Ioc 0 X).filter (fun d => ¬ Nat.Coprime d Q), Λ d

lemma corrQ_nonneg (Q X : ℕ) : 0 ≤ corrQ Q X :=
  Finset.sum_nonneg fun _ _ ↦ vonMangoldt_nonneg

lemma psiChar_chiZero_eq (Q X : ℕ) : psiChar (chiZero Q) X = ((psiN X - corrQ Q X : ℝ) : ℂ) := by
  classical
  rw [psiChar, psiN, corrQ, ← Finset.sum_filter_add_sum_filter_not (Ioc 0 X)
    (fun d => Nat.Coprime d Q) (fun d => Λ d)]
  push_cast
  rw [Finset.sum_filter]
  simp only [chiZero]
  rw [Finset.sum_filter]
  push_cast
  rw [add_sub_cancel_right]
  exact Finset.sum_congr rfl fun d _ ↦ by by_cases h : Nat.Coprime d Q <;> simp [h]

/-- **The correction is `O_Q(log x)`.**  The discarded mass sits on the prime powers `p^j`
with `p ∣ Q`, and for each such `p` totals `⌊log_p X⌋ · log p ≤ log X`. -/
theorem corrQ_le {Q : ℕ} (hQ : Q ≠ 0) (X : ℕ) :
    corrQ Q X ≤ (Q.primeFactors.card : ℝ) * Real.log X := by
  classical
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp [corrQ]
  have hX0 : X ≠ 0 := hX.ne'
  have hXR : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hXR
  set G : ℕ → ℕ → ℝ := fun p i => if p ^ i ≤ X ∧ 2 ≤ p then Real.log p else 0 with hGdef
  have hG : ∀ p i, 0 ≤ G p i := by
    intro p i
    simp only [hGdef]
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast le_trans (by norm_num) h.2)
    · exact le_rfl
  have hrect := sum_le_primePow_rectangle (N := X) (J := Nat.log 2 X) le_rfl
    (s := (Ioc 0 X).filter (fun d => ¬ Nat.Coprime d Q)) (T := Q.primeFactors)
    (Finset.filter_subset _ _) (fun d => Λ d) G hG
    (by
      intro d _ hd
      rw [vonMangoldt_eq_zero_iff.2 hd])
    (by
      intro d hd hdp
      have hd1 : d ∈ Ioc 0 X := (Finset.mem_filter.1 hd).1
      have hncop : ¬ Nat.Coprime d Q := (Finset.mem_filter.1 hd).2
      have hp : d.minFac.Prime := Nat.minFac_prime hdp.ne_one
      -- some prime divides both `d` and `Q`; on a prime power it must be `minFac d`
      have hg1 : Nat.gcd d Q ≠ 1 := hncop
      have hgpos : 0 < Nat.gcd d Q := Nat.gcd_pos_of_pos_left _ (mem_Ioc.1 hd1).1
      have hr : (Nat.gcd d Q).minFac.Prime := Nat.minFac_prime hg1
      have hrd : (Nat.gcd d Q).minFac ∣ d :=
        dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_left _ _)
      have hrQ : (Nat.gcd d Q).minFac ∣ Q :=
        dvd_trans (Nat.minFac_dvd _) (Nat.gcd_dvd_right _ _)
      obtain ⟨k, _, _, hdk, _⟩ := primePow_spec hdp
      have hrp : (Nat.gcd d Q).minFac = d.minFac := by
        have : (Nat.gcd d Q).minFac ∣ d.minFac ^ k := by rw [← hdk]; exact hrd
        exact (Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow this)
      rw [← hrp]
      exact Nat.mem_primeFactors.2 ⟨hr, hrQ, hQ⟩)
    (by
      intro d hd hdp
      have hd1 : d ∈ Ioc 0 X := (Finset.mem_filter.1 hd).1
      have hp : d.minFac.Prime := Nat.minFac_prime hdp.ne_one
      have hpow : d.minFac ^ (Nat.log d.minFac d) = d := primePow_minFac_pow_log hdp
      have hle : d.minFac ^ (Nat.log d.minFac d) ≤ X := by rw [hpow]; exact (mem_Ioc.1 hd1).2
      have h2 : 2 ≤ d.minFac := hp.two_le
      rw [hGdef]
      simp only [hle, h2, and_self, if_pos]
      rw [vonMangoldt_apply, if_pos hdp])
  refine hrect.trans ?_
  rw [Finset.sum_product]
  calc ∑ p ∈ Q.primeFactors, ∑ i ∈ Icc 1 (Nat.log 2 X), G p i
      ≤ ∑ _p ∈ Q.primeFactors, Real.log X := Finset.sum_le_sum fun p hp ↦ ?_
    _ = (Q.primeFactors.card : ℝ) * Real.log X := by
        rw [Finset.sum_const, nsmul_eq_mul]
  -- the inner sum: at most `⌊log_p X⌋` terms, each `log p`
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hpR : (1:ℝ) < p := by exact_mod_cast hp2
  have hsub : (Icc 1 (Nat.log 2 X)).filter (fun i => p ^ i ≤ X ∧ 2 ≤ p)
      ⊆ Icc 1 (Nat.log p X) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
    exact Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hi1).1, (Nat.le_log_iff_pow_le hp2 hX0).2 hi2.1⟩
  calc ∑ i ∈ Icc 1 (Nat.log 2 X), G p i
      = ∑ i ∈ (Icc 1 (Nat.log 2 X)).filter (fun i => p ^ i ≤ X ∧ 2 ≤ p), Real.log p := by
        rw [hGdef, Finset.sum_filter]
    _ = (((Icc 1 (Nat.log 2 X)).filter (fun i => p ^ i ≤ X ∧ 2 ≤ p)).card : ℝ) * Real.log p := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Nat.log p X : ℕ) : ℝ) * Real.log p := by
        have hcard := Finset.card_le_card hsub
        have : (((Icc 1 (Nat.log 2 X)).filter (fun i => p ^ i ≤ X ∧ 2 ≤ p)).card : ℝ)
            ≤ ((Nat.log p X : ℕ) : ℝ) := by
          exact_mod_cast le_trans hcard (by simp [Nat.card_Icc])
        have hlp : 0 ≤ Real.log p := Real.log_nonneg hpR.le
        exact mul_le_mul_of_nonneg_right this hlp
    _ = Real.log ((p : ℝ) ^ (Nat.log p X)) := by rw [Real.log_pow]
    _ ≤ Real.log X := by
        refine Real.log_le_log (by positivity) ?_
        have := Nat.pow_log_le_self p hX0
        exact_mod_cast this


/-- The correction summed over the hyperbola is `O_Q(N)` — the sharp `log` (not `log²`) in
`corrQ_le` is exactly what makes this fit the chain's budget. -/
lemma sum_corrQ_le {Q : ℕ} (hQ : Q ≠ 0) (N : ℕ) :
    ∑ k ∈ Ioc 0 N, corrQ Q (N / k) ≤ (Q.primeFactors.card : ℝ) * N := by
  have hw : (0:ℝ) ≤ (Q.primeFactors.card : ℝ) := by positivity
  calc ∑ k ∈ Ioc 0 N, corrQ Q (N / k)
      ≤ ∑ k ∈ Ioc 0 N, (Q.primeFactors.card : ℝ) * Real.log ((N:ℝ) / k) := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        obtain ⟨hk0, hkN⟩ := mem_Ioc.1 hk
        have hkR : (0:ℝ) < k := by exact_mod_cast hk0
        have h1 : 1 ≤ N / k := Nat.one_le_div_iff hk0 |>.2 hkN
        have hdivR : (1:ℝ) ≤ ((N / k : ℕ) : ℝ) := by exact_mod_cast h1
        have hle : ((N / k : ℕ) : ℝ) ≤ (N:ℝ) / k := Nat.cast_div_le
        refine (corrQ_le hQ (N / k)).trans ?_
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (by linarith) hle) hw
    _ = (Q.primeFactors.card : ℝ) * ∑ k ∈ Ioc 0 N, Real.log ((N:ℝ) / k) := by
        rw [Finset.mul_sum]
    _ ≤ (Q.primeFactors.card : ℝ) * N :=
        mul_le_mul_of_nonneg_left (sum_log_div_le N) hw

/-- **The principal branch.**  `∑_{n ≤ N, gcd(n,Q)=1} z^{ω_{>P}(n)} = o(N)` for unimodular
`z ≠ 1`.  This is rung 1 rerun with the coprimality restriction: the chain is the same, the
only new input is that `ψ(·,χ₀)` differs from `ψ` by `O_Q(log x)`, hence by `O_Q(N)` after
summing over the hyperbola. -/
theorem sigmaMeang_chiZero_tendsto_zero {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (P : ℕ)
    {Q : ℕ} (hQ : Q ≠ 0) :
    Tendsto (fun N : ℕ => sigmaMeang (chiZero Q) z P N) atTop (𝓝 0) := by
  set χ : ℕ → ℂ := chiZero Q with hχdef
  have hmul : ∀ a b : ℕ, χ (a * b) = χ a * χ b := chiZero_mul Q
  have hχ : ∀ n, ‖χ n‖ ≤ 1 := norm_chiZero_le Q
  obtain ⟨C2, hC2⟩ := exists_L2g (χ := χ) (z := z) (P := P) hmul hχ hz
  obtain ⟨C4, hC4⟩ := exists_L4g (χ := χ) (z := z) (P := P) hχ hz
  set W : ℝ := (Q.primeFactors.card : ℝ) with hW
  have hre : z.re < 1 := by
    by_contra hcon
    push_neg at hcon
    have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
      have h1 : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
      simpa [Complex.normSq_apply, sq] using h1
    have hre1 : z.re = 1 := by nlinarith [sq_nonneg z.im]
    have him : z.im = 0 := by nlinarith
    exact hz1 (Complex.ext (by simpa using hre1) (by simpa using him))
  refine recursion_tendsto_zero hz hre (1 + C2 + C4 + W) (fun k => sigmaMeang χ z P k)
    (fun k => norm_sigmaMeang_le hχ hz k) (fun N hN ↦ ?_)
  have hN0 : 0 < N := by lia
  have hNR : (0:ℝ) < N := by exact_mod_cast hN0
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  set A : ℂ := ∑ n ∈ Ioc 0 N, gfun χ z P n * (Real.log n : ℂ) with hA
  -- the correction term
  set E : ℂ := ∑ k ∈ Ioc 0 N, gfun χ z P k * ((corrQ Q (N / k) : ℝ) : ℂ) with hE
  have hEle : ‖E‖ ≤ W * N := by
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun k _ ↦ ?_) (sum_corrQ_le hQ N)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (corrQ_nonneg Q (N / k))]
    exact mul_le_of_le_one_left (corrQ_nonneg Q (N / k)) (norm_gfun_le hχ hz k)
  have hpsisplit : ∑ k ∈ Ioc 0 N, gfun χ z P k * psiChar χ (N / k)
      = (∑ k ∈ Ioc 0 N, gfun χ z P k * (psiN (N / k) : ℂ)) - E := by
    rw [hE, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hχdef, psiChar_chiZero_eq]
    push_cast
    ring
  have key : ‖Sgsum χ z P N * (Real.log N : ℂ) - z * ((N : ℂ) * mSumg χ z P N)‖
      ≤ (1 + C2 + C4 + W) * N := by
    have hsplit : Sgsum χ z P N * (Real.log N : ℂ) - z * ((N : ℂ) * mSumg χ z P N)
        = -(A - Sgsum χ z P N * (Real.log N : ℂ))
          + (A - z * ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * χ d * Sgsum χ z P (N / d))
          + z * ((∑ k ∈ Ioc 0 N, gfun χ z P k * (psiN (N / k) : ℂ)) - (N : ℂ) * mSumg χ z P N)
          - z * E := by
      rw [sum_Lambda_mul_Sgsum, hpsisplit]; ring
    rw [hsplit]
    calc ‖-(A - Sgsum χ z P N * (Real.log N : ℂ))
            + (A - z * ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * χ d * Sgsum χ z P (N / d))
            + z * ((∑ k ∈ Ioc 0 N, gfun χ z P k * (psiN (N / k) : ℂ))
                - (N : ℂ) * mSumg χ z P N) - z * E‖
        ≤ ‖-(A - Sgsum χ z P N * (Real.log N : ℂ))
            + (A - z * ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * χ d * Sgsum χ z P (N / d))
            + z * ((∑ k ∈ Ioc 0 N, gfun χ z P k * (psiN (N / k) : ℂ))
                - (N : ℂ) * mSumg χ z P N)‖ + ‖z * E‖ := norm_sub_le _ _
      _ ≤ (‖-(A - Sgsum χ z P N * (Real.log N : ℂ))
            + (A - z * ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * χ d * Sgsum χ z P (N / d))‖
          + ‖z * ((∑ k ∈ Ioc 0 N, gfun χ z P k * (psiN (N / k) : ℂ))
                - (N : ℂ) * mSumg χ z P N)‖) + ‖z * E‖ := by
            gcongr; exact norm_add_le _ _
      _ ≤ ((‖-(A - Sgsum χ z P N * (Real.log N : ℂ))‖
            + ‖A - z * ∑ d ∈ Ioc 0 N, (Λ d : ℂ) * χ d * Sgsum χ z P (N / d)‖)
          + ‖z * ((∑ k ∈ Ioc 0 N, gfun χ z P k * (psiN (N / k) : ℂ))
                - (N : ℂ) * mSumg χ z P N)‖) + ‖z * E‖ := by
            gcongr; exact norm_add_le _ _
      _ ≤ (((N:ℝ) + C2 * N) + C4 * N) + W * N := by
            rw [norm_neg, norm_mul, norm_mul, hz, one_mul, one_mul]
            gcongr
            · exact norm_sum_gfun_mul_log_sub hχ hz N
            · exact hC2 N
            · exact hC4 N
      _ = (1 + C2 + C4 + W) * N := by ring
  have hdiv : ((Real.log N : ℂ) - z) * sigmaMeang χ z P N
      - z * ∑ k ∈ Ico 1 N, sigmaMeang χ z P k / ((k : ℂ) + 1)
      = (Sgsum χ z P N * (Real.log N : ℂ) - z * ((N : ℂ) * mSumg χ z P N)) / (N : ℂ) := by
    have hS : sigmaMeang χ z P N * (N:ℂ) = Sgsum χ z P N := by rw [sigmaMeang]; field_simp
    rw [mSumg_eq]
    field_simp [sigmaMeang]
    linear_combination (Real.log N : ℂ) * hS
  rw [hdiv, norm_div, Complex.norm_natCast, div_le_iff₀ hNR]
  exact key

end NormalNumbers.DelangeSlot
