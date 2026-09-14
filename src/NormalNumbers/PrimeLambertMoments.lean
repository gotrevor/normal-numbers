import NormalNumbers.PrimeLambertTail

/-!
# The moment decomposition of `SmallPrimeDecay` (draft §5.3–5.4)

`SmallPrimeDecay C` asks that the sample average `𝔼_{n ∈ P_N} e(q S_N(n))` tend to zero, where
`S_N(n) = ∑_{p small} X_p(n)` is the good small-prime signed sum.  The draft proves it by
comparing with the **independent model**: the same function `S_N` evaluated at a uniform
residue `r mod ∏_{p small} p`.  By CRT (a theorem about this model, not part of its
definition) the local variables `X_p(r)` are then independent and uniform mod each `p`, so this
is exactly the model `S' = ∑ X'_p` of draft §5.3.  We define

* `indepAvg C N g = (1/∏p) ∑_{r < ∏p} g(S_N(r))`  and  `sampleAvg C N g = (1/|P_N|) ∑_{n∈P_N} g(S_N(n))`,

and three exact obligations for a moment cutoff `M : ℕ → ℕ`:

* `IndepCharDecay C q` (draft (15)+(13)): `‖indepAvg e(q·)‖ → 0`;
* `MomentComparison C M` (draft (16)): `|sampleAvg x^k − indepAvg x^k| ≤ δ_N` for all
  `k ≤ M_N`, `δ_N → 0`;
* `IndepMomentSmall C M q` (draft (17)): `(2π|q|)^{M_N}/M_N! · indepAvg x^{M_N} → 0`.

**Proved transfer** (`smallPrimeDecay_of_moments`): for even `M_N` these three imply
`SmallPrimeDecay C`.  The tool is the sharp Taylor bound
`‖e^{it} − ∑_{k<M} (it)^k/k!‖ ≤ |t|^M/M!` (`norm_expRem_le'`, by induction with the integral
form of the remainder), applied on both the sample and the model; evenness of `M` makes the
remainder majorant `|S|^M = S^M` a moment that `MomentComparison` controls.  This is the
centred even-moment step of the draft; nothing here is an `ℓ¹` first-moment bound.
-/

open Filter Topology Finset Complex
open scoped BigOperators

namespace NormalNumbers.PrimeLambert

/-! ### Sharp Taylor remainder of `exp(it)` -/

/-- `exp(it) − ∑_{k<M} (it)^k/k!`. -/
noncomputable def expRem (M : ℕ) (t : ℝ) : ℂ :=
  exp ((t : ℂ) * I) - ∑ k ∈ range M, ((t : ℂ) * I) ^ k / (k.factorial : ℂ)

lemma expRem_succ_zero (M : ℕ) : expRem (M + 1) 0 = 0 := by
  unfold expRem
  rw [Finset.sum_range_succ']; simp

lemma hasDerivAt_expRem (M : ℕ) (t : ℝ) :
    HasDerivAt (expRem (M + 1)) (I * expRem M t) t := by
  have h1 : HasDerivAt (fun s : ℝ => exp ((s : ℂ) * I)) (I * exp ((t : ℂ) * I)) t := by
    have := (((hasDerivAt_exp ((t : ℂ) * I)).comp (t : ℂ)
      ((hasDerivAt_id (t : ℂ)).mul_const I))).comp_ofReal
    refine this.congr_deriv ?_
    simp [mul_comm]
  have h2 : HasDerivAt (fun s : ℝ => ∑ k ∈ range (M + 1), ((s : ℂ) * I) ^ k / (k.factorial : ℂ))
      (I * ∑ k ∈ range M, ((t : ℂ) * I) ^ k / (k.factorial : ℂ)) t := by
    have hk : ∀ k : ℕ, HasDerivAt (fun s : ℝ => ((s : ℂ) * I) ^ k / (k.factorial : ℂ))
        ((k : ℂ) * ((t : ℂ) * I) ^ (k - 1) * I / (k.factorial : ℂ)) t := by
      intro k
      have := ((((hasDerivAt_id (t : ℂ)).mul_const I).pow k).comp_ofReal).div_const
        (k.factorial : ℂ)
      refine this.congr_deriv ?_
      simp
    have := HasDerivAt.sum (u := range (M + 1)) (fun k _ => hk k)
    have := this.congr_of_eventuallyEq (f₁ := fun s : ℝ =>
      ∑ k ∈ range (M + 1), ((s : ℂ) * I) ^ k / (k.factorial : ℂ)) (Filter.Eventually.of_forall
      (fun s => by simp only [Finset.sum_apply]))
    refine this.congr_deriv ?_
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Nat.factorial_succ]
    push_cast
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hkf : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    field_simp
  have := h1.sub h2
  refine this.congr_deriv ?_
  unfold expRem; ring

lemma expRem_eq_integral (M : ℕ) (t : ℝ) :
    expRem (M + 1) t = ∫ s in (0 : ℝ)..t, I * expRem M s := by
  have hc : Continuous (expRem M) := by
    unfold expRem
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_expRem M s)
    ((continuous_const.mul hc).intervalIntegrable _ _), expRem_succ_zero, sub_zero]

lemma norm_expRem_le (M : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖expRem M t‖ ≤ t ^ M / (M.factorial : ℝ) := by
  induction M generalizing t with
  | zero =>
    unfold expRem
    simp
  | succ M ih =>
    rw [expRem_eq_integral]
    have hb : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.Ioc 0 t →
        ‖I * expRem M s‖ ≤ s ^ M / (M.factorial : ℝ) := by
      refine Filter.Eventually.of_forall (fun s hs => ?_)
      rw [norm_mul, Complex.norm_I, one_mul]
      exact ih s hs.1.le
    refine (intervalIntegral.norm_integral_le_of_norm_le ht hb ?_).trans ?_
    · exact (continuous_id.pow M |>.div_const _).intervalIntegrable _ _
    · rw [intervalIntegral.integral_div, integral_pow, Nat.factorial_succ]
      push_cast
      rw [zero_pow (by omega), sub_zero]
      field_simp
      ring_nf; rfl

lemma norm_expRem_le' (M : ℕ) (t : ℝ) : ‖expRem M t‖ ≤ |t| ^ M / (M.factorial : ℝ) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]; exact norm_expRem_le M t ht
  · have h := norm_expRem_le M (-t) (by linarith)
    rw [abs_of_neg ht]
    refine le_trans (le_of_eq ?_) h
    unfold expRem
    rw [← norm_conj, map_sub, map_sum]
    congr 2
    · rw [← Complex.exp_conj]; congr 1; simp
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [map_div₀, map_pow, map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast]
      push_cast; ring

/-! ### Averages -/

/-- Normalized finite average of a complex function. -/
noncomputable def avg {ι : Type*} (P : Finset ι) (g : ι → ℂ) : ℂ := (∑ n ∈ P, g n) / P.card

/-- Normalized finite average of a real function. -/
noncomputable def ravg {ι : Type*} (P : Finset ι) (g : ι → ℝ) : ℝ := (∑ n ∈ P, g n) / P.card

lemma avg_ofReal {ι : Type*} (P : Finset ι) (g : ι → ℝ) :
    avg P (fun n => ((g n : ℝ) : ℂ)) = ((ravg P g : ℝ) : ℂ) := by
  unfold avg ravg; push_cast; rfl

/-- Taylor coefficient `(2πq i)^k/k!`. -/
noncomputable def tc (q : ℤ) (k : ℕ) : ℂ := (2 * Real.pi * q * I) ^ k / (k.factorial : ℂ)

lemma norm_tc (q : ℤ) (k : ℕ) : ‖tc q k‖ = (2 * Real.pi * |q|) ^ k / (k.factorial : ℝ) := by
  unfold tc
  rw [norm_div, norm_pow, Complex.norm_natCast]
  congr 2
  rw [norm_mul, Complex.norm_I, mul_one]
  rw [show (2 * Real.pi * q : ℂ) = ((2 * Real.pi * q : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity)]
  push_cast; rfl

lemma e_eq_taylor (q : ℤ) (x : ℝ) (M : ℕ) :
    e (q * x) = ∑ k ∈ range M, tc q k * ((x : ℂ) ^ k) + expRem M (2 * Real.pi * q * x) := by
  have h2 : ∀ k ∈ range M, tc q k * (x : ℂ) ^ k
      = (((2 * Real.pi * q * x : ℝ) : ℂ) * I) ^ k / (k.factorial : ℂ) := by
    intro k _; unfold tc; rw [div_mul_eq_mul_div, ← mul_pow]; push_cast; ring_nf
  rw [Finset.sum_congr rfl h2]
  unfold expRem e
  have h1 : ((2 * Real.pi * (q * x) : ℝ) : ℂ) * I = ((2 * Real.pi * q * x : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h1]; ring

/-- **Even-moment Taylor bound for a finite average**: the average of `e(q h)` differs from
its degree-`M−1` Taylor polynomial in the moments of `h` by at most
`(2π|q|)^M/M! · 𝔼 h^M`, for even `M`. -/
theorem norm_avg_e_sub_taylor_le {ι : Type*} (P : Finset ι) (hP : P.Nonempty) (h : ι → ℝ)
    (q : ℤ) (M : ℕ) (hM : Even M) :
    ‖avg P (fun n => e (q * h n))
        - ∑ k ∈ range M, tc q k * ((ravg P (fun n => h n ^ k) : ℝ) : ℂ)‖
      ≤ (2 * Real.pi * |q|) ^ M / (M.factorial : ℝ) * ravg P (fun n => h n ^ M) := by
  have hcard : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hP
  have hsplit : avg P (fun n => e (q * h n))
      = ∑ k ∈ range M, tc q k * ((ravg P (fun n => h n ^ k) : ℝ) : ℂ)
        + avg P (fun n => expRem M (2 * Real.pi * q * h n)) := by
    unfold avg ravg
    simp_rw [e_eq_taylor q _ M]
    rw [Finset.sum_add_distrib, add_div, Finset.sum_comm]
    congr 1
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.mul_sum, mul_div_assoc]
    push_cast; rfl
  rw [hsplit, add_sub_cancel_left]
  unfold avg ravg
  rw [norm_div, Complex.norm_natCast, mul_div_assoc', div_le_div_iff_of_pos_right hcard]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun n _ => ?_)
  refine (norm_expRem_le' M _).trans (le_of_eq ?_)
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two, mul_pow, mul_pow, mul_pow,
    ← hM.pow_abs (h n)]
  push_cast
  ring

/-! ### The independent CRT model and the sample -/

/-- The good small-prime signed sum `S_N(n)` on the chain. -/
noncomputable def smallSum {q : ℤ} (C : Chain q) (N : ℕ) (n : ℤ) : ℝ :=
  classSum (C.c N) (C.K N) (C.S N).J (C.S N).small n

/-- CRT modulus `∏_{p small} p`. -/
def modulus {q : ℤ} (C : Chain q) (N : ℕ) : ℕ := ∏ p ∈ (C.S N).small, p

lemma modulus_pos {q : ℤ} (C : Chain q) (N : ℕ) : 0 < modulus C N :=
  Finset.prod_pos (fun p hp => ((C.S N).prime_small p hp).pos)

/-- Independent-model average: `S_N` at a uniform residue modulo `∏_{p small} p`. -/
noncomputable def indepAvg {q : ℤ} (C : Chain q) (N : ℕ) (g : ℝ → ℂ) : ℂ :=
  avg (range (modulus C N)) (fun r : ℕ => g (smallSum C N r))

/-- Real independent-model average. -/
noncomputable def rIndepAvg {q : ℤ} (C : Chain q) (N : ℕ) (g : ℝ → ℝ) : ℝ :=
  ravg (range (modulus C N)) (fun r : ℕ => g (smallSum C N r))

/-- Sample average of `g(S_N)` over the progression sample `P_N`. -/
noncomputable def sampleAvg {q : ℤ} (C : Chain q) (N : ℕ) (g : ℝ → ℂ) : ℂ :=
  avg (C.D N).P (fun n => g (smallSum C N n))

/-- Real sample average. -/
noncomputable def rSampleAvg {q : ℤ} (C : Chain q) (N : ℕ) (g : ℝ → ℝ) : ℝ :=
  ravg (C.D N).P (fun n => g (smallSum C N n))

/-- `SmallPrimeDecay` is the statement `‖sampleAvg e(q·)‖ → 0`. -/
lemma smallPrimeDecay_iff {q : ℤ} (C : Chain q) :
    SmallPrimeDecay C ↔
      Tendsto (fun N => ‖sampleAvg C N (fun x => e (q * x))‖) atTop (𝓝 0) := Iff.rfl

/-! ### The three obligations -/

/-- Draft (13)+(15): the independent model's characteristic function at frequency `q` decays
(the draft proves `≤ exp(−c_q V_N)` with `V_N → ∞`). -/
def IndepCharDecay {q : ℤ} (C : Chain q) : Prop :=
  Tendsto (fun N => ‖indepAvg C N (fun x => e (q * x))‖) atTop (𝓝 0)

/-- Draft (16): CRT moment comparison up to order `M_N`, uniformly `δ_N → 0`
(the draft gives `δ_N = N^{−9/10+o(1)}`). -/
def MomentComparison {q : ℤ} (C : Chain q) (M : ℕ → ℕ) : Prop :=
  ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
    ∀ N, ∀ k ≤ M N,
      |rSampleAvg C N (fun x => x ^ k) - rIndepAvg C N (fun x => x ^ k)| ≤ δ N

/-- Draft (17): the independent `M_N`-th moment is beaten by `M_N!` (the draft bounds it by
`2 exp(C_q V_N − M_N)`, using the two-sided mgf (14) and `M_N ≫ V_N`). -/
def IndepMomentSmall {q : ℤ} (C : Chain q) (M : ℕ → ℕ) : Prop :=
  Tendsto (fun N => (2 * Real.pi * |q|) ^ M N / ((M N).factorial : ℝ)
    * rIndepAvg C N (fun x => x ^ M N)) atTop (𝓝 0)

/-! ### The transfer -/

lemma sum_norm_tc_le (q : ℤ) (M : ℕ) :
    ∑ k ∈ range M, ‖tc q k‖ ≤ Real.exp (2 * Real.pi * |q|) := by
  simp_rw [norm_tc]
  exact Real.sum_le_exp_of_nonneg (by positivity) M

lemma pow_div_factorial_le_exp' (q : ℤ) (M : ℕ) :
    (2 * Real.pi * |q|) ^ M / (M.factorial : ℝ) ≤ Real.exp (2 * Real.pi * |q|) := by
  have := Real.sum_le_exp_of_nonneg (x := 2 * Real.pi * |q|) (by positivity) (M + 1)
  rw [Finset.sum_range_succ] at this
  have hnn : 0 ≤ ∑ k ∈ range M, (2 * Real.pi * |q|) ^ k / (k.factorial : ℝ) :=
    Finset.sum_nonneg (fun k _ => by positivity)
  linarith

/-- Pointwise transfer bound at one `N`. -/
theorem norm_sampleAvg_le {q : ℤ} (C : Chain q) (N : ℕ) (M : ℕ) (hM : Even M) (δ : ℝ)
    (hδ : ∀ k ≤ M, |rSampleAvg C N (fun x => x ^ k) - rIndepAvg C N (fun x => x ^ k)| ≤ δ) :
    ‖sampleAvg C N (fun x => e (q * x))‖
      ≤ ‖indepAvg C N (fun x => e (q * x))‖ + 2 * Real.exp (2 * Real.pi * |q|) * δ
        + 2 * ((2 * Real.pi * |q|) ^ M / (M.factorial : ℝ) * rIndepAvg C N (fun x => x ^ M)) := by
  set A := sampleAvg C N (fun x => e (q * x))
  set B := indepAvg C N (fun x => e (q * x))
  set PA := ∑ k ∈ range M, tc q k * ((rSampleAvg C N (fun x => x ^ k) : ℝ) : ℂ)
  set PB := ∑ k ∈ range M, tc q k * ((rIndepAvg C N (fun x => x ^ k) : ℝ) : ℂ)
  set T := (2 * Real.pi * |q|) ^ M / (M.factorial : ℝ)
  have hT : 0 ≤ T := by positivity
  have hTe : T ≤ Real.exp (2 * Real.pi * |q|) := pow_div_factorial_le_exp' q M
  have hA : ‖A - PA‖ ≤ T * rSampleAvg C N (fun x => x ^ M) :=
    norm_avg_e_sub_taylor_le (C.D N).P (C.D N).nonempty (smallSum C N) q M hM
  have hB : ‖B - PB‖ ≤ T * rIndepAvg C N (fun x => x ^ M) :=
    norm_avg_e_sub_taylor_le (range (modulus C N)) (by
      rw [Finset.nonempty_range_iff]; exact (modulus_pos C N).ne') (fun r : ℕ => smallSum C N r)
      q M hM
  have hPAB : ‖PA - PB‖ ≤ Real.exp (2 * Real.pi * |q|) * δ := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ range M, ‖tc q k * ((rSampleAvg C N (fun x => x ^ k) : ℝ) : ℂ)
              - tc q k * ((rIndepAvg C N (fun x => x ^ k) : ℝ) : ℂ)‖
        ≤ ∑ k ∈ range M, ‖tc q k‖ * δ := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          gcongr
          exact hδ k (Finset.mem_range.mp hk).le
      _ = (∑ k ∈ range M, ‖tc q k‖) * δ := by rw [Finset.sum_mul]
      _ ≤ Real.exp (2 * Real.pi * |q|) * δ := by
          have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hδ 0 (Nat.zero_le _))
          exact mul_le_mul_of_nonneg_right (sum_norm_tc_le q M) hδ0
  have hM' : rSampleAvg C N (fun x => x ^ M) ≤ rIndepAvg C N (fun x => x ^ M) + δ := by
    have := hδ M le_rfl
    linarith [le_abs_self (rSampleAvg C N (fun x => x ^ M) - rIndepAvg C N (fun x => x ^ M))]
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) (hδ 0 (Nat.zero_le _))
  calc ‖A‖ = ‖B + (A - PA) + (PA - PB) + (PB - B)‖ := by congr 1; ring
    _ ≤ ‖B‖ + ‖A - PA‖ + ‖PA - PB‖ + ‖PB - B‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖B‖ + T * (rIndepAvg C N (fun x => x ^ M) + δ) + Real.exp (2 * Real.pi * |q|) * δ
          + T * rIndepAvg C N (fun x => x ^ M) := by
        rw [norm_sub_rev PB B]
        gcongr
        exact hA.trans (mul_le_mul_of_nonneg_left hM' hT)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hTe hδ0]

/-- **Transfer.**  For even moment cutoffs, the three moment obligations give
`SmallPrimeDecay`. -/
theorem smallPrimeDecay_of_moments {q : ℤ} (C : Chain q) (M : ℕ → ℕ) (hM : ∀ N, Even (M N))
    (h1 : IndepCharDecay C) (h2 : MomentComparison C M) (h3 : IndepMomentSmall C M) :
    SmallPrimeDecay C := by
  obtain ⟨δ, hδ, hb⟩ := h2
  rw [smallPrimeDecay_iff]
  have hpt : ∀ N, ‖sampleAvg C N (fun x => e (q * x))‖
      ≤ ‖indepAvg C N (fun x => e (q * x))‖ + 2 * Real.exp (2 * Real.pi * |q|) * δ N
        + 2 * ((2 * Real.pi * |q|) ^ M N / ((M N).factorial : ℝ)
          * rIndepAvg C N (fun x => x ^ M N)) :=
    fun N => norm_sampleAvg_le C N (M N) (hM N) (δ N) (hb N)
  have hlim : Tendsto (fun N => ‖indepAvg C N (fun x => e (q * x))‖
      + 2 * Real.exp (2 * Real.pi * |q|) * δ N
      + 2 * ((2 * Real.pi * |q|) ^ M N / ((M N).factorial : ℝ)
          * rIndepAvg C N (fun x => x ^ M N))) atTop (𝓝 0) := by
    have := (h1.add (hδ.const_mul (2 * Real.exp (2 * Real.pi * |q|)))).add (h3.const_mul 2)
    simpa using this
  exact squeeze_zero (fun N => norm_nonneg _) hpt hlim

/-- The remaining obligation for `SmallPrimeDecay`, as a research-map Prop: an even moment
cutoff with the three conditions.  Draft §5.1: `M_N ~ (log log N)^{1/12}` even. -/
def MomentChain {q : ℤ} (C : Chain q) : Prop :=
  ∃ M : ℕ → ℕ, (∀ N, Even (M N)) ∧ IndepCharDecay C ∧ MomentComparison C M ∧ IndepMomentSmall C M

theorem smallPrimeDecay_of_momentChain {q : ℤ} (C : Chain q) (h : MomentChain C) :
    SmallPrimeDecay C := by
  obtain ⟨M, hM, h1, h2, h3⟩ := h
  exact smallPrimeDecay_of_moments C M hM h1 h2 h3

end NormalNumbers.PrimeLambert
