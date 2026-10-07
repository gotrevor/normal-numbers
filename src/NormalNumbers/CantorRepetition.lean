/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorExactExponentProfile
import NormalNumbers.EntropyProfiles
import NormalNumbers.ExplicitPQ

/-!
# Is the profile cut forced?  Repetitions instead of zero runs

Ren, 2026-10-06 (`/create`, after the profile theorem).  In
`CantorExactExponentProfile`, a point of `K` whose exponent comes from forced **zero runs**
(approximations `P/3^a`) is normal to `3ˢt` only when `t > 3^{s(μ₀−1)}`.  In particular no
Cantor–Liouville point of the repo is normal to base 6 (`CantorLiouvilleAll.not_isNormal_six`).
Cassels–Schmidt-typical points of `K` are normal to every base that is not a power of 3, but
their exponent is 2.

**Question: is the cut a property of the exponent, or of zero runs?**  The approximations made
by zero runs have denominators divisible by `3^a`, and that divisibility is what produces the
base-`3ˢt` zero runs.  A **repetition** gives approximations with denominators *prime to 3*.
Take a free block `W` of length `ℓ` and copy it `M` times: then `x ≈ W/(3^ℓ − 1)` to within
`3^{−Mℓ}`, and `3^ℓ − 1` is prime to 3.  The digits stay in `{0, 2}`, so `x ∈ K`.  With `M → ∞`,
`x` is Liouville.

**Conjecture (frozen).**  There is a Liouville number in `K` that is normal to every base that is
not a power of 3 (`LiouvilleCantorFullProfile`); in particular one normal to base 6.  More
strongly, for every rational `μ₀ > 2` there is such a point with exponent exactly `μ₀`
(`ExponentCantorFullProfile`).  The profile cut would then belong to the zero-run construction,
not to the exponent.

**Why the zero-run obstruction is absent.**  In base `b = 3ˢt`, `bʲ·W/(3^ℓ − 1)` is never close
to an integer unless `3^ℓ − 1` divides it.  `gcd(b, 3^ℓ − 1)` divides `t`, so the base-`b`
expansion of the approximant is periodic with period `ord(b mod (3^ℓ−1)/gcd)`, typically
`≍ 3^ℓ`, which is far longer than the agreement window.  No forced base-`b` block appears.

**Why normality is plausible (mechanism).**  The copies are not free coins, but the law of `x`
is still a product over the free coins.  Coin `i` enters with the weight
`w_i = 2·Σ_c 3^{−(i+cℓ)−1}`, so `𝔼 e(ξx) = Π_i (1 + e(ξ w_i))/2`, and a Cassels second moment
needs `‖ξ w_i‖` to stay away from 0 on many coins.  For a frequency `ξ = h bⁿ` whose ternary
window lies in a copy region, the copy at `i + cℓ` plays the role of a free place.

**Known-false sibling.**  The same copies with base `b = 9` must fail, since base-9 digits of a
`{0,2}`-ternary point lie in `{0,2,6,8}`.  Any proof must use `t > 1` somewhere (in the
digit-change counting, as `CantorLiouvilleAll.secondMoment_le_b` uses `3 ∤ b`).

**What is hard.**  The Liouville version needs only the lower bound on the exponent, so the
whole difficulty is normality with copied digits (the fraction of copied digits tends to 1 along
the repetitions).  The exact-exponent version also needs an upper bound.  The approximants
`p/(3^ℓ−1)` are prime to 3, so the 3-adic count `hit_mass_padic` does not apply, and a new
count is needed.
-/

open MeasureTheory Filter

namespace NormalNumbers.CantorRepetition

/-- **A Liouville number in `K` with the full Cassels–Schmidt profile.**  Normal to `b` exactly
when `b` is not a power of 3.  Confidence 60%. -/
def LiouvilleCantorFullProfile : Prop :=
  ∃ x ∈ cantorSet, Liouville x ∧ ∀ b : ℕ, 2 ≤ b → (IsNormal b x ↔ ∀ s : ℕ, b ≠ 3 ^ s)

/-- **Exact exponent `μ₀` in `K` with the full profile.**  Confidence 40% (the exponent upper
bound for repetition approximants is a new count). -/
def ExponentCantorFullProfile (μ₀ : ℚ) : Prop :=
  ∃ x ∈ cantorSet, CantorExactExponent.HasIrrExponent x μ₀ ∧
    ∀ b : ℕ, 2 ≤ b → (IsNormal b x ↔ ∀ s : ℕ, b ≠ 3 ^ s)

/-! ## The construction: copies on the forced runs

We keep the free positions of `CantorLiouville` (`isFree`; runs `[a_k, (k+2)a_k)`,
`a_k = runStart k`).  On run `k` the digits are no longer zero: the block `[a_k, 2a_k)` carries
fresh coins, and the rest of the run repeats that block `k` more times (period `a_k`).  So
`x ≈ p/q` with `q = 3^{a_k}(3^{a_k} − 1)`, error `≤ 3^{-(k+2)a_k}`: exponent `≥ (k+2)/2`. -/

open CantorLiouville CantorLiouvilleAll DecayAeNormal ExplicitSquare CantorSelfSimilar

/-- The run containing a forced position (the largest `k ≤ i` with `a_k ≤ i`). -/
noncomputable def runIdx (i : ℕ) : ℕ := Nat.findGreatest (fun k => runStart k ≤ i) i

/-- The coin read at position `i`: itself if free, else the block position
`a_k + (i − a_k) mod a_k` of its run. -/
noncomputable def src (i : ℕ) : ℕ :=
  if isFree i then i else runStart (runIdx i) + (i - runStart (runIdx i)) % runStart (runIdx i)

/-- **The repetition point** coded by the coins `ω`. -/
noncomputable def repReal (ω : ℕ → Bool) : ℝ := pt (fun _ => true) (fun i => ω (src i))

/-- The copy part: digits on the forced positions only. -/
noncomputable def repCopy (ω : ℕ → Bool) : ℝ := pt (fun i => !isFree i) (fun i => ω (src i))

theorem runIdx_eq {k i : ℕ} (h1 : runStart k ≤ i) (h2 : i < (k + 2) * runStart k) :
    runIdx i = k := by
  unfold runIdx
  rw [Nat.findGreatest_eq_iff]
  refine ⟨(lt_runStart k).le.trans h1, fun _ => h1, fun j hj hji hP => ?_⟩
  have := runStart_mono (show k + 1 ≤ j by omega)
  rw [runStart_succ_eq] at this
  have : (k + 2) * runStart k ≤ 2 * (k + 2) * runStart k := by nlinarith
  omega

theorem exists_run_of_not_free {i : ℕ} (h : isFree i = false) :
    ∃ k, runStart k ≤ i ∧ i < (k + 2) * runStart k := by
  by_contra hc
  push_neg at hc
  have := isFree_of_not_mem_run (i := i) fun k ⟨h1, h2⟩ => absurd h2 (not_lt.2 (hc k h1))
  rw [h] at this; exact absurd this (by decide)

theorem src_of_mem_run {k i : ℕ} (h1 : runStart k ≤ i) (h2 : i < (k + 2) * runStart k) :
    src i = runStart k + (i - runStart k) % runStart k := by
  have hf : isFree i = false := by simp [isFree, isForced_of_mem_run h1 h2]
  simp [src, hf, runIdx_eq h1 h2]

theorem src_of_free {i : ℕ} (h : isFree i = true) : src i = i := by simp [src, h]

/-- Forced positions read forced positions (the block lies inside its run). -/
theorem isFree_src_of_not_free {i : ℕ} (h : isFree i = false) : isFree (src i) = false := by
  obtain ⟨k, h1, h2⟩ := exists_run_of_not_free h
  rw [src_of_mem_run h1 h2]
  have hpos : 0 < runStart k := (Nat.zero_le k).trans_lt (lt_runStart k)
  have := Nat.mod_lt (i - runStart k) hpos
  have hf := isForced_of_mem_run (k := k) (i := runStart k + (i - runStart k) % runStart k)
    (by omega) (by nlinarith)
  simp [isFree, hf]

theorem measurable_reindex : Measurable fun (ω : ℕ → Bool) (i : ℕ) => ω (src i) :=
  measurable_pi_lambda _ fun i => measurable_pi_apply (src i)

theorem measurable_repReal : Measurable repReal :=
  (measurable_pt _).comp measurable_reindex

theorem measurable_repCopy : Measurable repCopy :=
  (measurable_pt _).comp measurable_reindex

/-- **The point lies in the Cantor set.** -/
theorem repReal_mem_cantorSet (ω : ℕ → Bool) : repReal ω ∈ cantorSet := pt_mem_cantorSet _ _

theorem pt_true_eq_add (f : ℕ → Bool) (ω : ℕ → Bool) :
    pt (fun _ => true) ω = pt f ω + pt (fun i => !f i) ω := by
  unfold pt realOfDigits
  simp only [Nat.cast_ofNat]
  rw [← (summable_ptDigit f ω).tsum_add (summable_ptDigit _ ω)]
  refine tsum_congr fun i => ?_
  rw [← add_div]; congr 1
  simp only [ptDigit]
  rcases Bool.eq_false_or_eq_true (f i) with h | h <;>
    rcases Bool.eq_false_or_eq_true (ω i) with h' | h' <;> simp [h, h']

/-- **Free part plus copy part.**  The free coins enter exactly as in `cantorLiouvilleReal`. -/
theorem repReal_eq (ω : ℕ → Bool) : repReal ω = pt isFree ω + repCopy ω := by
  unfold repReal repCopy
  rw [pt_true_eq_add isFree]
  congr 1
  unfold pt; congr 1; funext i
  simp only [ptDigit]
  cases h : isFree i
  · simp
  · simp [src_of_free h]

/-- The copy part reads only forced coins. -/
theorem repCopy_congr {ω ω' : ℕ → Bool} (h : ∀ i, isFree i = false → ω i = ω' i) :
    repCopy ω = repCopy ω' := by
  unfold repCopy pt; congr 1; funext i
  simp only [ptDigit]
  by_cases hf : isFree i = true
  · simp [hf]
  · simp only [Bool.not_eq_true] at hf
    simp [hf, h _ (isFree_src_of_not_free hf)]

/-! ## Bases coprime to 3: Cassels with an independent shift -/

/-- **Riesz bound survives an independent additive shift.**  If `Z` reads only the non-free
coins, `‖𝔼 e(ξ(pt free + Z))‖ ≤ Bf free M ξ`.  Proved (the induction of `charFun_real`, carrying
`Z ∘ consB c` along). -/
theorem charFun_add (M : ℕ) : ∀ (free : ℕ → Bool) (ξ : ℝ) (Z : (ℕ → Bool) → ℝ), Measurable Z →
    (∀ ω ω', (∀ i, free i = false → ω i = ω' i) → Z ω = Z ω') →
    ‖∫ ω, ee (ξ * (pt free ω + Z ω)) ∂coinMeasure‖ ≤ Bf free M ξ := by
  induction M with
  | zero =>
    intro free ξ Z _ _
    simp only [Bf, Finset.range_zero, Finset.filter_empty, Finset.prod_empty]
    refine (norm_integral_le_of_norm_le_const (C := 1)
      (Eventually.of_forall fun ω => (norm_ee _).le)).trans ?_
    simp
  | succ M ih =>
    intro free ξ Z hZm hZ
    set free' : ℕ → Bool := fun i => free (i + 1)
    set g : (ℕ → Bool) → ℂ := fun ω => ee (ξ * (pt free ω + Z ω))
    have hgm : Measurable g := measurable_ee.comp (((measurable_pt free).add hZm).const_mul ξ)
    have hgi : ∀ μ : Measure (ℕ → Bool), IsFiniteMeasure μ → Integrable g μ := fun μ _ =>
      Integrable.of_bound hgm.aestronglyMeasurable 1
        (Eventually.of_forall fun ω => (norm_ee _).le)
    set Zc : Bool → (ℕ → Bool) → ℝ := fun c ω => 3 * Z (consB c ω)
    have hZcm : ∀ c, Measurable (Zc c) := fun c => (hZm.comp (measurable_consB c)).const_mul 3
    have hZc : ∀ c ω ω', (∀ i, free' i = false → ω i = ω' i) → Zc c ω = Zc c ω' := by
      intro c ω ω' h
      simp only [Zc]; congr 1
      refine hZ _ _ fun i hi => ?_
      cases i with
      | zero => rfl
      | succ i => exact h i hi
    set I' : Bool → ℂ := fun c => ∫ ω, ee (ξ / 3 * (pt free' ω + Zc c ω)) ∂coinMeasure
    have hc : ∀ c, ∫ ω, g (consB c ω) ∂coinMeasure =
        ee (ξ * ((if free 0 && c then 2 else 0) / 3)) * I' c := by
      intro c
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [g, Zc, pt_consB, ← ee_add]
      congr 1; ring
    have hsplit : ∫ ω, g ω ∂coinMeasure =
        2⁻¹ * ∫ ω, g (consB true ω) ∂coinMeasure + 2⁻¹ * ∫ ω, g (consB false ω) ∂coinMeasure := by
      conv_lhs => rw [coinMeasure_eq]
      rw [integral_add_measure ((hgi _ inferInstance).smul_measure (by simp))
          ((hgi _ inferInstance).smul_measure (by simp)),
        integral_smul_measure, integral_smul_measure,
        integral_map (measurable_consB true).aemeasurable hgm.aestronglyMeasurable,
        integral_map (measurable_consB false).aemeasurable hgm.aestronglyMeasurable]
      simp [ENNReal.toReal_inv]
    have hI' : ∀ c, ‖I' c‖ ≤ Bf free' M (ξ / 3) := fun c => ih free' (ξ / 3) (Zc c) (hZcm c) (hZc c)
    change ‖∫ ω, g ω ∂coinMeasure‖ ≤ _
    rw [hsplit, hc, hc]
    unfold Bf
    rw [Finset.prod_filter, Finset.prod_range_succ', ← Finset.prod_filter]
    have hre : ∏ p ∈ (Finset.range M).filter (fun p => free (p + 1) = true),
        |Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1 + 1))| = Bf free' M (ξ / 3) := by
      refine Finset.prod_congr rfl fun p _ => ?_
      congr 2; rw [pow_succ]; ring
    rw [hre]
    by_cases h0 : free 0 = true
    · have hZtf : I' true = I' false := by
        have hz : ∀ ω, Z (consB true ω) = Z (consB false ω) := fun ω =>
          hZ _ _ fun i hi => by
            cases i with
            | zero => rw [h0] at hi; exact absurd hi (by decide)
            | succ i => rfl
        simp only [I', Zc, hz]
      simp only [h0, Bool.true_and, if_true, Bool.false_eq_true, if_false]
      rw [hZtf]
      have : 2⁻¹ * (ee (ξ * (2 / 3)) * I' false) + 2⁻¹ * (ee (ξ * (0 / 3)) * I' false) =
          ((1 + ee (2 * ξ / 3)) / 2) * I' false := by
        rw [show ξ * (0 / 3) = 0 by ring, show ξ * (2 / 3) = 2 * ξ / 3 by ring]
        simp [ee]; ring
      rw [this, norm_mul, norm_one_add_ee_div_two, mul_comm,
        show Real.pi * (2 * ξ / 3) = 2 * Real.pi * ξ / 3 ^ (0 + 1) by ring]
      exact mul_le_mul_of_nonneg_right (hI' false) (abs_nonneg _)
    · simp only [Bool.not_eq_true] at h0
      simp only [h0, Bool.false_and, Bool.false_eq_true, if_false, mul_one]
      rw [show ξ * (0 / 3) = 0 by ring]
      simp only [ee, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
      calc ‖2⁻¹ * I' true + 2⁻¹ * I' false‖ ≤ ‖2⁻¹ * I' true‖ + ‖2⁻¹ * I' false‖ := norm_add_le _ _
        _ = 2⁻¹ * ‖I' true‖ + 2⁻¹ * ‖I' false‖ := by simp
        _ ≤ 2⁻¹ * Bf free' M (ξ / 3) + 2⁻¹ * Bf free' M (ξ / 3) := by
            gcongr <;> exact hI' _
        _ = _ := by ring

theorem charFun_repReal (M : ℕ) (ξ : ℝ) :
    ‖∫ ω, ee (ξ * repReal ω) ∂coinMeasure‖ ≤ Bf isFree M ξ := by
  simp_rw [repReal_eq]
  exact charFun_add M isFree ξ repCopy measurable_repCopy fun ω ω' h => repCopy_congr h

/-! ### The base-`b` second moment for any law with the Riesz bound (copy of
`CantorLiouvilleAll.secondMoment_le_b`, `pt free` replaced by `G`) -/

theorem secondMoment_expand_of_cf (free : ℕ → Bool) (Φ : (ℕ → Bool) → ℝ)
    (hGm : Measurable Φ) (hcf : ∀ M ξ, ‖∫ ω, ee (ξ * Φ ω) ∂coinMeasure‖ ≤ Bf free M ξ) (b : ℕ) (h : ℤ) (M N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * Φ ω)‖ ^ 2 ∂coinMeasure ≤
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, Bf free M (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) := by
  have hG := hGm
  have hint : ∀ ξ : ℝ, Integrable (fun ω => ee (ξ * Φ ω)) coinMeasure := fun ξ =>
    Integrable.of_bound ((measurable_ee.comp (hG.const_mul ξ)).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => (norm_ee _).le)
  have hexp : ∀ ω, ((‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * Φ ω)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * Φ ω) := by
    intro ω
    rw [sq_norm_sum_ee (fun k => h * (b : ℝ) ^ k * Φ ω)]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    congr 1; ring
  have hI : ((∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * Φ ω)‖ ^ 2 ∂coinMeasure : ℝ) : ℂ) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * Φ ω) ∂coinMeasure := by
    rw [← integral_complex_ofReal]
    simp_rw [hexp]
    rw [integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_finsetSum _ fun m _ => hint _]
  have := congrArg Complex.re hI
  rw [Complex.ofReal_re] at this
  rw [this]
  refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  refine Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun m _ => hcf M _

theorem secondMoment_le_explicit_of_cf (free : ℕ → Bool) (Φ : (ℕ → Bool) → ℝ)
    (hGm : Measurable Φ) (hcf : ∀ M ξ, ‖∫ ω, ee (ξ * Φ ω) ∂coinMeasure‖ ≤ Bf free M ξ) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ)
    (hh : h ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * Φ ω)‖ ^ 2 ∂coinMeasure ≤
      (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) +
        3 * (3 ^ (padicValNat 3 h.natAbs + tb b) + 2 * (3 / 2 : ℝ) ^ tb b) * (N : ℝ) ^ 2 *
          Real.exp (-(Real.log (3 / 2) / 2) * freeCount free (Nat.log 3 N / 2)) := by
  set e := padicValNat 3 h.natAbs
  set t := tb b
  set M := Nat.log 3 N / 2
  set F := freeCount free M
  set W := F / 2
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hMN : 3 ^ M ≤ N :=
    (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)).trans
      (Nat.pow_log_le_self 3 (by omega))
  set G : ℕ → ℕ → ℝ := fun d m => Bf free M (h * ((b : ℝ) ^ d - 1) * (b : ℝ) ^ m)
  have hpair := pair_sum_le (fun n m => Bf free M (h * ((b : ℝ) ^ n - (b : ℝ) ^ m))) G
    (fun d m => Bf_nonneg _ _ _) (fun n => Bf_le_one _ _ _)
    (fun n m hmn => le_of_eq (by
      simp only [G]; congr 1
      rw [show (b : ℝ) ^ n = (b : ℝ) ^ (n - m) * (b : ℝ) ^ m by rw [← pow_add]; congr 1; omega]; ring))
    (fun n m hmn => le_of_eq (by
      simp only [G]; rw [← Bf_neg]; congr 1
      rw [show (b : ℝ) ^ m = (b : ℝ) ^ (m - n) * (b : ℝ) ^ n by rw [← pow_add]; congr 1; omega]; ring)) N
  set P := (2 / 3 : ℝ) ^ W
  set T := (3 / 2 : ℝ) ^ t
  have hT : 0 ≤ T := by positivity
  have hshift : ∀ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤
      (if W ≤ e + padicValNat 3 (b ^ d - 1) then (N : ℝ) else 0) + 2 * N * T * P := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    have hd1 : 1 ≤ b ^ d - 1 := by
      have : 2 ≤ b ^ d := le_trans hb (Nat.le_self_pow (by omega) b)
      omega
    split_ifs with hbad
    · refine (Finset.sum_le_sum fun m _ => Bf_le_one free M _).trans ?_
      have : (0 : ℝ) ≤ 2 * N * T * P := by positivity
      simp; linarith
    · rw [zero_add]
      set c := h.natAbs * (b ^ d - 1)
      have hc : c ≠ 0 := Nat.mul_ne_zero (Int.natAbs_ne_zero.2 hh) (by omega)
      have hv : padicValNat 3 c = e + padicValNat 3 (b ^ d - 1) :=
        padicValNat.mul (Int.natAbs_ne_zero.2 hh) (by omega)
      refine le_of_eq_of_le (Finset.sum_congr rfl fun m _ => ?_)
        (good_shift_b free hb h3 M N hMN c hc (by omega))
      simp only [G]
      rw [← Bf_abs]
      congr 1
      have hd2 : (0 : ℝ) ≤ (b : ℝ) ^ d - 1 := by
        have : (1:ℝ) ≤ (b : ℝ) ^ d := one_le_pow₀ hb1; linarith
      simp only [c]
      push_cast [Nat.cast_sub (Nat.one_le_pow _ _ (by omega : 0 < b))]
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (b : ℝ) ^ m),
        abs_of_nonneg hd2, Nat.cast_natAbs, Int.cast_abs]
  have hsumd : ∑ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤
      N * ((N / 3 ^ (W - e - t) : ℕ) : ℝ) + N * (2 * N * T * P) := by
    refine (Finset.sum_le_sum hshift).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
      nsmul_eq_mul, nsmul_eq_mul, Nat.card_Ico]
    have hbc := bad_count_b hb h3 e W N
    have : (((Finset.Ico 1 N).filter (fun m => W ≤ e + padicValNat 3 (b ^ m - 1))).card : ℝ) ≤
        ((N / 3 ^ (W - e - t) : ℕ) : ℝ) := by exact_mod_cast hbc
    have hN1 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    have : (0 : ℝ) ≤ 2 * N * T * P := by positivity
    nlinarith
  have hdiv : ((N / 3 ^ (W - e - t) : ℕ) : ℝ) ≤ N * 3 ^ (e + t) * P := by
    have h1 : (N / 3 ^ (W - e - t)) * 3 ^ W ≤ N * 3 ^ (e + t) := by
      calc (N / 3 ^ (W - e - t)) * 3 ^ W ≤ (N / 3 ^ (W - e - t)) * (3 ^ (W - e - t) * 3 ^ (e + t)) := by
            gcongr; rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = (N / 3 ^ (W - e - t)) * 3 ^ (W - e - t) * 3 ^ (e + t) := by ring
        _ ≤ N * 3 ^ (e + t) := by gcongr; exact Nat.div_mul_le_self _ _
    have h2 : ((N / 3 ^ (W - e - t) : ℕ) : ℝ) * 3 ^ W ≤ N * 3 ^ (e + t) := by exact_mod_cast h1
    have h3' : (2 / 3 : ℝ) ^ W * 3 ^ W = 2 ^ W := by rw [← mul_pow]; norm_num
    have h4 : (1 : ℝ) ≤ 2 ^ W := one_le_pow₀ (by norm_num)
    have h5 : (0 : ℝ) < 3 ^ W := by positivity
    rw [← mul_le_mul_iff_of_pos_right h5]
    calc _ ≤ (N : ℝ) * 3 ^ (e + t) := h2
      _ ≤ (N : ℝ) * 3 ^ (e + t) * 2 ^ W := le_mul_of_one_le_right (by positivity) h4
      _ = _ := by rw [mul_assoc _ ((2 / 3 : ℝ) ^ W), h3']
  have hexp := pow_two_sub_le W F rfl
  have hNr : (N : ℝ) ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) = N * (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (N : ℝ) ^ 2 = N * N ^ (1 : ℝ) by rw [Real.rpow_one]; ring, mul_assoc,
        ← Real.rpow_add (by positivity)]
      norm_num
    rw [this]
    have : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hN0 (by norm_num)
    nlinarith
  have hI := (secondMoment_expand_of_cf free Φ hGm hcf b h M N).trans hpair
  set E := Real.exp (-(Real.log (3 / 2) / 2) * F)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hP : 0 ≤ P := by positivity
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hfin : ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * Φ ω)‖ ^ 2 ∂coinMeasure ≤
      N + 2 * ((N : ℝ) ^ 2 * (3 ^ (e + t) + 2 * T) * P) := by
    have := mul_le_mul_of_nonneg_left hdiv hN0
    nlinarith
  have hK : (0 : ℝ) ≤ 3 ^ (e + t) + 2 * T := by positivity
  calc _ ≤ N + 2 * ((N : ℝ) ^ 2 * (3 ^ (e + t) + 2 * T) * P) := hfin
    _ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ (-(1 / 2 : ℝ)) + 2 * ((N : ℝ) ^ 2 * (3 ^ (e + t) + 2 * T) * (3 / 2 * E)) := by
        gcongr
    _ = _ := by simp only [T, E, F, M]; ring

/-- **Cassels second moment, base `b` coprime to 3, any law with the Riesz bound.**  Confidence 80%.

English proof.  `secondMoment_le_explicit` verbatim with `2 → b`: `secondMoment_expand` (base-free
up to `2ᵏ → bᵏ`) gives `Σ_{n,m} Bf free M (h(bⁿ − bᵐ))`; the pair `m < n` has frequency
`h(bᵈ − 1)·bᵐ`, `d = n − m`.  Good `d` (`e + v₃(bᵈ−1) + 1 ≤ F/2`, `e = v₃ h`): `good_shift` with
`sum_Hf_le_b` in place of `sum_Hf_le`, an extra `(3/2)ᵗ`.  Bad `d`: by
`padicValNat_pow_sub_one_le` they have `v₃(d) ≥ W − e − t`, so there are
`≤ N / 3^{W−e−t−1}` of them (`bad_count` with `3^{t}` more).  The explicit constant becomes
`(1 + 3(3^{e+t+1} + 2))(3/2)ᵗ ≤ 16·|h|·(9/2)ᵗ ≤ 16·|h|·b⁶` (`3ᵉ ≤ |h|`, `three_pow_tb_lt`). -/
theorem secondMoment_le_of_cf (free : ℕ → Bool) (Φ : (ℕ → Bool) → ℝ)
    (hGm : Measurable Φ) (hcf : ∀ M ξ, ‖∫ ω, ee (ξ * Φ ω) ∂coinMeasure‖ ≤ Bf free M ξ) {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) (h : ℤ)
    (hh : h ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * Φ ω)‖ ^ 2 ∂coinMeasure ≤
      16 * (b : ℝ) ^ 6 * |(h : ℝ)| * (N : ℝ) ^ 2 *
        (Real.exp (-(Real.log (3 / 2) / 2) * freeCount free (Nat.log 3 N / 2)) +
          (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  refine (secondMoment_le_explicit_of_cf free Φ hGm hcf hb h3 h hh N hN).trans ?_
  set e := padicValNat 3 h.natAbs
  set t := tb b
  set E := Real.exp (-(Real.log (3 / 2) / 2) * freeCount free (Nat.log 3 N / 2))
  set R := (N : ℝ) ^ (-(1 / 2 : ℝ))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hR : 0 ≤ R := by positivity
  have hN2 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have he : (3 : ℝ) ^ e ≤ |(h : ℝ)| := by
    have : 3 ^ e ≤ h.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hh) pow_padicValNat_dvd
    rw [← Int.cast_abs, ← Int.natCast_natAbs]; exact_mod_cast this
  have ht : (3 : ℝ) ^ t ≤ (b : ℝ) ^ 2 := by exact_mod_cast (three_pow_tb_lt hb).le
  have hT : (3 / 2 : ℝ) ^ t ≤ 3 ^ t := pow_le_pow_left₀ (by norm_num) (by norm_num) t
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
  have hh1 : (1 : ℝ) ≤ |(h : ℝ)| := le_trans (one_le_pow₀ (by norm_num)) he
  have hb2 : (b : ℝ) ^ 2 ≤ (b : ℝ) ^ 6 := pow_le_pow_right₀ hb1 (by norm_num)
  have hb6 : (1 : ℝ) ≤ (b : ℝ) ^ 6 := one_le_pow₀ hb1
  have h3t : (0 : ℝ) ≤ 3 ^ t := by positivity
  have hK : 3 * ((3 : ℝ) ^ (e + t) + 2 * (3 / 2 : ℝ) ^ t) ≤ 16 * (b : ℝ) ^ 6 * |(h : ℝ)| := by
    rw [pow_add]
    have : (3 : ℝ) ^ e * 3 ^ t ≤ |(h : ℝ)| * 3 ^ t := by gcongr
    have : |(h : ℝ)| * 3 ^ t ≤ |(h : ℝ)| * (b : ℝ) ^ 6 := by gcongr; linarith
    have : (1 : ℝ) * 3 ^ t ≤ |(h : ℝ)| * 3 ^ t := by gcongr
    nlinarith
  have h16 : (1 : ℝ) ≤ 16 * (b : ℝ) ^ 6 * |(h : ℝ)| := by nlinarith
  have := mul_le_mul_of_nonneg_right hK (mul_nonneg hN2 hE)
  have := mul_le_mul_of_nonneg_right h16 (mul_nonneg hN2 hR)
  nlinarith



/-- **Bases coprime to 3, a.e.**  Proved: `charFun_repReal` feeds the Cassels chain; the free set
is exactly `isFree`, so the summation is `ae_isNormal_of_coprime_three` verbatim. -/
theorem ae_isNormal_rep_of_coprime_three {b : ℕ} (hb : 2 ≤ b) (h3 : ¬ 3 ∣ b) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (repReal ω) := by
  refine ae_isNormal_of_secondMoment coinMeasure hb _ measurable_repReal sched
    sched_strictMono sched_ratio ?_
  intro h hh
  have hC : (0 : ℝ) < 16 * (b : ℝ) ^ 6 * |(h : ℝ)| := by
    have : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    positivity
  have hl : 0 < Real.log (3 / 2) / 2 := by have := Real.log_pos (by norm_num : (1:ℝ) < 3 / 2); linarith
  refine (summable_sched_bound _ _ hC hl).of_nonneg_of_le
    (fun j => div_nonneg (integral_nonneg fun ω => by positivity) (by positivity))
    (fun j => ?_)
  have hN : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ _ := secondMoment_le_of_cf isFree repReal measurable_repReal charFun_repReal hb h3 h hh
          (sched j) (one_le_sched j)
    _ = _ := by ring

/-! ## Powers of 3 (elementary) -/

/-- **Guard: no point of `K` is normal to `3ˢ`.** -/
theorem not_isNormal_rep_three_pow (ω : ℕ → Bool) {s : ℕ} (hs : 0 < s) :
    ¬ IsNormal (3 ^ s) (repReal ω) := by
  have : repReal ω = EntropyProfiles.cantorPt (fun i => if ω (src i) then 1 else 0) := by
    unfold repReal pt EntropyProfiles.cantorPt
    congr 1; funext i
    simp only [ptDigit, Bool.true_and]
    split_ifs <;> simp
  rw [this]
  exact EntropyProfiles.not_isNormal_three_pow_cantorPt _ hs

/-! ## The Liouville property -/

open CantorExpGeneric in
theorem pow_mul_tl (free ω : ℕ → Bool) (n : ℕ) :
    (3 : ℝ) ^ n * tl free ω n = ∑' k, (ptDigit free ω (k + n) : ℝ) / 3 ^ (k + 1) := by
  rw [tl, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [show k + n + 1 = (k + 1) + n by ring, pow_add]
  field_simp

open CantorExpGeneric in
/-- **Liouville property.**  Proved.  With `k = 2n`, `A = a_k`, `T = (k+2)A`: the coins
`ω''` that repeat the block `[A, 2A)` forever agree with `ω ∘ src` below `T`, so
`|x − r| ≤ 3^{-T}` for `r = pt ω''`; `r (3^{2A} − 3^A) = hd(2A) − hd(A)` by periodicity of the
tail; and `(3^{2A} − 3^A)^n < 3^{(2n+2)A}`.  Irrationality supplies `x ≠ r`. -/
theorem liouville_repReal (ω : ℕ → Bool) (hirr : Irrational (repReal ω)) :
    Liouville (repReal ω) := by
  intro n
  set A := runStart (2 * n) with hAdef
  set T := (2 * n + 2) * A with hTdef
  have hA1 : 1 ≤ A := by have := lt_runStart (2 * n); omega
  set ω' : ℕ → Bool := fun i => ω (src i) with hω'
  set ω'' : ℕ → Bool := fun i => if i < A then ω' i else ω' (A + (i - A) % A) with hω''
  have hblk : ∀ r, r < A → src (A + r) = A + r := by
    intro r hr
    rw [src_of_mem_run (k := 2 * n) (by omega) (by nlinarith), Nat.add_sub_cancel_left,
      Nat.mod_eq_of_lt hr]
  have hagree : ∀ i < T, ω'' i = ω' i := by
    intro i hi
    simp only [hω'']
    split_ifs with h
    · rfl
    · simp only [hω']
      rw [hblk _ (Nat.mod_lt _ (by omega)), src_of_mem_run (k := 2 * n) (by omega) (by omega)]
  have hper : ∀ m, ω'' (m + 2 * A) = ω'' (m + A) := by
    intro m
    simp only [hω'', show ¬ m + 2 * A < A by omega, show ¬ m + A < A by omega, if_false]
    congr 2
    rw [show m + 2 * A - A = m + A by omega, show m + A - A = m by omega, Nat.add_mod_right]
  obtain ⟨r, hrdef⟩ : ∃ r, r = pt (fun _ => true) ω'' := ⟨_, rfl⟩
  have hx := pt_split (fun _ => true) ω' T
  have hr := pt_split (fun _ => true) ω'' T
  rw [← hrdef] at hr
  have hhd : hd (fun _ => true) ω' T = hd (fun _ => true) ω'' T :=
    hd_congr _ _ _ _ fun j hj => by simp only [ptDigit, hagree j hj]
  have hclose : |repReal ω - r| ≤ 1 / 3 ^ T := by
    change |pt (fun _ => true) ω' - r| ≤ _
    rw [hx, hr, hhd, abs_le]
    have := tl_nonneg (fun _ => true) ω' T; have := tl_le (fun _ => true) ω' T
    have := tl_nonneg (fun _ => true) ω'' T; have := tl_le (fun _ => true) ω'' T
    constructor <;> linarith
  -- rationality of `r`
  have hA := pt_split (fun _ => true) ω'' A
  have h2A := pt_split (fun _ => true) ω'' (2 * A)
  rw [← hrdef] at hA h2A
  have htl : (3 : ℝ) ^ (2 * A) * tl (fun _ => true) ω'' (2 * A) =
      (3 : ℝ) ^ A * tl (fun _ => true) ω'' A := by
    rw [pow_mul_tl, pow_mul_tl]
    refine tsum_congr fun k => ?_
    simp only [ptDigit, hper]
  set a : ℤ := (hd (fun _ => true) ω'' (2 * A) : ℤ) - hd (fun _ => true) ω'' A
  set b : ℤ := 3 ^ (2 * A) - 3 ^ A
  have hb3 : (3 : ℤ) ^ A ≥ 3 := by
    calc (3 : ℤ) ^ A ≥ 3 ^ 1 := pow_le_pow_right₀ (by norm_num) hA1
      _ = 3 := by norm_num
  have hbeq : b = 3 ^ A * (3 ^ A - 1) := by simp only [b]; rw [two_mul, pow_add]; ring
  have hb1 : 1 < b := by rw [hbeq]; nlinarith
  have hbR : (b : ℝ) = 3 ^ (2 * A) - 3 ^ A := by simp [b]
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : (0 : ℤ) < b)
  have hrab : r = a / b := by
    rw [eq_div_iff hb0.ne', hbR]
    have e1 : r * 3 ^ (2 * A) = hd (fun _ => true) ω'' (2 * A) +
        3 ^ (2 * A) * tl (fun _ => true) ω'' (2 * A) := by
      rw [h2A]; field_simp
    have e2 : r * 3 ^ A = hd (fun _ => true) ω'' A + 3 ^ A * tl (fun _ => true) ω'' A := by
      rw [hA]; field_simp
    simp only [a]; push_cast
    linear_combination e1 - e2 + htl
  refine ⟨a, b, hb1, ?_, ?_⟩
  · exact hirr.ne_rational a b
  · rw [← hrab]
    refine hclose.trans_lt ?_
    have hbn : (b : ℝ) ^ n < 3 ^ T := by
      have h1 : (b : ℝ) < 3 ^ (2 * A) := by rw [hbR]; have : (0 : ℝ) < 3 ^ A := by positivity
                                            linarith
      calc (b : ℝ) ^ n ≤ ((3 : ℝ) ^ (2 * A)) ^ n := pow_le_pow_left₀ hb0.le h1.le n
        _ = 3 ^ (2 * A * n) := by rw [← pow_mul]
        _ < 3 ^ T := pow_lt_pow_right₀ (by norm_num) (by simp only [hTdef]; nlinarith)
    rw [one_div_lt_one_div (by positivity) (by positivity)]
    exact hbn

/-- **The copy-zone pair sum**: `Σ_{n,m<N} ∏_{i<A} |cos(2π (bⁿ − bᵐ) 3ⁱ/(3^A − 1))|`, the Riesz
form of `𝔼_W |Σ_{m<N} e(bᵐ W/(3^A−1))|²` over a random Cantor block `W` of length `A`. -/
noncomputable def copyPairSum (b A N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∏ i ∈ Finset.range A,
    |Real.cos (2 * Real.pi * (((b : ℝ) ^ n - (b : ℝ) ^ m) * 3 ^ i) / (3 ^ A - 1))|

/-- **Copy-zone pair term as a Cassels product.**  Proved: reindex `i ↦ A − 1 − i`; the block
coin `i` reads the frequency `ξ = (bⁿ − bᵐ)·3^A/(3^A − 1)` at depth `A − i`.  So the copy zone is
`Bf` with every place free, at the twisted frequency (for `|bⁿ − bᵐ| ≪ 3^A`, `ξ ≈ bⁿ − bᵐ` and
the low-digit count of `CantorLiouvilleAll` applies). -/
theorem copyPairSum_eq_Bf (b A N : ℕ) :
    copyPairSum b A N = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      Bf (fun _ => true) A (((b : ℝ) ^ n - (b : ℝ) ^ m) * 3 ^ A / (3 ^ A - 1)) := by
  unfold copyPairSum Bf
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  simp only [Finset.filter_true]
  rw [← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  congr 2
  have h3 : (3 : ℝ) ^ A = 3 ^ i * 3 ^ (A - 1 - i + 1) := by rw [← pow_add]; congr 1; omega
  rw [h3]
  field_simp
  rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add, show A - 1 - i + (i + 1) = i + (A - 1 - i + 1) by omega]

/-- **`Bf` is `π`-Lipschitz in the frequency.**  Proved (`abs_prod_sub_prod_le`, geometric sum). -/
theorem Bf_lip (free : ℕ → Bool) (M : ℕ) (ξ ξ' : ℝ) :
    |Bf free M ξ - Bf free M ξ'| ≤ Real.pi * |ξ - ξ'| := by
  unfold Bf
  have hb : ∀ x : ℝ, 0 ≤ |Real.cos x| ∧ |Real.cos x| ≤ 1 :=
    fun x => ⟨abs_nonneg _, Real.abs_cos_le_one _⟩
  refine (CantorExactExponentProfile.abs_prod_sub_prod_le _ _ _ (fun k => hb _)
    (fun k => hb _)).trans ?_
  have hterm : ∀ p : ℕ, |(|Real.cos (2 * Real.pi * ξ / 3 ^ (p + 1))| -
      |Real.cos (2 * Real.pi * ξ' / 3 ^ (p + 1))|)| ≤
      2 * Real.pi * |ξ - ξ'| * (1 / 3) ^ (p + 1) := by
    intro p
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ((Real.abs_cos_sub_cos_le _ _).trans (le_of_eq ?_))
    rw [show 2 * Real.pi * ξ / 3 ^ (p + 1) - 2 * Real.pi * ξ' / 3 ^ (p + 1) =
      (2 * Real.pi / 3 ^ (p + 1)) * (ξ - ξ') by ring, abs_mul, abs_of_pos (by positivity)]
    rw [one_div_pow]; ring
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset
    (fun p => free p = true) (Finset.range M))
    (f := fun p => 2 * Real.pi * |ξ - ξ'| * (1 / 3 : ℝ) ^ (p + 1)) (fun _ _ _ => by positivity)
  refine (Finset.sum_le_sum fun p _ => hterm p).trans (hsub.trans ?_)
  rw [← Finset.mul_sum]
  have hg : ∑ p ∈ Finset.range M, (1 / 3 : ℝ) ^ (p + 1) ≤ 1 / 2 := by
    have := geom_sum_mul (1 / 3 : ℝ) M
    have e : ∑ p ∈ Finset.range M, (1 / 3 : ℝ) ^ (p + 1) =
        (1 / 3) * ∑ p ∈ Finset.range M, (1 / 3 : ℝ) ^ p := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
    have : (0 : ℝ) ≤ (1 / 3) ^ M := by positivity
    rw [e]; nlinarith
  have : 0 ≤ 2 * Real.pi * |ξ - ξ'| := by positivity
  nlinarith

/-- **Copy term vs. untwisted frequency.**  Proved: each pair term is within
`π|bⁿ − bᵐ|/(3^A − 1)` of the plain Cassels term `Bf A (bⁿ − bᵐ)`; for pairs with
`|bⁿ − bᵐ| ≤ 3^{A/2}` the twist costs `O(3^{-A/2})`. -/
theorem copyTerm_le (A : ℕ) (hA : 1 ≤ A) (η : ℝ) :
    Bf (fun _ => true) A (η * 3 ^ A / (3 ^ A - 1)) ≤
      Bf (fun _ => true) A η + Real.pi * |η| / (3 ^ A - 1) := by
  have h3 : (1 : ℝ) < 3 ^ A := one_lt_pow₀ (by norm_num) (by omega)
  have := Bf_lip (fun _ => true) A (η * 3 ^ A / (3 ^ A - 1)) η
  have hne : (3 : ℝ) ^ A - 1 ≠ 0 := by linarith
  have e : η * 3 ^ A / (3 ^ A - 1) - η = η / (3 ^ A - 1) := by
    rw [div_sub' hne, div_left_inj' hne]; ring
  rw [e, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 3 ^ A - 1), ← mul_div_assoc] at this
  linarith [(abs_le.1 this).2]

/-- The cyclic Riesz product of an integer `η` modulo `3^A − 1` (its cyclic ternary digits). -/
noncomputable def cycProd (A : ℕ) (η : ℤ) : ℝ :=
  ∏ i ∈ Finset.range A, |Real.cos (2 * Real.pi * ((η : ℝ) * 3 ^ i) / (3 ^ A - 1))|

theorem cycProd_add (A : ℕ) (η j : ℤ) : cycProd A (η + j * (3 ^ A - 1)) = cycProd A η := by
  unfold cycProd
  refine Finset.prod_congr rfl fun i _ => ?_
  have hq : (3 : ℝ) ^ A - 1 ≠ 0 ∨ (3 : ℝ) ^ A - 1 = 0 := (em _).symm.imp id id |>.symm.elim
    (fun h => Or.inr h) (fun h => Or.inl h)
  rcases hq with hq | hq
  · have : 2 * Real.pi * (((η + j * (3 ^ A - 1) : ℤ) : ℝ) * 3 ^ i) / (3 ^ A - 1) =
        2 * Real.pi * ((η : ℝ) * 3 ^ i) / (3 ^ A - 1) + ((j * 3 ^ i : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast; field_simp; try ring
    rw [this, Real.cos_add_int_mul_two_pi]
  · simp [hq]

/-- **Rotation invariance**: multiplying by 3 cycles the digits.  Proved (`3^A ≡ 1`). -/
theorem cycProd_mul_three (A : ℕ) (η : ℤ) : cycProd A (3 * η) = cycProd A η := by
  rcases Nat.eq_zero_or_pos A with h0 | hA
  · subst h0; simp [cycProd]
  have hq : (3 : ℝ) ^ A - 1 ≠ 0 := by
    have : (1 : ℝ) < 3 ^ A := one_lt_pow₀ (by norm_num) (by omega)
    linarith
  unfold cycProd
  have hs : ∀ i ∈ Finset.range A, |Real.cos (2 * Real.pi * (((3 * η : ℤ) : ℝ) * 3 ^ i) / (3 ^ A - 1))| =
      |Real.cos (2 * Real.pi * ((η : ℝ) * 3 ^ ((i + 1) % A)) / (3 ^ A - 1))| := by
    intro i hi
    rw [Finset.mem_range] at hi
    rcases Nat.lt_or_ge (i + 1) A with h | h
    · rw [Nat.mod_eq_of_lt h]; push_cast; congr 3; ring
    · have hiA : i + 1 = A := by omega
      rw [hiA, Nat.mod_self, pow_zero]
      have : 2 * Real.pi * (((3 * η : ℤ) : ℝ) * 3 ^ i) / (3 ^ A - 1) =
          2 * Real.pi * ((η : ℝ) * 1) / (3 ^ A - 1) + (η : ℝ) * (2 * Real.pi) := by
        have k : ((3 * η : ℤ) : ℝ) * 3 ^ i = (η : ℝ) * 1 + η * (3 ^ A - 1) := by
          rw [← hiA, pow_succ]; push_cast; ring
        rw [k]; field_simp; try ring
      rw [this, Real.cos_add_int_mul_two_pi]
  rw [Finset.prod_congr rfl hs]
  obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by omega⟩
  set f : ℕ → ℝ := fun j => |Real.cos (2 * Real.pi * ((η : ℝ) * 3 ^ j) / (3 ^ (A' + 1) - 1))|
  change ∏ i ∈ Finset.range (A' + 1), f ((i + 1) % (A' + 1)) = ∏ i ∈ Finset.range (A' + 1), f i
  rw [Finset.prod_range_succ, Finset.prod_range_succ', Nat.mod_self]
  congr 1
  exact Finset.prod_congr rfl fun i hi => by
    rw [Nat.mod_eq_of_lt (by simp at hi; omega)]

theorem cycProd_mul_three_pow (A k : ℕ) (η : ℤ) : cycProd A (3 ^ k * η) = cycProd A η := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_comm _ (3 : ℤ), mul_assoc, cycProd_mul_three, ih]

theorem copyPairSum_eq_cycProd (b A N : ℕ) :
    copyPairSum b A N = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      cycProd A ((b : ℤ) ^ n - (b : ℤ) ^ m) := by
  unfold copyPairSum cycProd; push_cast; rfl

/-- **Only the `t`-part matters.**  Proved: for `b = 3ˢt` the pair term at `(m + d, m)` is the
cyclic product of `tᵐ(b^d − 1)`; the factor `3^{sm}` is a rotation (`cycProd_mul_three_pow`).
So the copy zone is a statement about `tᵐ mod 3^A − 1`. -/
theorem cycProd_pair (A s t m d : ℕ) :
    cycProd A (((3 ^ s * t : ℕ) : ℤ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℤ) ^ m) =
      cycProd A ((t : ℤ) ^ m * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1)) := by
  have e : ((3 ^ s * t : ℕ) : ℤ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℤ) ^ m =
      3 ^ (s * m) * ((t : ℤ) ^ m * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1)) := by push_cast; ring
  rw [e, cycProd_mul_three_pow]

/-- **Copy-zone decay (open conjecture, the copy-zone leaf of `ae_isNormal_rep_of_three_dvd`).**
For `b` not a power of 3 there are `C, δ > 0` with `copyPairSum b A N ≤ C N^{2−δ}` for
`A ≤ N ≤ A^{3}` (runs of polynomially many copies).  Evidence (`scripts/rep_copyzone.py`,
`N = 4A`, `A = 8..24`): `N⁻²·copyPairSum` is `.0116/.0108/.0105` for `b = 2, 6, 12` at `A = 24`,
which is the diagonal floor `1/N = .0104`; control `b = 9`: `.33 → .20`, no decay.  Would give
the copy zone of the crux (with the twist `3^{-A}` and the run-end truncation still to add). -/
def CopyZoneDecay (b : ℕ) : Prop :=
  ∃ C δ : ℝ, 0 < δ ∧ ∀ A N : ℕ, 1 ≤ A → A ≤ N → N ≤ A ^ 3 →
    copyPairSum b A N ≤ C * (N : ℝ) ^ (2 - δ)

/-- **Uniform orbit decay of cyclic digits (open conjecture; the residual leaf of
`CopyZoneDecay`, via `cycProd_pair` with `c = b^d − 1`).**  For `t ≥ 2` prime to 3: the orbit
`c tᵐ` (`m < N`, `A ≤ N ≤ A³`) has cyclic Riesz products summing to `O(N^{1−δ})`, uniformly in
`c` with `gcd(c, 3^A−1)² ≤ 3^A − 1`.  Evidence (`scripts/rep_single.py`, exhaustive max over `c`,
`N = 4A`): `t = 2`: `N·max = 2.3, 1.7, 1.6` at `A = 6, 8, 10` (bounded); control `t = 1`: mean
`.37` flat (`N·max ≍ N`).  Confidence 55%: this is a short-orbit digit statement for `tᵐ` modulo
`3^A − 1` (middle digits of powers once `tᵐ > 3^A`). -/
def TOrbitCyclicDecay (t : ℕ) : Prop :=
  ∃ C δ : ℝ, 0 < δ ∧ ∀ A N : ℕ, 1 ≤ A → A ≤ N → N ≤ A ^ 3 → ∀ c : ℤ,
    (Int.gcd c (3 ^ A - 1) : ℝ) ^ 2 ≤ 3 ^ A - 1 →
    ∑ m ∈ Finset.range N, cycProd A (c * (t : ℤ) ^ m) ≤ C * (N : ℝ) ^ (1 - δ)

/-! ## Bases `3ˢt`, `t > 1`: the crux -/

/-- **Crux: a.e. normality to `b = 3ˢt`, `t > 1`.**  Open; confidence 50%.

What is proved around it: bases prime to 3 (`ae_isNormal_rep_of_coprime_three`, the free coins
alone), powers of 3 fail (`not_isNormal_rep_three_pow`), and the known-false sibling `b = 9` is
excluded by the hypothesis.  Probe `scripts/rep_probe.py` (b = 6, ℓ = 40, 30 copies): the
copy stretch of a random block has base-6 digit and pair frequencies at the level of uniform
random digits; control `b = 9` fails (error .19–.24), and the special block `W = 2` fails at
3 copies (error .35).

Route (second moment along `sched`, then `CantorLiouvilleAll.ae_isNormal_of_secondMoment`).
Split the frequencies `bᵐ` by where the window `[sm, sm + m log₃ t]` of `bᵐx mod 1` sits:
1. *Free zone* (window in a gap of `isFree`): the profile thread's window/Cassels count, with the
   `t`-orbit mod `3ᵏ` (as in `CantorExactExponentProfile.ae_isNormal_of_profileOK`, step 3).
2. *Copy zone* (window inside run `k`, `A = a_k`): `bᵐx ≡ bᵐ 3^{-A} W/(3^A − 1) (mod 1)` up to
   `t^m 3^{sm−(k+2)A}`, with `W` the random block.  The pair term is the Riesz product over the
   block coins, `∏_{i<A} |cos(2π η 3ⁱ/(3^A−1))|`, `η = h(bⁿ − bᵐ) 3^{-A}` reduced mod `3^A − 1`:
   the cyclic ternary digits of `η`.  Needed: few pairs have `η` with few cyclic digit changes.
   This is a digits-of-`bᵐ`-modulo-`3^A − 1` statement; plain counting fails (`A^K` strings
   with `K` changes against `N ≈ kA` pairs per `n`), and so does the large sieve
   (`Σ_y |μ̂(y/q)|² = (3/2)^A` against an orbit of length `≈ kA`).  The cyclic structure with
   the low `3`-adic digits of `h tᵐ (b^d − 1)` (when it is `< 3^A`, the existing count applies)
   is the expected mechanism.
3. *Shadow zone* (`m ∈ [(k+2)A/log₃ b, (k+2)A/s]`, window straddling the run end): the free
   coins after the run read the top digits of `h tᵐ (b^d − 1)`, as in the profile thread's
   shadow (Baker input `Literature.BakerLogDiscrepancy`, `sum_topProd_le`).
-/
theorem ae_isNormal_rep_of_three_dvd {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) (hpow : ∀ s : ℕ, b ≠ 3 ^ s) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (repReal ω) := by
  sorry

theorem irrational_of_isNormal_two {x : ℝ} (hx : IsNormal 2 x) : Irrational x := by
  rintro ⟨q, rfl⟩
  have := isNormal_rat_mul_add 2 le_rfl (q : ℝ) 1 (-q) one_ne_zero hx
  push_cast at this
  rw [one_mul, add_neg_cancel] at this
  exact ExplicitPQ.not_isNormal_two_zero this

/-- **The full profile, almost surely.** -/
theorem ae_repProfile : ∀ᵐ ω ∂coinMeasure,
    ∀ b : ℕ, 2 ≤ b → (IsNormal b (repReal ω) ↔ ∀ s : ℕ, b ≠ 3 ^ s) := by
  have hall : ∀ᵐ ω ∂coinMeasure, ∀ b : ℕ, 2 ≤ b → (∀ s : ℕ, b ≠ 3 ^ s) →
      IsNormal b (repReal ω) := by
    rw [ae_all_iff]
    intro b
    by_cases hb : 2 ≤ b
    · by_cases hp : ∀ s : ℕ, b ≠ 3 ^ s
      · by_cases h3 : 3 ∣ b
        · filter_upwards [ae_isNormal_rep_of_three_dvd hb h3 hp] with ω hω _ _ using hω
        · filter_upwards [ae_isNormal_rep_of_coprime_three hb h3] with ω hω _ _ using hω
      · exact Eventually.of_forall fun ω _ h => absurd h hp
    · exact Eventually.of_forall fun ω h => absurd h hb
  filter_upwards [hall] with ω hω b hb
  refine ⟨fun hn s hs => ?_, hω b hb⟩
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · subst h0; rw [hs] at hb; norm_num at hb
  · exact not_isNormal_rep_three_pow ω h0 (hs ▸ hn)

/-- **The cut is not forced (Liouville case).**  Wiring (proved) from `ae_repProfile`, whose only
open input is the crux `ae_isNormal_rep_of_three_dvd`. -/
theorem liouvilleCantorFullProfile : LiouvilleCantorFullProfile := by
  obtain ⟨ω, hω⟩ := ae_repProfile.exists
  have h2 : IsNormal 2 (repReal ω) := (hω 2 le_rfl).2 fun s hs => by
    rcases s with _ | s
    · norm_num at hs
    · have : 3 ∣ 2 := hs ▸ dvd_pow_self 3 (Nat.succ_ne_zero s)
      norm_num at this
  exact ⟨repReal ω, repReal_mem_cantorSet ω,
    liouville_repReal ω (irrational_of_isNormal_two h2), hω⟩

end NormalNumbers.CantorRepetition

