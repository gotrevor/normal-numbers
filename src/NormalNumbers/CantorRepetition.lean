/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorExactExponentProfile
import NormalNumbers.EntropyProfiles
import NormalNumbers.ExplicitPQ
import NormalNumbers.LevinSparse

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

/-- **Peeling one coin.**  Proved: flipping coin `j` preserves `coinMeasure`
(`LevinSparse.measurePreserving_flipAt`), so averaging the two values of `ω j` gives the factor
`(1 + e(a))/2`, of modulus `|cos πa|`.  This factorizes the law of `repReal` over the block coins
of a run (each block coin enters with weight `w_j = 2 Σ_c 3^{-(j+cA)-1}`). -/
theorem integral_ee_flip (j : ℕ) (a : ℝ) (Y : (ℕ → Bool) → ℝ) (hY : Measurable Y)
    (hinv : ∀ ω, Y (LevinSparse.flipAt j ω) = Y ω) :
    ∫ ω, ee (a * (if ω j then 1 else 0) + Y ω) ∂coinMeasure =
      (1 + ee a) / 2 * ∫ ω, ee (Y ω) ∂coinMeasure := by
  have hmp := LevinSparse.measurePreserving_flipAt j
  have hm : Measurable fun ω : ℕ → Bool => (if ω j then (1 : ℝ) else 0) :=
    (measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp (measurable_pi_apply j)
  have hint : ∀ f : (ℕ → Bool) → ℝ, Measurable f → Integrable (fun ω => ee (f ω)) coinMeasure :=
    fun f hf => Integrable.of_bound ((measurable_ee.comp hf).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => (norm_ee _).le)
  have hflip : ∫ ω, ee (a * (if ω j then 1 else 0) + Y ω) ∂coinMeasure =
      ∫ ω, ee (a * (if ω j then 0 else 1) + Y ω) ∂coinMeasure := by
    have hinvol : Function.Involutive (LevinSparse.flipAt j) := fun ω => by
      funext i; by_cases h : i = j
      · subst h; simp [LevinSparse.flipAt]
      · simp [LevinSparse.flipAt, Function.update_of_ne h]
    have he : MeasurableEmbedding (LevinSparse.flipAt j) :=
      (MeasurableEquiv.ofInvolutive _ hinvol hmp.measurable).measurableEmbedding
    rw [← hmp.integral_comp he]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hinv]
    congr 2
    cases h : ω j <;> simp [LevinSparse.flipAt, h]
  have hm' : Measurable fun ω : ℕ → Bool => (if ω j then (0 : ℝ) else 1) :=
    (measurable_of_countable (fun b : Bool => if b then (0 : ℝ) else 1)).comp (measurable_pi_apply j)
  have hsum := integral_add (hint (fun ω => a * (if ω j then 1 else 0) + Y ω) ((hm.const_mul a).add hY))
    (hint (fun ω => a * (if ω j then 0 else 1) + Y ω) ((hm'.const_mul a).add hY))
  have hpt : ∀ ω : ℕ → Bool, ee (a * (if ω j then 1 else 0) + Y ω) +
      ee (a * (if ω j then 0 else 1) + Y ω) = (1 + ee a) * ee (Y ω) := by
    intro ω
    simp only [ee_add]
    cases ω j <;> simp [ee] <;> ring
  simp only [hpt] at hsum
  rw [integral_const_mul, ← hflip] at hsum
  linear_combination -hsum / 2

/-- **Peeling a finite set of coins.**  Proved (induction with `integral_ee_flip`). -/
theorem norm_integral_ee_le_prod (S : Finset ℕ) (w : ℕ → ℝ) : ∀ (Y : (ℕ → Bool) → ℝ),
    Measurable Y → (∀ j ∈ S, ∀ ω, Y (LevinSparse.flipAt j ω) = Y ω) →
    ‖∫ ω, ee (∑ j ∈ S, w j * (if ω j then 1 else 0) + Y ω) ∂coinMeasure‖ ≤
      ∏ j ∈ S, |Real.cos (Real.pi * w j)| := by
  induction S using Finset.induction_on with
  | empty =>
    intro Y _ _
    simp only [Finset.sum_empty, zero_add, Finset.prod_empty]
    exact (norm_integral_le_of_norm_le_const (C := 1)
      (Eventually.of_forall fun ω => (norm_ee _).le)).trans (by simp)
  | insert a S ha ih =>
    intro Y hY hinv
    have hfl : ∀ ω, (LevinSparse.flipAt a ω) a = !ω a := fun ω => by simp [LevinSparse.flipAt]
    have hfl' : ∀ ω i, i ≠ a → (LevinSparse.flipAt a ω) i = ω i := fun ω i h => by
      simp [LevinSparse.flipAt, Function.update_of_ne h]
    set Y' : (ℕ → Bool) → ℝ := fun ω => ∑ j ∈ S, w j * (if ω j then 1 else 0) + Y ω
    have hY' : Measurable Y' := (Finset.measurable_sum _ fun j _ =>
      ((measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp
        (measurable_pi_apply j)).const_mul _).add hY
    have hinv' : ∀ ω, Y' (LevinSparse.flipAt a ω) = Y' ω := by
      intro ω
      simp only [Y', hinv a (Finset.mem_insert_self a S)]
      congr 1
      exact Finset.sum_congr rfl fun j hj => by rw [hfl' ω j (fun h => ha (h ▸ hj))]
    have e := integral_ee_flip a (w a) Y' hY' hinv'
    have : ∀ ω, ∑ j ∈ insert a S, w j * (if ω j then 1 else 0) + Y ω =
        w a * (if ω a then 1 else 0) + Y' ω := fun ω => by
      rw [Finset.sum_insert ha]; simp only [Y']; ring
    simp_rw [this]
    rw [e, norm_mul, Finset.prod_insert ha, norm_one_add_ee_div_two]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact ih Y hY fun j hj ω => hinv j (Finset.mem_insert_of_mem hj) ω

/-- Total weight of coin `j` in `repReal`: `Σ_{i : src i = j} 2·3^{-(i+1)}`. -/
noncomputable def srcWeight (j : ℕ) : ℝ :=
  ∑' i, if src i = j then 2 / (3 : ℝ) ^ (i + 1) else 0

theorem summable_two_div_pow : Summable fun i : ℕ => 2 / (3 : ℝ) ^ (i + 1) :=
  (CantorExpGeneric.tsum_two_geom 0).1.congr fun i => by simp

theorem summable_ite_le {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 2 / (3 : ℝ) ^ (i + 1)) :
    Summable f :=
  Summable.of_nonneg_of_le (fun i => (hf i).1) (fun i => (hf i).2) summable_two_div_pow

/-- **Coin decomposition of `repReal`.**  Proved: for any finite set `S` of coins,
`repReal = Σ_{j∈S} [ω j]·srcWeight j + (digits not reading `S`)`. -/
theorem repReal_eq_sum (S : Finset ℕ) (ω : ℕ → Bool) :
    repReal ω = ∑ j ∈ S, srcWeight j * (if ω j then 1 else 0) +
      ∑' i, (if src i ∈ S then 0 else (if ω (src i) then 2 else 0) / (3 : ℝ) ^ (i + 1)) := by
  have hb : ∀ i, (0 : ℝ) ≤ 2 / (3 : ℝ) ^ (i + 1) := fun i => by positivity
  have hsj : ∀ j, Summable fun i => if src i = j then 2 / (3 : ℝ) ^ (i + 1) else 0 := fun j =>
    summable_ite_le fun i => by split_ifs <;> simp [hb i]
  have hrest : Summable fun i =>
      (if src i ∈ S then 0 else (if ω (src i) then 2 else 0) / (3 : ℝ) ^ (i + 1)) :=
    summable_ite_le fun i => by split_ifs <;> simp [hb i]
  have hfin : ∑ j ∈ S, srcWeight j * (if ω j then 1 else 0) =
      ∑' i, ∑ j ∈ S, (if src i = j then 2 / (3 : ℝ) ^ (i + 1) else 0) * (if ω j then 1 else 0) := by
    rw [Summable.tsum_finsetSum (fun j _ => (hsj j).mul_right _)]
    exact Finset.sum_congr rfl fun j _ => by rw [srcWeight, tsum_mul_right]
  have hfs : Summable fun i => ∑ j ∈ S,
      (if src i = j then 2 / (3 : ℝ) ^ (i + 1) else 0) * (if ω j then 1 else 0) :=
    summable_sum fun j _ => (hsj j).mul_right _
  rw [hfin, ← hfs.tsum_add hrest]
  unfold repReal pt realOfDigits
  simp only [Nat.cast_ofNat]
  refine tsum_congr fun i => ?_
  simp only [ptDigit, Bool.true_and]
  by_cases hS : src i ∈ S
  · rw [if_pos hS, add_zero, Finset.sum_eq_single (src i)]
    · simp only [if_true]; split_ifs <;> simp
    · intro j _ hj; rw [if_neg (Ne.symm hj), zero_mul]
    · intro h; exact absurd hS h
  · rw [if_neg hS, Finset.sum_eq_zero, zero_add]
    · split_ifs <;> simp
    · intro j hj; rw [if_neg (fun (h : src i = j) => hS (h ▸ hj)), zero_mul]

/-- **Block-coin Riesz bound for the true law.**  Proved: `‖𝔼 e(ξ·repReal)‖ ≤
∏_{j∈S} |cos(π ξ srcWeight j)|` for any finite set of coins. -/
theorem norm_charFun_repReal_le (S : Finset ℕ) (ξ : ℝ) :
    ‖∫ ω, ee (ξ * repReal ω) ∂coinMeasure‖ ≤ ∏ j ∈ S, |Real.cos (Real.pi * (ξ * srcWeight j))| := by
  set Y : (ℕ → Bool) → ℝ := fun ω => ξ * ∑' i,
    (if src i ∈ S then 0 else (if ω (src i) then 2 else 0) / (3 : ℝ) ^ (i + 1))
  have hY : Measurable Y := by
    refine (Measurable.tsum fun i => ?_).const_mul ξ
    by_cases h : src i ∈ S
    · simp only [h, if_true]; exact measurable_const
    · simp only [h, if_false]
      exact ((measurable_of_countable (fun b : Bool => if b then (2 : ℝ) else 0)).comp
        (measurable_pi_apply (src i))).div_const _
  have hinv : ∀ j ∈ S, ∀ ω, Y (LevinSparse.flipAt j ω) = Y ω := by
    intro j hj ω
    simp only [Y]; congr 1
    refine tsum_congr fun i => ?_
    by_cases h : src i ∈ S
    · simp [h]
    · have : src i ≠ j := fun e => h (e ▸ hj)
      simp [h, LevinSparse.flipAt, Function.update_of_ne this]
  have := norm_integral_ee_le_prod S (fun j => ξ * srcWeight j) Y hY hinv
  refine le_of_eq_of_le ?_ this
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [Y]
  rw [repReal_eq_sum S ω, mul_add, Finset.mul_sum]
  congr 2
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Who reads a block coin.**  Proved: for `j` in the block `[a_k, 2a_k)` of run `k`, the
positions reading coin `j` are exactly its copies `j + c·a_k`, `c ≤ k`. -/
theorem src_eq_iff_block {k j i : ℕ} (h1 : runStart k ≤ j) (h2 : j < 2 * runStart k) :
    src i = j ↔ ∃ c ∈ Finset.range (k + 1), i = j + c * runStart k := by
  have hj2 : j < (k + 2) * runStart k := by nlinarith
  have hpos : 0 < runStart k := (Nat.zero_le k).trans_lt (lt_runStart k)
  constructor
  · intro h
    by_cases hf : isFree i = true
    · rw [src_of_free hf] at h
      subst h
      have := isForced_of_mem_run h1 hj2
      simp [isFree, this] at hf
    · obtain ⟨k', h1', h2'⟩ := exists_run_of_not_free (by simpa using hf)
      have hpos' : 0 < runStart k' := (Nat.zero_le k').trans_lt (lt_runStart k')
      rw [src_of_mem_run h1' h2'] at h
      have hm := Nat.mod_lt (i - runStart k') hpos'
      have hk : k' = k := by
        have e1 := runIdx_eq (k := k') (i := j) (by omega) (by nlinarith)
        rw [runIdx_eq h1 hj2] at e1; exact e1.symm
      subst hk
      refine ⟨(i - runStart k') / runStart k', Finset.mem_range.2 ?_, ?_⟩
      · have : (i - runStart k') / runStart k' < k' + 1 := by
          rw [Nat.div_lt_iff_lt_mul hpos']
          have e : (k' + 2) * runStart k' = (k' + 1) * runStart k' + runStart k' := by ring
          omega
        exact this
      · have := Nat.div_add_mod (i - runStart k') (runStart k')
        rw [mul_comm] at this
        omega
  · rintro ⟨c, hc, rfl⟩
    rw [Finset.mem_range] at hc
    have hi2 : j + c * runStart k < (k + 2) * runStart k := by nlinarith
    rw [src_of_mem_run (by omega) hi2]
    have : j + c * runStart k - runStart k = (j - runStart k) + c * runStart k := by omega
    rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- **Weight of a block coin.**  Proved: `srcWeight j = Σ_{c≤k} 2·3^{-(j+c a_k)-1}`. -/
theorem srcWeight_block {k j : ℕ} (h1 : runStart k ≤ j) (h2 : j < 2 * runStart k) :
    srcWeight j = ∑ c ∈ Finset.range (k + 1), 2 / (3 : ℝ) ^ (j + c * runStart k + 1) := by
  have hpos : 0 < runStart k := (Nat.zero_le k).trans_lt (lt_runStart k)
  set T := (Finset.range (k + 1)).image fun c => j + c * runStart k
  have hinj : Set.InjOn (fun c => j + c * runStart k) (Finset.range (k + 1) : Set ℕ) :=
    fun a _ b _ h => by
      have : a * runStart k = b * runStart k := by simpa using h
      exact Nat.eq_of_mul_eq_mul_right hpos this
  unfold srcWeight
  rw [tsum_eq_sum (s := T) fun i hi => by
    rw [if_neg]; intro h; exact hi (Finset.mem_image.2 (by
      obtain ⟨c, hc, e⟩ := (src_eq_iff_block h1 h2).1 h; exact ⟨c, hc, e.symm⟩))]
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [if_pos ((src_eq_iff_block h1 h2).2 ⟨c, hc, rfl⟩)]

/-- **Block-coin product is a cyclic Riesz product.**  Proved: over the block of run `k`
(`a = a_k`), `∏_j |cos(π ξ srcWeight j)| = ∏_{i<a} |cos(2π η 3ⁱ/(3^a − 1))|` with the real
frequency `η = ξ(1 − 3^{-(k+1)a})/3^a` (coin `a + r` is cyclic place `a − 1 − r`). -/
theorem prod_block_eq_cyc (k : ℕ) (ξ : ℝ) :
    ∏ j ∈ Finset.Ico (runStart k) (2 * runStart k),
        |Real.cos (Real.pi * (ξ * srcWeight j))| =
      ∏ i ∈ Finset.range (runStart k), |Real.cos (2 * Real.pi *
        ((ξ * (1 - (3 : ℝ) ^ (-(((k + 1) * runStart k : ℕ) : ℤ))) / 3 ^ runStart k) * 3 ^ i) /
          (3 ^ runStart k - 1))| := by
  set a := runStart k with ha
  have hpos : 0 < a := (Nat.zero_le k).trans_lt (lt_runStart k)
  rw [show 2 * a = a + a by ring, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    ← Finset.prod_range_reflect]
  refine Finset.prod_congr rfl fun r hr => ?_
  rw [Finset.mem_range] at hr
  rw [srcWeight_block (k := k) (j := a + (a - 1 - r)) (by omega) (by omega)]
  congr 2
  have h3a : (1 : ℝ) < 3 ^ a := one_lt_pow₀ (by norm_num) (by omega)
  have hne : (3 : ℝ) ^ a - 1 ≠ 0 := by linarith
  -- geometric sum
  have hgeom : ∑ c ∈ Finset.range (k + 1), 2 / (3 : ℝ) ^ (a + (a - 1 - r) + c * a + 1) =
      2 / 3 ^ (a + (a - 1 - r) + 1) * ∑ c ∈ Finset.range (k + 1), ((3 : ℝ) ^ a)⁻¹ ^ c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inv_pow, ← pow_mul, show a + (a - 1 - r) + c * a + 1 = (a + (a - 1 - r) + 1) + a * c by ring,
      pow_add]
    field_simp
  have hq : ((3 : ℝ) ^ a)⁻¹ ≠ 1 := by
    intro h; have := inv_eq_one.1 h; linarith
  rw [hgeom, geom_sum_eq hq]
  have hz : (3 : ℝ) ^ (-(((k + 1) * a : ℕ) : ℤ)) = ((3 : ℝ) ^ a)⁻¹ ^ (k + 1) := by
    rw [zpow_neg, zpow_natCast, inv_pow, ← pow_mul, mul_comm]
  rw [hz]
  have hi : (3 : ℝ) ^ (a - 1 - r) * 3 ^ (r + 1) = 3 ^ a := by rw [← pow_add]; congr 1; omega
  have e1 : (3 : ℝ) ^ (a + (a - 1 - r) + 1) = 3 ^ a * 3 ^ (a - 1 - r) * 3 := by
    rw [pow_succ, pow_add]
  rw [e1]
  have hX : (0 : ℝ) < 3 ^ r := by positivity
  have hi' : (3 : ℝ) ^ (a - 1 - r) * 3 ^ r * 3 = 3 ^ a := by rw [← hi, pow_succ]; ring
  have hP0 : (0 : ℝ) < 3 ^ (a - 1 - r) := by positivity
  clear hi hgeom hz e1
  generalize ((3 : ℝ) ^ a)⁻¹ ^ (k + 1) = Z
  generalize (3 : ℝ) ^ a = Q at *
  generalize (3 : ℝ) ^ (a - 1 - r) = P at *
  generalize (3 : ℝ) ^ r = X at *
  subst hi'
  have hP : P ≠ 0 := hP0.ne'
  have hX' : X ≠ 0 := hX.ne'
  have h1 : (P * X * 3)⁻¹ - 1 ≠ 0 := sub_ne_zero.2 hq
  have h2 : 1 - P * X * 3 ≠ 0 := by linarith
  field_simp
  ring

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

/-- **Few shifts `d` with a large common factor (open; believed, 75%).**  Shifts `d < N` with
`gcd(b^d − 1, 3^A − 1)² > 3^A − 1` number `O(N^{1−δ})`.  Evidence (`A ≤ 14`, `N = A³`): for
`b = 2, 6, 12` the bad `d` are multiples of one order (e.g. `b = 6, A = 12`: `36ℤ`, 47 of 1728),
at most 66 of 1000.  Mechanism: a bad `d` has `b^d ≡ 1` modulo a divisor `> 3^{A/2}`, so its order
there is `≥ A log 3/(2 log b)`. -/
def BadGcdSparse (b : ℕ) : Prop :=
  ∃ C δ : ℝ, 0 < δ ∧ ∀ A N : ℕ, 1 ≤ A → A ≤ N → N ≤ A ^ 3 →
    (((Finset.Ico 1 N).filter fun d =>
      ¬ ((Int.gcd ((b : ℤ) ^ d - 1) (3 ^ A - 1) : ℝ) ^ 2 ≤ 3 ^ A - 1)).card : ℝ) ≤
      C * (N : ℝ) ^ (1 - δ)

/-- The cyclic Riesz product at a real frequency. -/
noncomputable def cycProdR (A : ℕ) (η : ℝ) : ℝ :=
  ∏ i ∈ Finset.range A, |Real.cos (2 * Real.pi * (η * 3 ^ i) / (3 ^ A - 1))|

theorem cycProdR_intCast (A : ℕ) (η : ℤ) : cycProdR A η = cycProd A η := rfl

/-- **The cyclic product is `π`-Lipschitz.**  Proved (`Σ_{i<A} 3ⁱ = (3^A − 1)/2`). -/
theorem cycProdR_lip (A : ℕ) (η η' : ℝ) :
    |cycProdR A η - cycProdR A η'| ≤ Real.pi * |η - η'| := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · simp [cycProdR]; positivity
  have h3 : (1 : ℝ) < 3 ^ A := one_lt_pow₀ (by norm_num) (by omega)
  have hQ : (0 : ℝ) < 3 ^ A - 1 := by linarith
  have hb : ∀ x : ℝ, 0 ≤ |Real.cos x| ∧ |Real.cos x| ≤ 1 :=
    fun x => ⟨abs_nonneg _, Real.abs_cos_le_one _⟩
  unfold cycProdR
  refine (CantorExactExponentProfile.abs_prod_sub_prod_le _ _ _ (fun k => hb _)
    (fun k => hb _)).trans ?_
  have hterm : ∀ i : ℕ, |(|Real.cos (2 * Real.pi * (η * 3 ^ i) / (3 ^ A - 1))| -
      |Real.cos (2 * Real.pi * (η' * 3 ^ i) / (3 ^ A - 1))|)| ≤
      2 * Real.pi * |η - η'| / (3 ^ A - 1) * 3 ^ i := by
    intro i
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ((Real.abs_cos_sub_cos_le _ _).trans (le_of_eq ?_))
    rw [show 2 * Real.pi * (η * 3 ^ i) / (3 ^ A - 1) - 2 * Real.pi * (η' * 3 ^ i) / (3 ^ A - 1) =
      (2 * Real.pi * 3 ^ i / (3 ^ A - 1)) * (η - η') by ring, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi * 3 ^ i / (3 ^ A - 1))]
    ring
  refine (Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  have hg : ∑ i ∈ Finset.range A, (3 : ℝ) ^ i = (3 ^ A - 1) / 2 := by
    have := geom_sum_mul (3 : ℝ) A; linarith
  rw [hg]; field_simp

/-- **True-law copy-zone bound.**  Proved: for every run `k` (`a = a_k`) and every integer
`η₀`, `‖𝔼 e(ξ·repReal)‖ ≤ cycProd a η₀ + π |ξ(1 − 3^{-(k+1)a})/3^a − η₀|`.  The pair term of
the second moment at `ξ = h(bⁿ − bᵐ)` is the cyclic product of the nearest integer frequency. -/
theorem norm_charFun_repReal_le_cyc (k : ℕ) (ξ : ℝ) (η₀ : ℤ) :
    ‖∫ ω, ee (ξ * repReal ω) ∂coinMeasure‖ ≤ cycProd (runStart k) η₀ + Real.pi *
      |ξ * (1 - (3 : ℝ) ^ (-(((k + 1) * runStart k : ℕ) : ℤ))) / 3 ^ runStart k - η₀| := by
  have h1 := norm_charFun_repReal_le (Finset.Ico (runStart k) (2 * runStart k)) ξ
  rw [prod_block_eq_cyc] at h1
  have h2 := cycProdR_lip (runStart k)
    (ξ * (1 - (3 : ℝ) ^ (-(((k + 1) * runStart k : ℕ) : ℤ))) / 3 ^ runStart k) η₀
  rw [cycProdR_intCast] at h2
  have := (abs_le.1 h2).2
  exact h1.trans (by unfold cycProdR at this; linarith)

/-- **Copy-zone bound at an integer frequency divisible by `3^a`.**  Proved: if `z = 3^a η₀`,
then `‖𝔼 e(z·repReal)‖ ≤ cycProd a η₀ + π |z| 3^{-(k+2)a}`.  For `z = h(bⁿ − bᵐ)` with
`b = 3ˢt` and `sm ≥ a` this is the copy-zone pair term, error negligible while
`|z| ≪ 3^{(k+2)a}` (the frequency's window stays inside run `k`). -/
theorem norm_charFun_repReal_le_cyc_int (k : ℕ) (η₀ : ℤ) :
    ‖∫ ω, ee (((3 : ℝ) ^ runStart k * η₀) * repReal ω) ∂coinMeasure‖ ≤
      cycProd (runStart k) η₀ +
        Real.pi * |(3 : ℝ) ^ runStart k * η₀| / 3 ^ ((k + 2) * runStart k) := by
  refine (norm_charFun_repReal_le_cyc k _ η₀).trans (le_of_eq ?_)
  congr 1
  have h3 : (0 : ℝ) < 3 ^ runStart k := by positivity
  have hz : (3 : ℝ) ^ (-(((k + 1) * runStart k : ℕ) : ℤ)) =
      3 ^ runStart k / 3 ^ ((k + 2) * runStart k) := by
    rw [zpow_neg, zpow_natCast, show (k + 2) * runStart k = runStart k + (k + 1) * runStart k by ring,
      pow_add]
    field_simp
  rw [hz, show (3 : ℝ) ^ runStart k * η₀ * (1 - 3 ^ runStart k / 3 ^ ((k + 2) * runStart k)) /
      3 ^ runStart k - η₀ = -(3 ^ runStart k * η₀ / 3 ^ ((k + 2) * runStart k)) by
    field_simp; ring, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ ((k + 2) * runStart k))]
  ring

/-- **Corvaja–Zannier gcd bound, specialized to `u = b^d`, `v = 3^A` (literature hypothesis).**
Corvaja–Zannier (Monatsh. Math. 144 (2005); see also Bugeaud–Corvaja–Zannier, Math. Z. 243
(2003)): for a finite set of primes `S` and `ε > 0`, all `S`-unit integers `α, β` satisfy, outside
a finite exceptional set, either a relation `α^m = β^n` with `1 ≤ max(m,n) ≤ ε⁻¹`, or
`gcd(α − 1, β − 1) ≤ max(|α|, |β|)^ε`.  This is the instance `α = b^d`, `β = 3^A` (weaker: a
finite set of `(α, β)` gives a bound `D` on `max(d, A)`).  Transcription checked against the
statement quoted in arXiv:1505.03957; the source itself not read (no egress). -/
def CZGcdPow (b : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, ∀ d A : ℕ, D ≤ max d A →
    (∀ m n : ℕ, 1 ≤ max m n → (max m n : ℝ) ≤ 1 / ε → (b : ℤ) ^ (d * m) ≠ 3 ^ (A * n)) →
    (Int.gcd ((b : ℤ) ^ d - 1) (3 ^ A - 1) : ℝ) ≤ (max ((b : ℝ) ^ d) (3 ^ A)) ^ ε

theorem eq_three_pow_of_pow_eq {b k j : ℕ} (hk : 1 ≤ k) (h : b ^ k = 3 ^ j) : ∃ s, b = 3 ^ s := by
  have : b ∣ 3 ^ j := h ▸ dvd_pow_self b (by omega)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 this
  exact ⟨i, hi⟩

/-- **Short shifts have small gcd (from Corvaja–Zannier).**  Proved: if `b` is not a power of 3,
then for every `ε > 0` and all large `A`, every shift `1 ≤ d` with `b^d ≤ 3^A` has
`gcd(b^d − 1, 3^A − 1) ≤ 3^{εA}`.  So (for large `A`) `BadGcdSparse`'s bad shifts all have
`b^d > 3^A`; the open part is the long shifts `d > A log₃ b⁻¹·…`, where the bound
`max(b^d,3^A)^ε` is too weak.  In the crux, run `k` uses shifts up to `≈ (k+2)a/log₃ b`, so this
covers bounded `k` only. -/
theorem gcd_small_of_CZ {b : ℕ} (hb : 2 ≤ b) (hpow : ∀ s : ℕ, b ≠ 3 ^ s) (hCZ : CZGcdPow b)
    {ε : ℝ} (hε : 0 < ε) : ∃ A₀ : ℕ, ∀ A d : ℕ, A₀ ≤ A → 1 ≤ d → (b : ℝ) ^ d ≤ 3 ^ A →
      (Int.gcd ((b : ℤ) ^ d - 1) (3 ^ A - 1) : ℝ) ≤ (3 : ℝ) ^ (ε * A) := by
  obtain ⟨D, hD⟩ := hCZ ε hε
  refine ⟨max D 1, fun A d hA hd hbd => ?_⟩
  have hA1 : 1 ≤ A := (le_max_right _ _).trans hA
  have h := hD d A (le_max_of_le_right ((le_max_left _ _).trans hA)) (fun m n hmn _ heq => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hn0 : n ≠ 0 := by intro h0; subst h0; simp at hmn
      have : (1 : ℤ) = 3 ^ (A * n) := by simpa using heq
      have h2 : (3 : ℤ) ^ (A * n) = 1 := this.symm
      rw [pow_eq_one_iff_of_ne_zero (Nat.mul_ne_zero (by omega) hn0)] at h2
      norm_num at h2
    · have heq' : b ^ (d * m) = 3 ^ (A * n) := by exact_mod_cast heq
      obtain ⟨s, hs⟩ := eq_three_pow_of_pow_eq (Nat.one_le_iff_ne_zero.2
        (Nat.mul_ne_zero (by omega) (by omega))) heq'
      exact hpow s hs)
  refine h.trans (le_of_eq ?_)
  rw [max_eq_right hbd, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]

theorem cycProd_neg (A : ℕ) (η : ℤ) : cycProd A (-η) = cycProd A η := by
  unfold cycProd
  refine Finset.prod_congr rfl fun i _ => ?_
  push_cast
  rw [show 2 * Real.pi * (-(η : ℝ) * 3 ^ i) / (3 ^ A - 1) =
    -(2 * Real.pi * ((η : ℝ) * 3 ^ i) / (3 ^ A - 1)) by ring, Real.cos_neg]

theorem cycProd_nonneg (A : ℕ) (η : ℤ) : 0 ≤ cycProd A η :=
  Finset.prod_nonneg fun _ _ => abs_nonneg _

theorem cycProd_le_one (A : ℕ) (η : ℤ) : cycProd A η ≤ 1 :=
  Finset.prod_le_one (fun _ _ => abs_nonneg _) fun _ _ => Real.abs_cos_le_one _

/-- **Copy-zone decay from the two leaves.**  Proved: `pair_sum_le` with
`G d m = cycProd(tᵐ(b^d − 1))` (`cycProd_pair`, `cycProd_neg`); good shifts by
`TOrbitCyclicDecay t`, bad shifts trivially and counted by `BadGcdSparse`. -/
theorem copyZoneDecay_of {s t : ℕ} (hT : TOrbitCyclicDecay t) (hS : BadGcdSparse (3 ^ s * t)) :
    CopyZoneDecay (3 ^ s * t) := by
  obtain ⟨C, δ, hδ, hC⟩ := hT
  obtain ⟨C', δ', hδ', hC'⟩ := hS
  set b := 3 ^ s * t with hbdef
  set δ'' := min (min δ δ') 1
  have hδ''0 : 0 < δ'' := lt_min (lt_min hδ hδ') one_pos
  refine ⟨1 + 2 * |C| + 2 * |C'|, δ'', hδ''0, fun A N hA hAN hNA => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hA.trans hAN
  have hN0 : (0 : ℝ) < N := by linarith
  set G : ℕ → ℕ → ℝ := fun d m => cycProd A ((t : ℤ) ^ m * ((b : ℤ) ^ d - 1))
  have hpair := pair_sum_le (fun n m => cycProd A ((b : ℤ) ^ n - (b : ℤ) ^ m)) G
    (fun d m => cycProd_nonneg _ _) (fun n => by simp [cycProd_le_one])
    (fun n m hmn => le_of_eq (by
      have := cycProd_pair A s t m (n - m)
      rw [show m + (n - m) = n by omega] at this
      simpa [G, hbdef] using this))
    (fun n m hmn => le_of_eq (by
      have := cycProd_pair A s t n (m - n)
      rw [show n + (m - n) = m by omega] at this
      rw [← cycProd_neg, neg_sub]
      simpa [G, hbdef] using this)) N
  rw [copyPairSum_eq_cycProd]
  refine hpair.trans ?_
  -- each shift
  set bad := (Finset.Ico 1 N).filter fun d =>
      ¬ ((Int.gcd ((b : ℤ) ^ d - 1) (3 ^ A - 1) : ℝ) ^ 2 ≤ 3 ^ A - 1)
  have hrow : ∀ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤
      |C| * (N : ℝ) ^ (1 - δ) + (if d ∈ bad then (N : ℝ) else 0) := by
    intro d hd
    by_cases hg : ((Int.gcd ((b : ℤ) ^ d - 1) (3 ^ A - 1) : ℝ) ^ 2 ≤ 3 ^ A - 1)
    · have h1 := hC A N hA hAN hNA ((b : ℤ) ^ d - 1) hg
      have : d ∉ bad := by simp [bad, hg]
      rw [if_neg this, add_zero]
      refine le_trans (le_of_eq ?_) (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C)
        (by positivity)))
      exact Finset.sum_congr rfl fun m _ => by simp only [G]; ring_nf
    · have : d ∈ bad := Finset.mem_filter.2 ⟨hd, hg⟩
      rw [if_pos this]
      have : ∑ m ∈ Finset.range N, G d m ≤ N := by
        refine (Finset.sum_le_sum fun m _ => cycProd_le_one A _).trans ?_
        simp
      have : 0 ≤ |C| * (N : ℝ) ^ (1 - δ) := by positivity
      linarith
  have hsum := Finset.sum_le_sum hrow
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.2 (Finset.filter_subset _ _),
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Nat.card_Ico] at hsum
  have hbad := hC' A N hA hAN hNA
  have hcard : ((N - 1 : ℕ) : ℝ) ≤ N := by
    have : N - 1 ≤ N := Nat.sub_le _ _
    exact_mod_cast this
  -- exponents
  have hp : ∀ e : ℝ, e ≤ 2 - δ'' → (N : ℝ) ^ e ≤ (N : ℝ) ^ (2 - δ'') := fun e he =>
    Real.rpow_le_rpow_of_exponent_le hN1 he
  have e1 : (N : ℝ) * (N : ℝ) ^ (1 - δ) = (N : ℝ) ^ (2 - δ) := by
    rw [show (2 : ℝ) - δ = 1 + (1 - δ) by ring, Real.rpow_add hN0, Real.rpow_one]
  have e2 : (N : ℝ) * (N : ℝ) ^ (1 - δ') = (N : ℝ) ^ (2 - δ') := by
    rw [show (2 : ℝ) - δ' = 1 + (1 - δ') by ring, Real.rpow_add hN0, Real.rpow_one]
  have hN : (N : ℝ) ≤ (N : ℝ) ^ (2 - δ'') := by
    have := hp 1 (by have : δ'' ≤ 1 := min_le_right _ _; linarith)
    rwa [Real.rpow_one] at this
  have h2 := hp (2 - δ) (by have : δ'' ≤ δ := (min_le_left _ _).trans (min_le_left _ _); linarith)
  have h3 := hp (2 - δ') (by have : δ'' ≤ δ' := (min_le_left _ _).trans (min_le_right _ _); linarith)
  have hP : 0 ≤ (N : ℝ) ^ (1 - δ) := by positivity
  have hbad' : (bad.card : ℝ) * N ≤ |C'| * (N : ℝ) ^ (2 - δ') := by
    rw [← e2]
    have := mul_le_mul_of_nonneg_right (hbad.trans (mul_le_mul_of_nonneg_right (le_abs_self C')
      (by positivity))) hN0.le
    nlinarith
  have hrow' : ((N - 1 : ℕ) : ℝ) * (|C| * (N : ℝ) ^ (1 - δ)) ≤ |C| * (N : ℝ) ^ (2 - δ) := by
    rw [← e1]; have := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ |C| * (N : ℝ) ^ (1 - δ))
    nlinarith
  have hCa : 0 ≤ |C| := abs_nonneg _
  have hC'a : 0 ≤ |C'| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h2 hCa, mul_le_mul_of_nonneg_left h3 hC'a]

/-- Pair term with a multiplier `h`.  Proved (as `cycProd_pair`). -/
theorem cycProd_pairH (A s t m d : ℕ) (h : ℤ) :
    cycProd A (h * (((3 ^ s * t : ℕ) : ℤ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℤ) ^ m)) =
      cycProd A ((t : ℤ) ^ m * (h * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1))) := by
  have e : h * (((3 ^ s * t : ℕ) : ℤ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℤ) ^ m) =
      3 ^ (s * m) * ((t : ℤ) ^ m * (h * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1))) := by push_cast; ring
  rw [e, cycProd_mul_three_pow]

theorem int_gcd_mul_le {h q : ℤ} (hh : h ≠ 0) (hq : q ≠ 0) (c : ℤ) :
    (Int.gcd (h * c) q : ℝ) ≤ h.natAbs * Int.gcd c q := by
  have hd : Nat.gcd (h.natAbs * c.natAbs) q.natAbs ∣ h.natAbs * Nat.gcd c.natAbs q.natAbs := by
    rw [← Nat.gcd_mul_left]
    exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ((Nat.gcd_dvd_right _ _).trans (dvd_mul_left _ _))
  have hpos : 0 < h.natAbs * Nat.gcd c.natAbs q.natAbs :=
    Nat.mul_pos (Int.natAbs_pos.2 hh) (Nat.gcd_pos_of_pos_right _ (Int.natAbs_pos.2 hq))
  have := Nat.le_of_dvd hpos hd
  rw [Int.gcd, Int.gcd, Int.natAbs_mul]
  exact_mod_cast this

/-- **Copy-zone decay with a multiplier `h` (open; ⇐ `TOrbitCyclicDecay` + `BadGcdSparseH`).** -/
def CopyZoneDecayH (b : ℕ) (h : ℤ) : Prop :=
  ∃ C δ : ℝ, 0 < δ ∧ ∀ A N : ℕ, 1 ≤ A → A ≤ N → N ≤ A ^ 3 →
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, cycProd A (h * ((b : ℤ) ^ n - (b : ℤ) ^ m)) ≤
      C * (N : ℝ) ^ (2 - δ)

/-- **`BadGcdSparse` with a multiplier slack `H` (open; believed, 75%).** -/
def BadGcdSparseH (b : ℕ) : Prop :=
  ∀ H : ℕ, 1 ≤ H → ∃ C δ : ℝ, 0 < δ ∧ ∀ A N : ℕ, 1 ≤ A → A ≤ N → N ≤ A ^ 3 →
    (((Finset.Ico 1 N).filter fun d =>
      ¬ (((H : ℝ) * Int.gcd ((b : ℤ) ^ d - 1) (3 ^ A - 1)) ^ 2 ≤ 3 ^ A - 1)).card : ℝ) ≤
      C * (N : ℝ) ^ (1 - δ)

theorem copyZoneDecayH_of {s t : ℕ} (hT : TOrbitCyclicDecay t) (hS : BadGcdSparseH (3 ^ s * t))
    (h : ℤ) (hh : h ≠ 0) : CopyZoneDecayH (3 ^ s * t) h := by
  obtain ⟨C, δ, hδ, hC⟩ := hT
  obtain ⟨C', δ', hδ', hC'⟩ := hS h.natAbs (Int.natAbs_pos.2 hh)
  set b := 3 ^ s * t with hbdef
  set δ'' := min (min δ δ') 1
  have hδ''0 : 0 < δ'' := lt_min (lt_min hδ hδ') one_pos
  refine ⟨1 + 2 * |C| + 2 * |C'|, δ'', hδ''0, fun A N hA hAN hNA => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hA.trans hAN
  have hN0 : (0 : ℝ) < N := by linarith
  set G : ℕ → ℕ → ℝ := fun d m => cycProd A ((t : ℤ) ^ m * (h * ((b : ℤ) ^ d - 1)))
  have hpair := pair_sum_le (fun n m => cycProd A (h * ((b : ℤ) ^ n - (b : ℤ) ^ m))) G
    (fun d m => cycProd_nonneg _ _) (fun n => by simp [cycProd_le_one])
    (fun n m hmn => le_of_eq (by
      have := cycProd_pairH A s t m (n - m) h
      rw [show m + (n - m) = n by omega] at this
      simpa [G, hbdef] using this))
    (fun n m hmn => le_of_eq (by
      have := cycProd_pairH A s t n (m - n) h
      rw [show n + (m - n) = m by omega] at this
      rw [← cycProd_neg, ← mul_neg, neg_sub]
      simpa [G, hbdef] using this)) N
  refine hpair.trans ?_
  -- each shift
  set bad := (Finset.Ico 1 N).filter fun d =>
      ¬ (((h.natAbs : ℝ) * Int.gcd ((b : ℤ) ^ d - 1) (3 ^ A - 1)) ^ 2 ≤ 3 ^ A - 1)
  have hrow : ∀ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N, G d m ≤
      |C| * (N : ℝ) ^ (1 - δ) + (if d ∈ bad then (N : ℝ) else 0) := by
    intro d hd
    by_cases hg : (((h.natAbs : ℝ) * Int.gcd ((b : ℤ) ^ d - 1) (3 ^ A - 1)) ^ 2 ≤ 3 ^ A - 1)
    · have h1 := hC A N hA hAN hNA (h * ((b : ℤ) ^ d - 1)) ((pow_le_pow_left₀ (by positivity)
        (int_gcd_mul_le hh (by
          have : (1 : ℤ) < 3 ^ A := one_lt_pow₀ (by norm_num) (by omega)
          omega) _) 2).trans hg)
      have : d ∉ bad := fun hm => (Finset.mem_filter.1 hm).2 hg
      rw [if_neg this, add_zero]
      refine le_trans (le_of_eq ?_) (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C)
        (by positivity)))
      exact Finset.sum_congr rfl fun m _ => by simp only [G]; ring_nf
    · have : d ∈ bad := Finset.mem_filter.2 ⟨hd, hg⟩
      rw [if_pos this]
      have : ∑ m ∈ Finset.range N, G d m ≤ N := by
        refine (Finset.sum_le_sum fun m _ => cycProd_le_one A _).trans ?_
        simp
      have : 0 ≤ |C| * (N : ℝ) ^ (1 - δ) := by positivity
      linarith
  have hsum := Finset.sum_le_sum hrow
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.2 (Finset.filter_subset _ _),
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Nat.card_Ico] at hsum
  have hbad := hC' A N hA hAN hNA
  have hcard : ((N - 1 : ℕ) : ℝ) ≤ N := by
    have : N - 1 ≤ N := Nat.sub_le _ _
    exact_mod_cast this
  -- exponents
  have hp : ∀ e : ℝ, e ≤ 2 - δ'' → (N : ℝ) ^ e ≤ (N : ℝ) ^ (2 - δ'') := fun e he =>
    Real.rpow_le_rpow_of_exponent_le hN1 he
  have e1 : (N : ℝ) * (N : ℝ) ^ (1 - δ) = (N : ℝ) ^ (2 - δ) := by
    rw [show (2 : ℝ) - δ = 1 + (1 - δ) by ring, Real.rpow_add hN0, Real.rpow_one]
  have e2 : (N : ℝ) * (N : ℝ) ^ (1 - δ') = (N : ℝ) ^ (2 - δ') := by
    rw [show (2 : ℝ) - δ' = 1 + (1 - δ') by ring, Real.rpow_add hN0, Real.rpow_one]
  have hN : (N : ℝ) ≤ (N : ℝ) ^ (2 - δ'') := by
    have := hp 1 (by have : δ'' ≤ 1 := min_le_right _ _; linarith)
    rwa [Real.rpow_one] at this
  have h2 := hp (2 - δ) (by have : δ'' ≤ δ := (min_le_left _ _).trans (min_le_left _ _); linarith)
  have h3 := hp (2 - δ') (by have : δ'' ≤ δ' := (min_le_left _ _).trans (min_le_right _ _); linarith)
  have hP : 0 ≤ (N : ℝ) ^ (1 - δ) := by positivity
  have hbad' : (bad.card : ℝ) * N ≤ |C'| * (N : ℝ) ^ (2 - δ') := by
    rw [← e2]
    have := mul_le_mul_of_nonneg_right (hbad.trans (mul_le_mul_of_nonneg_right (le_abs_self C')
      (by positivity))) hN0.le
    nlinarith
  have hrow' : ((N - 1 : ℕ) : ℝ) * (|C| * (N : ℝ) ^ (1 - δ)) ≤ |C| * (N : ℝ) ^ (2 - δ) := by
    rw [← e1]; have := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ |C| * (N : ℝ) ^ (1 - δ))
    nlinarith
  have hCa : 0 ≤ |C| := abs_nonneg _
  have hC'a : 0 ≤ |C'| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h2 hCa, mul_le_mul_of_nonneg_left h3 hC'a]

/-! ### Reduction of the crux to a pair-sum decay -/

/-- The second moment is at most the sum of the pair characteristic values.  Proved (the
expansion of `secondMoment_expand_of_cf`, stopped before the Riesz bound). -/
theorem secondMoment_le_pairs (Φ : (ℕ → Bool) → ℝ) (hG : Measurable Φ) (b : ℕ) (h : ℤ) (N : ℕ) :
    ∫ ω, ‖∑ k ∈ Finset.range N, ee (h * (b : ℝ) ^ k * Φ ω)‖ ^ 2 ∂coinMeasure ≤
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        ‖∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * Φ ω) ∂coinMeasure‖ := by
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
  exact Finset.sum_le_sum fun n _ => norm_sum_le _ _

/-- **Pair-sum decay for the repetition law (open; the crux in pair form).**  For every
`h ≠ 0`, `N⁻²·Σ_{n,m<N} ‖𝔼 e(h(bⁿ − bᵐ)·repReal)‖` is summable along `N = sched j`
(`sched j ≈ e^{√j}`, so a rate `N^{-δ}` or even `exp(−c log N/log log N)` suffices).  Confidence 45% for `b = 3ˢt`,
`t > 1` (the zone split in the docstring of `ae_isNormal_rep_of_three_dvd`; copy-zone terms are
`norm_charFun_repReal_le_cyc_int`, i.e. `CopyZoneDecay`).  Power decay is more than needed
was the first formulation; the summable form admits Stewart-type rates (see `RepPairArith`). -/
def RepPairDecay (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → Summable fun j => (∑ n ∈ Finset.range (sched j), ∑ m ∈ Finset.range (sched j),
      ‖∫ ω, ee ((h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) * repReal ω) ∂coinMeasure‖) /
        ((sched j : ℝ) ^ 2)

/-- The two Riesz bounds on the repetition law: the free coins below `M` (`none`) or the block
coins of run `k` (`some k`, a real-frequency cyclic product). -/
noncomputable def repBound (M : ℕ) : Option ℕ → ℝ → ℝ
  | none, ξ => Bf isFree M ξ
  | some k, ξ => cycProdR (runStart k)
      (ξ * (1 - (3 : ℝ) ^ (-(((k + 1) * runStart k : ℕ) : ℤ))) / 3 ^ runStart k)

theorem norm_charFun_repReal_le_repBound (M : ℕ) (o : Option ℕ) (ξ : ℝ) :
    ‖∫ ω, ee (ξ * repReal ω) ∂coinMeasure‖ ≤ repBound M o ξ := by
  cases o with
  | none => exact charFun_repReal M ξ
  | some k =>
    have h1 := norm_charFun_repReal_le (Finset.Ico (runStart k) (2 * runStart k)) ξ
    rw [prod_block_eq_cyc] at h1
    exact h1

theorem cycProdR_add_int (A : ℕ) (η : ℝ) (j : ℤ) :
    cycProdR A (η + j * (3 ^ A - 1)) = cycProdR A η := by
  unfold cycProdR
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hq : (3 : ℝ) ^ A - 1 = 0
  · simp [hq]
  · have : 2 * Real.pi * ((η + j * (3 ^ A - 1)) * 3 ^ i) / (3 ^ A - 1) =
        2 * Real.pi * (η * 3 ^ i) / (3 ^ A - 1) + ((j * 3 ^ i : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast; field_simp; try ring
    rw [this, Real.cos_add_int_mul_two_pi]

/-- **The copy coins never see past the run end.**  Proved: the run-`k` bound `repBound M (some k)`
at `ξ` and at `ξ + j·3^{(k+2)a}` agree (the period `a` divides the copy length `(k+1)a`).  So in
the shadow zone (window of `ξ` straddling the run end) the copy coins read only `ξ mod 3^{(k+2)a}`,
the low digits; the top digits are visible to the free coins only (the Baker input). -/
theorem repBound_some_add (M k : ℕ) (ξ : ℝ) (j : ℤ) :
    repBound M (some k) (ξ + j * 3 ^ ((k + 2) * runStart k)) = repBound M (some k) ξ := by
  simp only [repBound]
  set a := runStart k
  have h3 : (0 : ℝ) < 3 ^ a := by positivity
  set K : ℤ := ∑ c ∈ Finset.range (k + 1), (3 : ℤ) ^ (a * c) with hKdef
  have hK : (K : ℝ) * (3 ^ a - 1) = 3 ^ ((k + 1) * a) - 1 := by
    have := geom_sum_mul ((3 : ℝ) ^ a) (k + 1)
    rw [hKdef]; push_cast
    simp_rw [pow_mul] at this ⊢
    rw [this, ← pow_mul, ← pow_mul, mul_comm]
  have e : (ξ + j * 3 ^ ((k + 2) * a)) * (1 - (3 : ℝ) ^ (-(((k + 1) * a : ℕ) : ℤ))) / 3 ^ a =
      ξ * (1 - (3 : ℝ) ^ (-(((k + 1) * a : ℕ) : ℤ))) / 3 ^ a + ((j * K : ℤ) : ℝ) * (3 ^ a - 1) := by
    rw [zpow_neg, zpow_natCast]
    push_cast
    rw [mul_assoc (j : ℝ), hK, show (k + 2) * a = a + (k + 1) * a by ring, pow_add]
    have : (0 : ℝ) < 3 ^ ((k + 1) * a) := by positivity
    field_simp
  rw [e, cycProdR_add_int]

/-- **Copy-zone pair term.**  Proved: for `b = 3ˢt`, a pair `(m + d, m)` with `a ≤ sm`
(`a = a_k`) has run-`k` bound at most `cycProd a (h tᵐ(b^d − 1)) + π|ξ|/3^{(k+2)a}`,
`ξ = h(b^{m+d} − bᵐ)`. -/
theorem repBound_pair_le (M k s t m d : ℕ) (h : ℤ) (hsm : runStart k ≤ s * m) :
    repBound M (some k) (h * (((3 ^ s * t : ℕ) : ℝ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℝ) ^ m)) ≤
      cycProd (runStart k) (h * ((t : ℤ) ^ m * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1))) +
        Real.pi * |h * (((3 ^ s * t : ℕ) : ℝ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℝ) ^ m)| /
          3 ^ ((k + 2) * runStart k) := by
  set a := runStart k
  set η₀ : ℤ := 3 ^ (s * m - a) * (h * ((t : ℤ) ^ m * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1)))
  have hξ : h * (((3 ^ s * t : ℕ) : ℝ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℝ) ^ m) =
      (3 : ℝ) ^ a * η₀ := by
    simp only [η₀]; push_cast
    rw [show (3 : ℝ) ^ a = 3 ^ a * 1 by ring]
    have e : (3 : ℝ) ^ (s * m) = 3 ^ a * 3 ^ (s * m - a) := by
      rw [← pow_add]; congr 1; omega
    have e2 : ((3 : ℝ) ^ s * t) ^ (m + d) - ((3 : ℝ) ^ s * t) ^ m =
        3 ^ (s * m) * (t ^ m * ((3 ^ s * t) ^ d - 1)) := by
      rw [pow_mul]; ring
    rw [e2, e]; ring
  have hrot : cycProd a η₀ = cycProd a (h * ((t : ℤ) ^ m * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1))) :=
    cycProd_mul_three_pow _ _ _
  rw [hξ, ← hrot]
  simp only [repBound]
  have h2 := cycProdR_lip a
    ((3 : ℝ) ^ a * η₀ * (1 - (3 : ℝ) ^ (-(((k + 1) * a : ℕ) : ℤ))) / 3 ^ a) η₀
  rw [cycProdR_intCast] at h2
  have h3 : (0 : ℝ) < 3 ^ a := by positivity
  have hz : (3 : ℝ) ^ (-(((k + 1) * a : ℕ) : ℤ)) = 3 ^ a / 3 ^ ((k + 2) * a) := by
    rw [zpow_neg, zpow_natCast, show (k + 2) * a = a + (k + 1) * a by ring, pow_add]
    field_simp
  have e : (3 : ℝ) ^ a * η₀ * (1 - (3 : ℝ) ^ (-(((k + 1) * a : ℕ) : ℤ))) / 3 ^ a - η₀ =
      -(3 ^ a * η₀ / 3 ^ ((k + 2) * a)) := by
    rw [hz]; field_simp; ring
  rw [e, abs_neg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ ((k + 2) * a))] at h2
  have := (abs_le.1 h2).2
  linarith [show Real.pi * (|(3 : ℝ) ^ a * η₀| / 3 ^ ((k + 2) * a)) =
    Real.pi * |(3 : ℝ) ^ a * η₀| / 3 ^ ((k + 2) * a) by ring]

theorem cycProdR_neg (A : ℕ) (η : ℝ) : cycProdR A (-η) = cycProdR A η := by
  unfold cycProdR
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show 2 * Real.pi * (-η * 3 ^ i) / (3 ^ A - 1) = -(2 * Real.pi * (η * 3 ^ i) / (3 ^ A - 1)) by
    ring, Real.cos_neg]

theorem repBound_some_neg (M k : ℕ) (ξ : ℝ) : repBound M (some k) (-ξ) = repBound M (some k) ξ := by
  simp only [repBound]
  rw [show -ξ * (1 - (3 : ℝ) ^ (-(((k + 1) * runStart k : ℕ) : ℤ))) / 3 ^ runStart k =
    -(ξ * (1 - (3 : ℝ) ^ (-(((k + 1) * runStart k : ℕ) : ℤ))) / 3 ^ runStart k) by ring,
    cycProdR_neg]

/-- **Copy-zone pair term, symmetric form.**  Proved: if `a ≤ s·min(n, m)` then the run-`k` bound
at `ξ = h(bⁿ − bᵐ)` (`b = 3ˢt`) is at most `cycProd a (h(bⁿ − bᵐ)) + π|ξ|/3^{(k+2)a}`. -/
theorem repBound_pair_le' (M k s t n m : ℕ) (h : ℤ) (hsm : runStart k ≤ s * min n m) :
    repBound M (some k) (h * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m)) ≤
      cycProd (runStart k) (h * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ m)) +
        Real.pi * |h * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m)| /
          3 ^ ((k + 2) * runStart k) := by
  rcases le_total m n with hmn | hnm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [min_eq_right (by omega)] at hsm
    rw [cycProd_pairH]
    have := repBound_pair_le M k s t m d h hsm
    rwa [show h * ((t : ℤ) ^ m * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1)) =
      (t : ℤ) ^ m * (h * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1)) by ring] at this
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [min_eq_left (by omega)] at hsm
    have e1 : h * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ (n + d)) =
        -(h * (((3 ^ s * t : ℕ) : ℝ) ^ (n + d) - ((3 ^ s * t : ℕ) : ℝ) ^ n)) := by ring
    have e2 : h * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ (n + d)) =
        -(h * (((3 ^ s * t : ℕ) : ℤ) ^ (n + d) - ((3 ^ s * t : ℕ) : ℤ) ^ n)) := by ring
    rw [e1, e2, repBound_some_neg, cycProd_neg, abs_neg, cycProd_pairH]
    have := repBound_pair_le M k s t n d h hsm
    rwa [show h * ((t : ℤ) ^ n * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1)) =
      (t : ℤ) ^ n * (h * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1)) by ring] at this

/-- **Run-`k` copy-zone sum.**  Proved: over any set `P` of pairs below `N'` with
`a ≤ s·min(n,m)` and `|ξ| ≤ B`, the run-`k` bounds sum to at most the cyclic pair sum below
`N'` (the `CopyZoneDecayH` quantity) plus `|P|·πB/3^{(k+2)a}`. -/
theorem copyRun_sum_le (M k s t : ℕ) (h : ℤ) (P : Finset (ℕ × ℕ)) (N' : ℕ) (B : ℝ)
    (hP : ∀ p ∈ P, p.1 < N' ∧ p.2 < N' ∧ runStart k ≤ s * min p.1 p.2 ∧
      |h * (((3 ^ s * t : ℕ) : ℝ) ^ p.1 - ((3 ^ s * t : ℕ) : ℝ) ^ p.2)| ≤ B) :
    ∑ p ∈ P, repBound M (some k) (h * (((3 ^ s * t : ℕ) : ℝ) ^ p.1 - ((3 ^ s * t : ℕ) : ℝ) ^ p.2)) ≤
      ∑ n ∈ Finset.range N', ∑ m ∈ Finset.range N',
        cycProd (runStart k) (h * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ m)) +
      P.card * (Real.pi * B / 3 ^ ((k + 2) * runStart k)) := by
  have hE : (0 : ℝ) < 3 ^ ((k + 2) * runStart k) := by positivity
  have h1 : ∀ p ∈ P, repBound M (some k)
      (h * (((3 ^ s * t : ℕ) : ℝ) ^ p.1 - ((3 ^ s * t : ℕ) : ℝ) ^ p.2)) ≤
      cycProd (runStart k) (h * (((3 ^ s * t : ℕ) : ℤ) ^ p.1 - ((3 ^ s * t : ℕ) : ℤ) ^ p.2)) +
        Real.pi * B / 3 ^ ((k + 2) * runStart k) := by
    intro p hp
    obtain ⟨-, -, hs, hB⟩ := hP p hp
    refine (repBound_pair_le' M k s t p.1 p.2 h hs).trans ?_
    gcongr
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  gcongr
  rw [← Finset.sum_product']
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun _ _ _ => cycProd_nonneg _ _)
  obtain ⟨h1, h2, -, -⟩ := hP p hp
  exact Finset.mem_product.2 ⟨Finset.mem_range.2 h1, Finset.mem_range.2 h2⟩

/-- **The crux as a deterministic exponential-sum statement (open).**  For each `h ≠ 0` there
is a choice, per `N = sched j` and pair `(n, m)`, of free coins or of one run's block coins whose
Riesz bounds at `ξ = h(bⁿ − bᵐ)` sum to `N²·ε_j` with `Σ ε_j < ∞`.

Route note (2026-10-07).  Windows `[P, cP]` (`c = 1 + log₃t/s`) of the frequencies lie inside
runs (runs have multiplicative length `k+2 → ∞`), so free coins cannot carry the bound; the
copy coins must.  No-wrap copy pairs (`h tᵐ(b^d − 1) < 3^A`) need only `≳ log A/log log A`
ternary digit changes of the integer `h tᵐ(b^d−1)`: a Stewart-type digit theorem (Baker;
Stewart 1980 covers fixed multipliers, uniformity in `b^d − 1` is not known to us), which would give
the rate `exp(−c log N/log log N)`, summable along `sched`; hence the summable form.  The
wrap pairs are modular (`tᵐ mod 3^A − 1`, orbit length polylog in the modulus, below
Bourgain–Glibichuk–Konyagin range).  No measure theory left: the crux
`repPairDecay_of_three_dvd` follows (`repPairDecay_of_arith`).  Choices expected: `some k` when
the window of `h bⁿ` sits in run `k`'s copy stretch (`CopyZoneDecay`), `none` otherwise (free
gaps: Cassels; shadow: Baker).  Evidence (`scripts/rep_arith.py`, `h = 1`, greedy `κ` = min
over all options, `N⁻²·Σ` at `N = 30, 60, 120, 200`; `N = 200` reaches run 2's copy stretch):
`b = 6`: `.043/.019/.009/.0052`, `b = 12`: `.037/.018/.009/.0051`, i.e. the diagonal floor `1/N`;
control `b = 9`: `.30/.30/.28/.25`, no decay. -/
def RepPairArith (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∃ (M : ℕ → ℕ) (κ : ℕ → ℕ → ℕ → Option ℕ), Summable fun j =>
    (∑ n ∈ Finset.range (sched j), ∑ m ∈ Finset.range (sched j),
      repBound (M j) (κ j n m) (h * ((b : ℝ) ^ n - (b : ℝ) ^ m))) / ((sched j : ℝ) ^ 2)

/-- Proved: pointwise `norm_charFun_repReal_le_repBound`. -/
theorem repPairDecay_of_arith {b : ℕ} (hA : RepPairArith b) : RepPairDecay b := by
  intro h hh
  obtain ⟨M, κ, hκ⟩ := hA h hh
  refine hκ.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ =>
    norm_charFun_repReal_le_repBound (M j) (κ j n m) _) (by positivity)

/-- **Normality from pair-sum decay.**  Proved: `secondMoment_le_pairs` +
`summable_sched_rpow` + `ae_isNormal_of_secondMoment`. -/
theorem ae_isNormal_rep_of_pairDecay {b : ℕ} (hb : 2 ≤ b) (hP : RepPairDecay b) :
    ∀ᵐ ω ∂coinMeasure, IsNormal b (repReal ω) := by
  refine ae_isNormal_of_secondMoment coinMeasure hb _ measurable_repReal sched
    sched_strictMono sched_ratio ?_
  intro h hh
  refine (hP h hh).of_nonneg_of_le
    (fun j => div_nonneg (integral_nonneg fun ω => by positivity) (by positivity))
    (fun j => div_le_div_of_nonneg_right
      (secondMoment_le_pairs repReal measurable_repReal b h (sched j)) (by positivity))

/-! ### Alternative construction: short periods (route note, statements only) -/

/-- **Exponential order modulo `3^ℓ − 1` along infinitely many periods (open conjecture).**
For `b` not a power of 3 (unit part `t`): for infinitely many `ℓ`, the order of `t` modulo the
`t`-free part of `3^ℓ − 1` exceeds `3^{θℓ}` with `θ > log₃(3/2) ≈ .369`.

Why it matters (2026-10-07).  The frozen headline is `∃ x`, so the construction is ours.  Take
runs `[u, (k+2)u)` periodic with a SHORT period `ℓ ≈ κ log₃ u` (Liouville still holds: the
approximant has `log q ≈ u + ℓ`).  Then the copy-zone frequencies `bᵐ` run over many full orbits
modulo `q = 3^ℓ − 1`, and Parseval over the block law `ν` (mass `2^{-ℓ}` on `2^ℓ` residues)
gives `𝔼_W |Σ_{m<M} e(h bᵐ W/q)|² ≤ (3/2)^ℓ Σ_y f(y)²`, `f(y) = #{m < M : h bᵐ ≡ y}`, i.e.
normalized second moment `≤ (3/2)^ℓ (1/M + 1/ord_q(b))`.  So the wrapped cyclic-digit wall
(`TOrbitCyclicDecay`) is replaced by this order statement (the signed second moment is needed:
`RepPairDecay`, which takes norms per pair, loses the Parseval structure).
Evidence (`scripts/rep_order.py`, `t = 2`, `ℓ ≤ 60`): `log₃ ord/ℓ` is `.56–.90` at every prime
`ℓ ≥ 5` (e.g. `ℓ = 59`: `.854`), dips to `.21–.35` at highly composite `ℓ` (`ℓ = 48`: `.206`).
Corvaja–Zannier (`CZGcdPow`) gives only `ord ≥ ℓ/ε` (superlinear), not exponential.  Confidence
85% that it is true, but its proof looks out of reach (an Artin-type statement for the moduli
`3^p − 1`).  The shadow zone (Baker) would remain. -/
def ExpOrderPeriods (t : ℕ) : Prop :=
  ∃ θ : ℝ, Real.logb 3 (3 / 2) < θ ∧ ∀ L : ℕ, ∃ ℓ ≥ L, ∃ e : ℕ, 0 < e ∧
    (3 : ℝ) ^ (θ * ℓ) ≤ e ∧ ∀ e' : ℕ, 0 < e' → e' < e →
      ¬ ((3 ^ ℓ - 1) / Nat.gcd (3 ^ ℓ - 1) (t ^ ℓ)) ∣ (t ^ e' - 1)

/-! ## Bases `3ˢt`, `t > 1`: the crux -/

/-- **Assembly of the crux from its inputs (open; believed, 60%).**  For `b = 3ˢt`, `t > 1`:
`RepPairArith b` follows from the Baker discrepancy of `m log₃ t` (cited,
`Literature.BakerLogDiscrepancy`), the copy-zone digit statements `TOrbitCyclicDecay t` and
`BadGcdSparseH b`.  Plan (per pair `(n, m)`, `v = s·min(n,m)`, window `[v, log₃|ξ|]`):
* window meets a free gap in `≥ K` places at its bottom: `κ = none`, low-digit Cassels count
  (`cassels_Bf`-type, elementary);
* window top `≥ K` places into the gap after run `k`: `κ = none`, top window
  (`CantorExactExponentProfile.bf_le_topProd`, `sum_topProd_le` from Baker);
* otherwise the window lies in run `k` up to `K` places: `κ = some k`; by `repBound_some_add`
  only `ξ mod 3^{(k+2)a}` matters and `norm_charFun_repReal_le_cyc_int` reduces to
  `cycProd a (tᵐ(b^d − 1))` (`cycProd_pair`), summed by `copyZoneDecayH_of` (hence `BadGcdSparseH`).
* top of `ξ` within `K` places above a run end (band): bound the term by `1`; these pairs have
  `max(n,m)` in a band of width `K/log₃ b`, so contribute `O(N K)`, negligible for `K ≍ log N`.
  (Needed: in the band, `repBound_some_add` reduces to `X mod 3^{E−v}`, not to `cycProd` of
  `tᵐ(b^d−1)`, and the free coins below the top are run positions.)
The copy-zone ranges match: in run `k`, `N ≈ (k+2)a/s ≤ a³` since `a_k` grows like `2^k k!`.

**Gap in the plan for large `t` (2026-10-07).**  The window has multiplicative length
`c = log₃ b / s`, while the gap after run `k` is `[E_k, a_{k+1}) = [(k+2)a, 2(k+2)a)`, ratio 2.
For `c < 2` (e.g. `b = 6`: `c = 1.63`) a window starting in run `k` has its top in that gap or
in run `k`, and the four classes above cover it.  For `c ≥ 2` (`t ≥ 3^s`, e.g. `b = 12, 15, 24`)
a window starting at `v ∈ [E_k/c·2, E_k − a]` covers the whole gap and tops out in run `k+1`:
* run `k`'s copy coins read only `X mod 3^{E_k − v}` folded mod `3^a − 1` (`repBound_some_add`),
  not `cycProd` of `X`;
* the gap coins read middle digits of `X` (neither low nor top: no Cassels, no Baker);
* run `k+1`'s copy coins read the top `T − a_{k+1}` digits of `ξ` unfolded when `c < 4`
  (top-window, Baker-type, unproved shape).
A positive fraction of `m` falls here, so the assembly as stated needs either the third bullet
formalized or a construction with `a_{k+1}/E_k → ∞` (gaps eventually longer than every window;
Liouville unaffected; e.g. use only the runs `k` in a sparse set and free the others).  The 60%
confidence is for the redesigned or extended version.  Numerically the class is harmless
(`scripts/rep_arith.py 12 300,380`: `N⁻²Σ = .0034, .0027`, the `1/N` floor, and `N = 380` reaches
the gap-spanning windows `n ≥ 340` of run 2; `b = 6`, `N = 300`: `.0034`): a proof-plan gap,
not evidence against `RepPairArith`. -/
theorem repPairArith_of_inputs {s t : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (h3t : ¬ 3 ∣ t)
    (hB : CantorExactExponentProfile.Literature.BakerLogDiscrepancy) (hT : TOrbitCyclicDecay t)
    (hS : BadGcdSparseH (3 ^ s * t)) : RepPairArith (3 ^ s * t) := by
  sorry

/-- **The crux, arithmetic form (open leaf).**  See `RepPairArith`. -/
theorem repPairArith_of_three_dvd {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) (hpow : ∀ s : ℕ, b ≠ 3 ^ s) :
    RepPairArith b := by
  sorry

/-- **Pair-sum decay at `b = 3ˢt`, `t > 1` (open leaf; the crux in pair form).**  See
`RepPairDecay` and the zone route in the docstring of `ae_isNormal_rep_of_three_dvd`. -/
theorem repPairDecay_of_three_dvd {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b) (hpow : ∀ s : ℕ, b ≠ 3 ^ s) :
    RepPairDecay b :=
  repPairDecay_of_arith (repPairArith_of_three_dvd hb h3 hpow)

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
    ∀ᵐ ω ∂coinMeasure, IsNormal b (repReal ω) :=
  ae_isNormal_rep_of_pairDecay hb (repPairDecay_of_three_dvd hb h3 hpow)

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

