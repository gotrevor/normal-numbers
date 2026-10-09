/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import NormalNumbers.CantorExactExponentProfile
import NormalNumbers.EntropyProfiles
import NormalNumbers.ExplicitPQ
import NormalNumbers.LevinSparse
import NormalNumbers.SparseIdentity
import NormalNumbers.CycMerge
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Analysis.SpecificLimits.Normed

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
`a_k = runStart k`).  On an even run `k` the digits are no longer zero: the block `[a_k, 2a_k)`
carries fresh coins, and the rest of the run repeats that block `k` more times (period `a_k`).
Odd runs carry fresh coins throughout (2026-10-07 redesign: gaps between copy runs then grow
relative to the runs).  So
`x ≈ p/q` with `q = 3^{a_k}(3^{a_k} − 1)`, error `≤ 3^{-(k+2)a_k}`: exponent `≥ (k+2)/2`. -/

open CantorLiouville CantorLiouvilleAll DecayAeNormal ExplicitSquare CantorSelfSimilar

/-- The run containing a forced position (the largest `k ≤ i` with `a_k ≤ i`). -/
noncomputable def runIdx (i : ℕ) : ℕ := Nat.findGreatest (fun k => runStart k ≤ i) i

/-- The coin read at position `i`: itself if free or in an odd run, else (even run `k`) the
block position `a_k + (i − a_k) mod a_k`.  Only even runs copy, so the gap between copy runs
`k` and `k + 2` has ratio `a_{k+2}/E_k = 4(k+3) → ∞` (every frequency window of a fixed base
eventually fits: see `repPairArith_of_inputs`). -/
noncomputable def src (i : ℕ) : ℕ :=
  if isFree i then i else if Even (runIdx i) then
    runStart (runIdx i) + (i - runStart (runIdx i)) % runStart (runIdx i) else i

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

theorem src_of_mem_run {k i : ℕ} (hk : Even k) (h1 : runStart k ≤ i)
    (h2 : i < (k + 2) * runStart k) :
    src i = runStart k + (i - runStart k) % runStart k := by
  have hf : isFree i = false := by simp [isFree, isForced_of_mem_run h1 h2]
  simp [src, hf, runIdx_eq h1 h2, hk]

theorem src_of_mem_odd_run {k i : ℕ} (hk : ¬ Even k) (h1 : runStart k ≤ i)
    (h2 : i < (k + 2) * runStart k) : src i = i := by
  have hf : isFree i = false := by simp [isFree, isForced_of_mem_run h1 h2]
  simp [src, hf, runIdx_eq h1 h2, hk]

theorem src_of_free {i : ℕ} (h : isFree i = true) : src i = i := by simp [src, h]

/-- Forced positions read forced positions (the block lies inside its run). -/
theorem isFree_src_of_not_free {i : ℕ} (h : isFree i = false) : isFree (src i) = false := by
  obtain ⟨k, h1, h2⟩ := exists_run_of_not_free h
  by_cases hk : Even k
  swap; · rw [src_of_mem_odd_run hk h1 h2]; exact h
  rw [src_of_mem_run hk h1 h2]
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

/-! ### Fresh coins: free places and odd runs -/

/-- **Fresh places**: free places and the places of odd runs.  Each reads its own coin and no
other place reads it. -/
noncomputable def isFresh (i : ℕ) : Bool := isFree i || !decide (Even (runIdx i))

theorem src_of_fresh {i : ℕ} (h : isFresh i = true) : src i = i := by
  unfold isFresh at h
  cases hf : isFree i
  · rw [hf] at h
    simp only [Bool.false_or, Bool.not_eq_true', decide_eq_false_iff_not] at h
    simp [src, hf, h]
  · exact src_of_free hf

theorem isFresh_eq_false {i : ℕ} : isFresh i = false ↔
    ∃ k, Even k ∧ runStart k ≤ i ∧ i < (k + 2) * runStart k := by
  constructor
  · intro h
    unfold isFresh at h
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at h
    obtain ⟨k, h1, h2⟩ := exists_run_of_not_free h.1
    exact ⟨k, runIdx_eq h1 h2 ▸ h.2, h1, h2⟩
  · rintro ⟨k, hk, h1, h2⟩
    have hf : isFree i = false := by simp [isFree, isForced_of_mem_run h1 h2]
    simp [isFresh, hf, runIdx_eq h1 h2, hk]

/-- Non-fresh places read non-fresh coins (the block of their own even run). -/
theorem isFresh_src_of_not_fresh {i : ℕ} (h : isFresh i = false) : isFresh (src i) = false := by
  obtain ⟨k, hk, h1, h2⟩ := isFresh_eq_false.1 h
  rw [src_of_mem_run hk h1 h2]
  have hpos : 0 < runStart k := (Nat.zero_le k).trans_lt (lt_runStart k)
  have := Nat.mod_lt (i - runStart k) hpos
  exact isFresh_eq_false.2 ⟨k, hk, by omega, by nlinarith⟩

/-- The even-run copy part. -/
noncomputable def repCopyE (ω : ℕ → Bool) : ℝ := pt (fun i => !isFresh i) (fun i => ω (src i))

theorem measurable_repCopyE : Measurable repCopyE :=
  (measurable_pt _).comp measurable_reindex

/-- **Fresh part plus even-run copy part.** -/
theorem repReal_eq_fresh (ω : ℕ → Bool) : repReal ω = pt isFresh ω + repCopyE ω := by
  unfold repReal repCopyE
  rw [pt_true_eq_add isFresh]
  congr 1
  unfold pt; congr 1; funext i
  simp only [ptDigit]
  cases h : isFresh i
  · simp
  · simp [src_of_fresh h]

theorem repCopyE_congr {ω ω' : ℕ → Bool} (h : ∀ i, isFresh i = false → ω i = ω' i) :
    repCopyE ω = repCopyE ω' := by
  unfold repCopyE pt; congr 1; funext i
  simp only [ptDigit]
  by_cases hf : isFresh i = true
  · simp [hf]
  · simp only [Bool.not_eq_true] at hf
    simp [hf, h _ (isFresh_src_of_not_fresh hf)]

/-- **Riesz bound over the fresh coins.**  Proved (`charFun_add` with the even-run copy part as
the shift). -/
theorem charFun_repReal_fresh (M : ℕ) (ξ : ℝ) :
    ‖∫ ω, ee (ξ * repReal ω) ∂coinMeasure‖ ≤ Bf isFresh M ξ := by
  simp_rw [repReal_eq_fresh]
  exact charFun_add M isFresh ξ repCopyE measurable_repCopyE fun ω ω' h => repCopyE_congr h

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
    rw [src_of_mem_run (k := 2 * n) (even_two_mul n) (by omega) (by nlinarith), Nat.add_sub_cancel_left,
      Nat.mod_eq_of_lt hr]
  have hagree : ∀ i < T, ω'' i = ω' i := by
    intro i hi
    simp only [hω'']
    split_ifs with h
    · rfl
    · simp only [hω']
      rw [hblk _ (Nat.mod_lt _ (by omega)), src_of_mem_run (k := 2 * n) (even_two_mul n) (by omega) (by omega)]
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
theorem src_eq_iff_block {k j i : ℕ} (hk : Even k) (h1 : runStart k ≤ j) (h2 : j < 2 * runStart k) :
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
      by_cases hk' : Even k'
      swap
      · rw [src_of_mem_odd_run hk' h1' h2'] at h
        subst h
        have := (runIdx_eq h1' h2').symm.trans (runIdx_eq h1 hj2)
        exact absurd (this ▸ hk) hk'
      rw [src_of_mem_run hk' h1' h2'] at h
      have hm := Nat.mod_lt (i - runStart k') hpos'
      have hkk : k' = k := by
        have e1 := runIdx_eq (k := k') (i := j) (by omega) (by nlinarith)
        rw [runIdx_eq h1 hj2] at e1; exact e1.symm
      subst hkk
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
    rw [src_of_mem_run hk (by omega) hi2]
    have : j + c * runStart k - runStart k = (j - runStart k) + c * runStart k := by omega
    rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- **Weight of a block coin.**  Proved: `srcWeight j = Σ_{c≤k} 2·3^{-(j+c a_k)-1}`. -/
theorem srcWeight_block {k j : ℕ} (hk : Even k) (h1 : runStart k ≤ j) (h2 : j < 2 * runStart k) :
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
      obtain ⟨c, hc, e⟩ := (src_eq_iff_block hk h1 h2).1 h; exact ⟨c, hc, e.symm⟩))]
  rw [Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [if_pos ((src_eq_iff_block hk h1 h2).2 ⟨c, hc, rfl⟩)]

/-- **Block-coin product is a cyclic Riesz product.**  Proved: over the block of run `k`
(`a = a_k`), `∏_j |cos(π ξ srcWeight j)| = ∏_{i<a} |cos(2π η 3ⁱ/(3^a − 1))|` with the real
frequency `η = ξ(1 − 3^{-(k+1)a})/3^a` (coin `a + r` is cyclic place `a − 1 − r`). -/
theorem prod_block_eq_cyc {k : ℕ} (hk : Even k) (ξ : ℝ) :
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
  rw [srcWeight_block (k := k) hk (j := a + (a - 1 - r)) (by omega) (by omega)]
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
theorem norm_charFun_repReal_le_cyc {k : ℕ} (hk : Even k) (ξ : ℝ) (η₀ : ℤ) :
    ‖∫ ω, ee (ξ * repReal ω) ∂coinMeasure‖ ≤ cycProd (runStart k) η₀ + Real.pi *
      |ξ * (1 - (3 : ℝ) ^ (-(((k + 1) * runStart k : ℕ) : ℤ))) / 3 ^ runStart k - η₀| := by
  have h1 := norm_charFun_repReal_le (Finset.Ico (runStart k) (2 * runStart k)) ξ
  rw [prod_block_eq_cyc hk] at h1
  have h2 := cycProdR_lip (runStart k)
    (ξ * (1 - (3 : ℝ) ^ (-(((k + 1) * runStart k : ℕ) : ℤ))) / 3 ^ runStart k) η₀
  rw [cycProdR_intCast] at h2
  have := (abs_le.1 h2).2
  exact h1.trans (by unfold cycProdR at this; linarith)

/-- **Copy-zone bound at an integer frequency divisible by `3^a`.**  Proved: if `z = 3^a η₀`,
then `‖𝔼 e(z·repReal)‖ ≤ cycProd a η₀ + π |z| 3^{-(k+2)a}`.  For `z = h(bⁿ − bᵐ)` with
`b = 3ˢt` and `sm ≥ a` this is the copy-zone pair term, error negligible while
`|z| ≪ 3^{(k+2)a}` (the frequency's window stays inside run `k`). -/
theorem norm_charFun_repReal_le_cyc_int {k : ℕ} (hk : Even k) (η₀ : ℤ) :
    ‖∫ ω, ee (((3 : ℝ) ^ runStart k * η₀) * repReal ω) ∂coinMeasure‖ ≤
      cycProd (runStart k) η₀ +
        Real.pi * |(3 : ℝ) ^ runStart k * η₀| / 3 ^ ((k + 2) * runStart k) := by
  refine (norm_charFun_repReal_le_cyc hk _ η₀).trans (le_of_eq ?_)
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
coins of run `k` (`some k`, a real-frequency cyclic product).  `none` uses the fresh coins (free
places and odd runs). -/
noncomputable def repBound (M : ℕ) : Option ℕ → ℝ → ℝ
  | none, ξ => Bf isFresh M ξ
  | some k, ξ => if Even k then cycProdR (runStart k)
      (ξ * (1 - (3 : ℝ) ^ (-(((k + 1) * runStart k : ℕ) : ℤ))) / 3 ^ runStart k) else 1

theorem norm_charFun_repReal_le_repBound (M : ℕ) (o : Option ℕ) (ξ : ℝ) :
    ‖∫ ω, ee (ξ * repReal ω) ∂coinMeasure‖ ≤ repBound M o ξ := by
  cases o with
  | none => exact charFun_repReal_fresh M ξ
  | some k =>
    simp only [repBound]
    split_ifs with hk
    · have h1 := norm_charFun_repReal_le (Finset.Ico (runStart k) (2 * runStart k)) ξ
      rw [prod_block_eq_cyc hk] at h1
      exact h1
    · exact (charFun_repReal 0 ξ).trans (Finset.prod_le_one (fun _ _ => abs_nonneg _)
        fun _ _ => Real.abs_cos_le_one _)

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
theorem repBound_pair_le (M k s t m d : ℕ) (hk : Even k) (h : ℤ) (hsm : runStart k ≤ s * m) :
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
  simp only [repBound, if_pos hk]
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
theorem repBound_pair_le' (M k s t n m : ℕ) (hk : Even k) (h : ℤ) (hsm : runStart k ≤ s * min n m) :
    repBound M (some k) (h * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m)) ≤
      cycProd (runStart k) (h * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ m)) +
        Real.pi * |h * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m)| /
          3 ^ ((k + 2) * runStart k) := by
  rcases le_total m n with hmn | hnm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [min_eq_right (by omega)] at hsm
    rw [cycProd_pairH]
    have := repBound_pair_le M k s t m d hk h hsm
    rwa [show h * ((t : ℤ) ^ m * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1)) =
      (t : ℤ) ^ m * (h * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1)) by ring] at this
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [min_eq_left (by omega)] at hsm
    have e1 : h * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ (n + d)) =
        -(h * (((3 ^ s * t : ℕ) : ℝ) ^ (n + d) - ((3 ^ s * t : ℕ) : ℝ) ^ n)) := by ring
    have e2 : h * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ (n + d)) =
        -(h * (((3 ^ s * t : ℕ) : ℤ) ^ (n + d) - ((3 ^ s * t : ℕ) : ℤ) ^ n)) := by ring
    rw [e1, e2, repBound_some_neg, cycProd_neg, abs_neg, cycProd_pairH]
    have := repBound_pair_le M k s t n d hk h hsm
    rwa [show h * ((t : ℤ) ^ n * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1)) =
      (t : ℤ) ^ n * (h * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1)) by ring] at this

/-- **Run-`k` copy-zone sum.**  Proved: over any set `P` of pairs below `N'` with
`a ≤ s·min(n,m)` and `|ξ| ≤ B`, the run-`k` bounds sum to at most the cyclic pair sum below
`N'` (the `CopyZoneDecayH` quantity) plus `|P|·πB/3^{(k+2)a}`. -/
theorem copyRun_sum_le (M k s t : ℕ) (hk : Even k) (h : ℤ) (P : Finset (ℕ × ℕ)) (N' : ℕ) (B : ℝ)
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
    refine (repBound_pair_le' M k s t p.1 p.2 hk h hs).trans ?_
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

/-! ### Cyclic digits via `⌊3·{u}⌋` (for `card_cycProd_ge_le`) -/

/-- Leading ternary digit of the fractional part. -/
noncomputable def rd (u : ℝ) : ℤ := ⌊3 * Int.fract u⌋

theorem rd_nonneg (u : ℝ) : 0 ≤ rd u :=
  Int.floor_nonneg.2 (by have := Int.fract_nonneg u; linarith)

theorem rd_lt (u : ℝ) : rd u < 3 := by
  unfold rd; rw [Int.floor_lt]; push_cast; have := Int.fract_lt_one u; linarith

theorem fract_three_mul (u : ℝ) : Int.fract (3 * u) = 3 * Int.fract u - rd u := by
  unfold rd
  have h1 : 3 * u = 3 * Int.fract u + ((3 * ⌊u⌋ : ℤ) : ℝ) := by
    push_cast; rw [Int.fract]; ring
  rw [h1, Int.fract_add_intCast, Int.fract]

/-- **A cyclic digit change forces a small factor.** -/
theorem abs_cos_le_of_rd_ne {u : ℝ} (h : rd u ≠ rd (3 * u)) :
    |Real.cos (2 * Real.pi * u)| ≤ Real.cos (Real.pi / 9) := by
  have hw : 2 * Real.pi * u = 2 * Real.pi * Int.fract u + (⌊u⌋ : ℤ) * (2 * Real.pi) := by
    rw [Int.fract]; ring
  rw [hw, Real.cos_add_int_mul_two_pi]
  have hw' := fract_three_mul u
  have ha1 : ((rd u : ℤ) : ℝ) ≤ 3 * Int.fract u := Int.floor_le _
  have ha2 : 3 * Int.fract u < (rd u : ℝ) + 1 := Int.lt_floor_add_one _
  have hb1 : ((rd (3 * u) : ℤ) : ℝ) ≤ 3 * Int.fract (3 * u) := Int.floor_le _
  have hb2 : 3 * Int.fract (3 * u) < (rd (3 * u) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [hw'] at hb1 hb2
  apply abs_cos_le_of_mem
  have key : ∀ (w : ℝ) (a b : ℤ), a ≠ b → (a : ℝ) ≤ 3 * w → 3 * w < a + 1 →
      (b : ℝ) ≤ 3 * (3 * w - a) → 3 * (3 * w - a) < b + 1 → 0 ≤ a → a < 3 → 0 ≤ b → b < 3 →
      (1 / 9 ≤ w ∧ w ≤ 4 / 9) ∨ (5 / 9 ≤ w ∧ w ≤ 8 / 9) := by
    intro w a b hab ha1 ha2 hb1 hb2 a0 a3 b0 b3
    have hA : a = 0 ∨ a = 1 ∨ a = 2 := by omega
    have hB : b = 0 ∨ b = 1 ∨ b = 2 := by omega
    rcases hA with rfl | rfl | rfl <;> rcases hB with rfl | rfl | rfl <;>
      simp at hab <;> push_cast at ha1 ha2 hb1 hb2 <;>
      first | (left; constructor <;> linarith) | (right; constructor <;> linarith)
  exact key _ _ _ h ha1 ha2 hb1 hb2 (rd_nonneg u) (rd_lt u) (rd_nonneg _) (rd_lt _)

/-- Digit expansion: `{u}·3ⁿ = Σ_{i<n} rd(3ⁱu) 3^{n−1−i} + {3ⁿu}`. -/
theorem fract_mul_pow_eq (u : ℝ) (n : ℕ) :
    Int.fract u * 3 ^ n = ∑ i ∈ Finset.range n, (rd (3 ^ i * u) : ℝ) * 3 ^ (n - 1 - i) +
      Int.fract (3 ^ n * u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, show (3 : ℝ) ^ (n + 1) * u = 3 * (3 ^ n * u) by ring,
      fract_three_mul, pow_succ, ← mul_assoc, ih]
    have : ∀ i ∈ Finset.range n, (rd (3 ^ i * u) : ℝ) * 3 ^ (n + 1 - 1 - i) =
        (rd (3 ^ i * u) : ℝ) * 3 ^ (n - 1 - i) * 3 := by
      intro i hi
      have hi := Finset.mem_range.1 hi
      rw [mul_assoc, ← pow_succ]; congr 2; omega
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul]
    simp
    ring

/-- **Reconstruction.**  For `y < 3^P − 1`, `y = Σ_{i<P} rd(3ⁱy/(3^P−1)) 3^{P−1−i}`. -/
theorem eq_sum_rd {P y : ℕ} (hP : 1 ≤ P) (hy : y < 3 ^ P - 1) :
    (y : ℝ) = ∑ i ∈ Finset.range P, (rd (3 ^ i * ((y : ℝ) / (3 ^ P - 1))) : ℝ) * 3 ^ (P - 1 - i) := by
  have hq1 : (1 : ℝ) < 3 ^ P := one_lt_pow₀ (by norm_num) (by omega)
  have hq : (0 : ℝ) < 3 ^ P - 1 := by linarith
  have hyq : (y : ℝ) < 3 ^ P - 1 := by
    have : ((y : ℕ) : ℝ) < ((3 ^ P - 1 : ℕ) : ℝ) := by exact_mod_cast hy
    rwa [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at this
  set u := (y : ℝ) / (3 ^ P - 1)
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u < 1 := (div_lt_one hq).2 hyq
  have hfu : Int.fract u = u := Int.fract_eq_self.2 ⟨hu0, hu1⟩
  have hfP : Int.fract (3 ^ P * u) = u := by
    have : 3 ^ P * u = u + ((y : ℤ) : ℝ) := by
      simp only [u]; field_simp; push_cast; ring
    rw [this, Int.fract_add_intCast, hfu]
  have := fract_mul_pow_eq u P
  rw [hfu, hfP] at this
  have e : (y : ℝ) = u * 3 ^ P - u := by simp only [u]; field_simp
  linarith


/-- Cyclic digit `i` of `y` modulo `3^P − 1`. -/
noncomputable def dg (P y i : ℕ) : ℤ := rd (3 ^ i * ((y : ℝ) / (3 ^ P - 1)))

/-- Change-point code: positions `i < P` where the digit changes from `i − 1` (and `0`), with the
new digit. -/
noncomputable def chCode (P y : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range P).filter (fun i => i = 0 ∨ dg P y (i - 1) ≠ dg P y i)).image
    (fun i => (i, (dg P y i).toNat))

theorem mem_chCode {P y n v : ℕ} : (n, v) ∈ chCode P y ↔
    n < P ∧ (n = 0 ∨ dg P y (n - 1) ≠ dg P y n) ∧ v = (dg P y n).toNat := by
  unfold chCode
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, rfl, rfl⟩; exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, rfl⟩; exact ⟨n, ⟨h1, h2⟩, rfl, rfl⟩

theorem dg_eq_of_toNat {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a.toNat = b.toNat) : a = b := by
  omega

theorem dg_eq_of_chCode {P y y' : ℕ} (h : chCode P y = chCode P y') :
    ∀ n < P, dg P y n = dg P y' n := by
  intro n
  induction n with
  | zero =>
    intro hP
    have : (0, (dg P y 0).toNat) ∈ chCode P y' := h ▸ mem_chCode.2 ⟨hP, Or.inl rfl, rfl⟩
    exact dg_eq_of_toNat (rd_nonneg _) (rd_nonneg _) (mem_chCode.1 this).2.2
  | succ n ih =>
    intro hP
    have ihn := ih (by omega)
    by_cases h1 : dg P y n ≠ dg P y (n + 1)
    · have : (n + 1, (dg P y (n + 1)).toNat) ∈ chCode P y' :=
        h ▸ mem_chCode.2 ⟨hP, Or.inr (by simpa using h1), rfl⟩
      exact dg_eq_of_toNat (rd_nonneg _) (rd_nonneg _) (mem_chCode.1 this).2.2
    · by_cases h2 : dg P y' n ≠ dg P y' (n + 1)
      · have : (n + 1, (dg P y' (n + 1)).toNat) ∈ chCode P y :=
          h.symm ▸ mem_chCode.2 ⟨hP, Or.inr (by simpa using h2), rfl⟩
        exact (dg_eq_of_toNat (rd_nonneg _) (rd_nonneg _) (mem_chCode.1 this).2.2).symm
      · push_neg at h1 h2; rw [← h1, ← h2, ihn]

theorem chCode_injOn (P : ℕ) (hP : 1 ≤ P) :
    Set.InjOn (chCode P) (Finset.range (3 ^ P - 1) : Set ℕ) := by
  intro y hy y' hy' h
  simp only [Finset.coe_range, Set.mem_Iio] at hy hy'
  have e := eq_sum_rd hP hy
  have e' := eq_sum_rd hP hy'
  have hd := dg_eq_of_chCode h
  have : (y : ℝ) = y' := by
    rw [e, e']
    refine Finset.sum_congr rfl fun i hi => ?_
    have := hd i (Finset.mem_range.1 hi)
    simp only [dg] at this
    rw [this]
  exact_mod_cast this

theorem card_chCode_le (P y : ℕ) :
    (chCode P y).card ≤ 1 + ((Finset.range P).filter fun i => dg P y i ≠ dg P y (i + 1)).card := by
  unfold chCode
  refine Finset.card_image_le.trans ?_
  calc _ ≤ (insert 0 (((Finset.range P).filter fun i => dg P y i ≠ dg P y (i + 1)).image
        (· + 1))).card := by
        refine Finset.card_le_card fun i hi => ?_
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        rcases hi.2 with h0 | h1
        · simp [h0]
        · refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨i - 1, ?_, ?_⟩)
          · have : i ≠ 0 := by rintro rfl; simp at h1
            simp only [Finset.mem_filter, Finset.mem_range]
            refine ⟨by omega, ?_⟩
            rwa [show i - 1 + 1 = i by omega]
          · have : i ≠ 0 := by rintro rfl; simp at h1
            omega
    _ ≤ _ := (Finset.card_insert_le _ _).trans (by rw [add_comm]; exact Nat.add_le_add_left Finset.card_image_le 1)

theorem card_changes_lt {P y K' : ℕ} {δ : ℝ} (hK : Real.cos (Real.pi / 9) ^ K' < δ)
    (hy : δ ≤ cycProd P (y : ℤ)) :
    ((Finset.range P).filter fun i => dg P y i ≠ dg P y (i + 1)).card < K' := by
  set C := (Finset.range P).filter fun i => dg P y i ≠ dg P y (i + 1)
  set c := Real.cos (Real.pi / 9)
  have hc0 : 0 ≤ c := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hc1 : c < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_pos]) (by positivity)
  have hprod : cycProd P (y : ℤ) ≤ c ^ C.card := by
    unfold cycProd
    calc _ ≤ ∏ i ∈ Finset.range P, (if i ∈ C then c else 1) := by
          refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i hi => ?_
          split_ifs with hC
          · have hne := (Finset.mem_filter.1 hC).2
            have e : 2 * Real.pi * (((y : ℤ) : ℝ) * 3 ^ i) / (3 ^ P - 1) =
                2 * Real.pi * (3 ^ i * ((y : ℝ) / (3 ^ P - 1))) := by push_cast; ring
            rw [e]
            refine abs_cos_le_of_rd_ne ?_
            simp only [dg] at hne
            rwa [show (3 : ℝ) * (3 ^ i * ((y : ℝ) / (3 ^ P - 1))) =
              3 ^ (i + 1) * ((y : ℝ) / (3 ^ P - 1)) by ring]
          · exact Real.abs_cos_le_one _
      _ = c ^ C.card := by
          rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
          congr 1
          rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (Finset.filter_subset _ _)]
  by_contra hcon
  push_neg at hcon
  have : c ^ C.card ≤ c ^ K' := pow_le_pow_of_le_one hc0 hc1.le hcon
  linarith

theorem card_powerset_le_le (S : Finset (ℕ × ℕ)) (K : ℕ) :
    ((S.powerset).filter fun Z => Z.card ≤ K).card ≤ (S.card + 1) ^ K := by
  have hsub : (S.powerset).filter (fun Z => Z.card ≤ K) ⊆
      (Finset.range (K + 1)).biUnion fun c => S.powersetCard c := by
    intro Z hZ
    simp only [Finset.mem_filter, Finset.mem_powerset] at hZ
    exact Finset.mem_biUnion.2 ⟨Z.card, Finset.mem_range.2 (by omega),
      Finset.mem_powersetCard.2 ⟨hZ.1, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  simp only [Finset.card_powersetCard]
  have : ∀ K : ℕ, ∑ c ∈ Finset.range (K + 1), S.card.choose c ≤ (S.card + 1) ^ K := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have h1 := Nat.choose_le_pow S.card (K + 1)
      have h2 : S.card ^ (K + 1) ≤ (S.card + 1) ^ K * S.card := by
        rw [pow_succ]; exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
      nlinarith
  exact this K

/-- **The large spectrum of the cyclic Cantor law is polynomial in the period (proved).** -/
theorem card_cycProd_ge_le' (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℕ, ∀ P : ℕ, 1 ≤ P →
    (((Finset.range (3 ^ P - 1)).filter fun y : ℕ => δ ≤ cycProd P (y : ℤ)).card : ℝ) ≤
      3 * (2 * P + 1) ^ K := by
  have hc1 : Real.cos (Real.pi / 9) < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_pos]) (by positivity)
  obtain ⟨K', hK'⟩ := exists_pow_lt_of_lt_one hδ hc1
  refine ⟨2 * K', fun P hP => ?_⟩
  set S := Finset.range P ×ˢ Finset.range 3
  have hmaps : ∀ y ∈ (Finset.range (3 ^ P - 1)).filter (fun y : ℕ => δ ≤ cycProd P (y : ℤ)),
      chCode P y ∈ (S.powerset).filter fun Z => Z.card ≤ K' := by
    intro y hy
    simp only [Finset.mem_filter] at hy
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun p hp => ?_, ?_⟩
    · obtain ⟨n, v⟩ := p
      obtain ⟨h1, -, h3⟩ := mem_chCode.1 hp
      simp only [S, Finset.mem_product, Finset.mem_range]
      refine ⟨h1, ?_⟩
      have := rd_lt (3 ^ n * ((y : ℝ) / (3 ^ P - 1)))
      have := rd_nonneg (3 ^ n * ((y : ℝ) / (3 ^ P - 1)))
      simp only [dg] at h3; omega
    · have := card_chCode_le P y
      have := card_changes_lt hK' hy.2
      omega
  have hcard := Finset.card_le_card_of_injOn (chCode P) hmaps
    ((chCode_injOn P hP).mono (by intro y hy; simp only [Finset.coe_filter] at hy; exact hy.1))
  have hS : S.card = 3 * P := by simp [S, mul_comm]
  have h2 := card_powerset_le_le S K'
  rw [hS] at h2
  have h3 : (3 * P + 1) ^ K' ≤ (2 * P + 1) ^ (2 * K') := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by nlinarith) _
  have : ((Finset.range (3 ^ P - 1)).filter (fun y : ℕ => δ ≤ cycProd P (y : ℤ))).card ≤
      3 * (2 * P + 1) ^ (2 * K') := by omega
  exact_mod_cast this

/-- **The large spectrum of the cyclic Cantor law is polynomial in the period (proved, `card_cycProd_ge_le'`).**
For `δ > 0` there is `K` such that at most `3·(2P+1)^K` residues `y mod 3^P − 1` have
`cycProd P y ≥ δ`.  English proof: at each cyclic ternary digit change of `y mod 3^P − 1` the factor
of `cycProd` is `≤ cos(π/9)` (the cyclic form of `CantorLiouville.abs_cos_le_of_tdig_ne`), so
`cycProd P y ≥ δ` forces fewer than `K ≈ 2 log(1/δ)/log(1/cos(π/9))` changes, and a cyclic string of
length `P` with `< K` changes is fixed by its change positions and run digits.
Use (review lap 3, 2026-10-07): counting settles the copy zone only when the orbit `c tᵐ mod 3^P − 1`
has more than `P^K` distinct points, i.e. for SHORT periods with large order
(`SuperPolyOrderPeriods`); for the long periods of `repReal` the orbit has `≈ kP` points and this
count is useless (the wrap wall `TOrbitCyclicDecay`). -/
theorem card_cycProd_ge_le (δ : ℝ) (hδ : 0 < δ) : ∃ K : ℕ, ∀ P : ℕ, 1 ≤ P →
    (((Finset.range (3 ^ P - 1)).filter fun y : ℕ => δ ≤ cycProd P (y : ℤ)).card : ℝ) ≤
      3 * (2 * P + 1) ^ K :=
  card_cycProd_ge_le' δ hδ

/-- **Superpolynomial order of `t` modulo `3^P − 1` (open conjecture; confidence 95%, no proof
known).**  For every `C` there are arbitrarily large `P` such that the order of `t` modulo the
`t`-free part of `3^P − 1` exceeds `P^C`.  Weaker than `ExpOrderPeriods` (exponential order with
`θ > log₃(3/2)`): with `card_cycProd_ge_le`, a short-period construction (period `P ≈ (log a)^C`,
copy stretches of length `exp(P^{1/C})`) would have its copy zone bounded by counting alone, up to
the gcd analogue of `BadGcdSparseH` (review lap 3).  Corvaja–Zannier (`CZGcdPow`) gives only
`ord/P → ∞`.  Not pursued: the frozen construction uses long periods (DIRECTION, 2026-10-07). -/
def SuperPolyOrderPeriods (t : ℕ) : Prop :=
  ∀ C L : ℕ, ∃ P ≥ L, ∀ e : ℕ, 0 < e → e ≤ P ^ C →
    ¬ ((3 ^ P - 1) / Nat.gcd (3 ^ P - 1) (t ^ P)) ∣ (t ^ e - 1)

/-! ### Pair classification (combinatorial core of the assembly) -/

/-- `P` lies within the band of a copy-run boundary: within `[a_k − W − K, a_k + K]` or
`[E_k − K, E_k + W + K]` for an even run `k`. -/
def NearCopyBdry (W K P : ℕ) : Prop := ∃ k, Even k ∧
  ((runStart k ≤ P + W + K ∧ P ≤ runStart k + K) ∨
    ((k + 2) * runStart k ≤ P + K ∧ P ≤ (k + 2) * runStart k + W + K))

theorem runStart_add_two (k : ℕ) :
    runStart (k + 2) = 4 * (k + 3) * ((k + 2) * runStart k) := by
  rw [runStart_succ_eq, runStart_succ_eq]; ring

theorem runEnd_le_runStart {k k' : ℕ} (h : k' < k) : (k' + 2) * runStart k' ≤ runStart k := by
  have h1 : (k' + 2) * runStart k' ≤ runStart (k' + 1) := by
    rw [runStart_succ_eq]; nlinarith
  exact h1.trans (runStart_mono (by omega))

/-- **Deep or fresh.**  A place away from every copy-run boundary is deep inside an even run, or
has a fresh neighbourhood of radius `W + K`. -/
theorem deep_or_fresh {W K P : ℕ} (hP : ¬ NearCopyBdry W K P) :
    (∃ k, Even k ∧ runStart k + K < P ∧ P + K < (k + 2) * runStart k) ∨
      (∀ q, P ≤ q + W + K → q ≤ P + W + K → isFresh q = true) := by
  unfold NearCopyBdry at hP
  push Not at hP
  by_cases hc : ∃ k, Even k ∧ runStart k ≤ P ∧ P < (k + 2) * runStart k
  · obtain ⟨k, hk, h1, h2⟩ := hc
    obtain ⟨hA, hE⟩ := hP k hk
    left
    refine ⟨k, hk, ?_, ?_⟩
    · by_contra hh; exact absurd (hA (by omega)) (by omega)
    · by_contra hh; exact absurd (hE (by omega)) (by omega)
  · right
    intro q hq1 hq2
    by_contra hq
    rw [Bool.not_eq_true, isFresh_eq_false] at hq
    obtain ⟨k, hk, h1, h2⟩ := hq
    obtain ⟨hA, hE⟩ := hP k hk
    by_cases hlt : P < runStart k
    · exact absurd (hA (by omega)) (by omega)
    · by_cases hge : (k + 2) * runStart k ≤ P
      · exact absurd (hE (by omega)) (by omega)
      · exact hc ⟨k, hk, by omega, by omega⟩

/-- **One copy run per bounded window.**  If `P` lies in even run `k` and `P ≤ Q ≤ ρP` with
`ρ ≤ 4(k+3)` (the ratio of the fresh stretch after run `k`), any even run containing `Q` is `k`. -/
theorem run_unique {k k' ρ P Q : ℕ} (hk : Even k) (hk' : Even k') (hρ : ρ ≤ 4 * (k + 3))
    (h1 : runStart k ≤ P) (h2 : P < (k + 2) * runStart k)
    (h1' : runStart k' ≤ Q) (h2' : Q < (k' + 2) * runStart k') (hPQ : P ≤ Q) (hQ : Q ≤ ρ * P) :
    k' = k := by
  rcases lt_trichotomy k' k with hlt | heq | hgt
  · have := runEnd_le_runStart hlt; omega
  · exact heq
  · have hk2 : k + 2 ≤ k' := by
      obtain ⟨i, rfl⟩ := hk; obtain ⟨j, rfl⟩ := hk'; omega
    have hA := runStart_mono hk2
    rw [runStart_add_two] at hA
    have : ρ * P < 4 * (k + 3) * ((k + 2) * runStart k) := by
      calc ρ * P ≤ 4 * (k + 3) * P := Nat.mul_le_mul_right _ hρ
        _ < _ := by have : 0 < 4 * (k + 3) := by omega
                    exact Nat.mul_lt_mul_of_pos_left h2 this
    omega

theorem run_index_ge {k k₀ P : ℕ} (h0 : runStart k₀ ≤ P) (h2 : P < (k + 2) * runStart k) :
    k₀ ≤ k := by
  by_contra h
  have := runEnd_le_runStart (show k < k₀ by omega)
  omega

/-- **Pair classification.**  For a pair with low end `v` (of `ξ` and of `Y = h bᵐ`), top `y` of
`Y`, low end `u` of the high part `h bⁿ` and top `T` of `ξ`, away from copy-run boundaries and
past run `k₀` (with `ρ ≤ 4(k₀+3)` bounding the window ratios), one of six classes holds:
(1) low window of `ξ` fresh; (2) top window of `Y` fresh, below `u`; (3) separated, low window of
the high part fresh; (4) top window of `ξ` fresh; (5) the window of `ξ` inside an even run;
(6) separated, the high part inside an even run, `Y` far below it.  Proved. -/
theorem pair_classify_rep {W K ρ k₀ v y u T : ℕ} (hρ : ρ ≤ 4 * (k₀ + 3))
    (hv0 : runStart k₀ ≤ v) (hW : W ≤ v)
    (hvy : v ≤ y) (hy : y ≤ ρ * v) (hvu : v ≤ u) (huT : u ≤ T) (hT : T ≤ ρ * u)
    (hsep : u < y + K → T ≤ ρ * v)
    (hnv : ¬ NearCopyBdry W K v) (hny : ¬ NearCopyBdry W K y) (hnu : ¬ NearCopyBdry W K u)
    (hnT : ¬ NearCopyBdry W K T) :
    (∀ p, v + 1 ≤ p → p < v + W → isFresh p = true) ∨
    (W ≤ y ∧ y ≤ u ∧ ∀ j < W, isFresh (y - 1 - j) = true) ∨
    (y + K ≤ u ∧ ∀ p, u + 1 ≤ p → p < u + W → isFresh p = true) ∨
    (W ≤ T ∧ ∀ j < W, isFresh (T - 1 - j) = true) ∨
    (∃ k, Even k ∧ runStart k ≤ v ∧ T + K < (k + 2) * runStart k) ∨
    (∃ k, Even k ∧ runStart k ≤ u ∧ T + K < (k + 2) * runStart k ∧ y + K ≤ runStart k) := by
  rcases deep_or_fresh hnv with ⟨k, hk, hv1, hv2⟩ | hfv
  swap
  · exact Or.inl fun p hp1 hp2 => hfv p (by omega) (by omega)
  right
  have hkk₀ : k₀ ≤ k := run_index_ge hv0 (by omega)
  have hρk : ρ ≤ 4 * (k + 3) := hρ.trans (by omega)
  rcases deep_or_fresh hnT with ⟨k', hk', hT1, hT2⟩ | hfT
  swap
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, fun j hj => hfT _ (by omega) (by omega)⟩))
  by_cases hkk : k' = k
  · subst hkk
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k', hk', by omega, hT2⟩)))
  -- the window of `ξ` meets two copy runs: it is separated
  have hsep' : y + K ≤ u := by
    by_contra hc
    exact hkk (run_unique hk hk' hρk (by omega) (by omega) (by omega) (by omega) (by omega)
      (hsep (by omega)))
  rcases deep_or_fresh hny with ⟨ky, hky, hy1, hy2⟩ | hfy
  swap
  · exact Or.inl ⟨by omega, by omega, fun j hj => hfy _ (by omega) (by omega)⟩
  have hkyk : ky = k := run_unique hk hky hρk (by omega) (by omega) (by omega) (by omega)
    (by omega) hy
  subst hkyk
  rcases deep_or_fresh hnu with ⟨ku, hku, hu1, hu2⟩ | hfu
  swap
  · exact Or.inr (Or.inl ⟨hsep', fun p hp1 hp2 => hfu p (by omega) (by omega)⟩)
  have hku0 : k₀ ≤ ku := run_index_ge (k := ku) (hv0.trans hvu) (by omega)
  have hρu : ρ ≤ 4 * (ku + 3) := hρ.trans (by omega)
  have hkTu : k' = ku := run_unique hku hk' hρu (by omega) (by omega) (by omega) (by omega)
    huT hT
  subst hkTu
  have hlt : ky < k' := by
    rcases lt_trichotomy ky k' with h | h | h
    · exact h
    · exact absurd h.symm hkk
    · exfalso
      have := runEnd_le_runStart h
      omega
  have := runEnd_le_runStart hlt
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨k', hk', by omega, hT2, by omega⟩)))

/-! ### Per-class Riesz bounds -/

theorem sum_two_div_three_pow (W : ℕ) :
    ∑ q ∈ Finset.range W, (2 : ℝ) / 3 ^ (q + 1) = 1 - 1 / 3 ^ W := by
  induction W with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; field_simp; ring

theorem hf_true_lip (W : ℕ) (u X : ℝ) :
    |Hf (fun _ => true) 0 W u - Hf (fun _ => true) 0 W X| ≤ Real.pi * |u - X| := by
  rw [CantorExactExponentProfile.hf_true_eq, CantorExactExponentProfile.hf_true_eq]
  have hb : ∀ x : ℝ, 0 ≤ |Real.cos x| ∧ |Real.cos x| ≤ 1 :=
    fun x => ⟨abs_nonneg _, Real.abs_cos_le_one _⟩
  refine (CantorExactExponentProfile.abs_prod_sub_prod_le _ _ _ (fun k => hb _)
    (fun k => hb _)).trans ?_
  have hterm : ∀ q ∈ Finset.Ico 1 W, |(|Real.cos (2 * Real.pi * u / 3 ^ (q + 1))| -
      |Real.cos (2 * Real.pi * X / 3 ^ (q + 1))|)| ≤ Real.pi * |u - X| * (2 / 3 ^ (q + 1)) := by
    intro q _
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ((Real.abs_cos_sub_cos_le _ _).trans
      (le_of_eq ?_))
    rw [show 2 * Real.pi * u / 3 ^ (q + 1) - 2 * Real.pi * X / 3 ^ (q + 1) =
      (u - X) * (2 * Real.pi / 3 ^ (q + 1)) by ring, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi / 3 ^ (q + 1))]
    ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hs : ∑ q ∈ Finset.Ico 1 W, (2 : ℝ) / 3 ^ (q + 1) ≤ 1 := by
    calc _ ≤ ∑ q ∈ Finset.range W, (2 : ℝ) / 3 ^ (q + 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun q hq => Finset.mem_range.2 (Finset.mem_Ico.1 hq).2) fun _ _ _ => by positivity
      _ ≤ 1 := by rw [sum_two_div_three_pow]; have : (0:ℝ) < 1 / 3 ^ W := by positivity
                  linarith
  have : 0 ≤ Real.pi * |u - X| := by positivity
  nlinarith

/-- **Low window with a perturbation.**  Fresh places `[w+1, w+W)` and `ξ = 3^w X + Z` with
`|Z| ≤ 3^w ε` give `Bf ξ ≤ Hf_true(X) + π ε`. -/
theorem bf_le_hf_true_add (free : ℕ → Bool) {M w W : ℕ} (hM : w + W ≤ M)
    (hfree : ∀ p, w + 1 ≤ p → p < w + W → free p = true) (X Z ε : ℝ)
    (hZ : |Z| ≤ 3 ^ w * ε) :
    Bf free M (3 ^ w * X + Z) ≤ Hf (fun _ => true) 0 W X + Real.pi * ε := by
  have h3 : (0 : ℝ) < 3 ^ w := by positivity
  have e : 3 ^ w * X + Z = 3 ^ w * (X + Z / 3 ^ w) := by field_simp
  rw [e]
  refine (CantorExactExponentProfile.bf_le_hf_true free hM hfree _).trans ?_
  have hl := hf_true_lip W (X + Z / 3 ^ w) X
  have hd : |X + Z / 3 ^ w - X| ≤ ε := by
    rw [show X + Z / 3 ^ w - X = Z / 3 ^ w by ring, abs_div, abs_of_pos h3, div_le_iff₀ h3]
    linarith
  have := abs_le.1 hl
  nlinarith [Real.pi_pos]

/-- **Copy-run bound with a perturbation.**  For even `k`, `a = a_k`, any real `ξ` and integer
`η₀`: `repBound (some k) ξ ≤ cycProd a η₀ + π(|ξ − 3^a η₀|/3^a + |ξ|/3^{(k+2)a})`.  Classes 5
(`Z = 0`) and 6 (`Z = −Y`, `Y` below the run). -/
theorem repBound_some_le_cyc (M k : ℕ) (hk : Even k) (ξ : ℝ) (η₀ : ℤ) :
    repBound M (some k) ξ ≤ cycProd (runStart k) η₀ + Real.pi *
      (|ξ - 3 ^ runStart k * η₀| / 3 ^ runStart k + |ξ| / 3 ^ ((k + 2) * runStart k)) := by
  set a := runStart k
  simp only [repBound, if_pos hk]
  have h2 := cycProdR_lip a (ξ * (1 - (3 : ℝ) ^ (-(((k + 1) * a : ℕ) : ℤ))) / 3 ^ a) η₀
  rw [cycProdR_intCast] at h2
  have h3 : (0 : ℝ) < 3 ^ a := by positivity
  have h3' : (0 : ℝ) < 3 ^ ((k + 2) * a) := by positivity
  have hz : (3 : ℝ) ^ (-(((k + 1) * a : ℕ) : ℤ)) = 3 ^ a / 3 ^ ((k + 2) * a) := by
    rw [zpow_neg, zpow_natCast, show (k + 2) * a = a + (k + 1) * a by ring, pow_add]
    field_simp
  have e : ξ * (1 - (3 : ℝ) ^ (-(((k + 1) * a : ℕ) : ℤ))) / 3 ^ a - η₀ =
      (ξ - 3 ^ a * η₀) / 3 ^ a - ξ / 3 ^ ((k + 2) * a) := by
    rw [hz]; field_simp; ring
  rw [e] at h2
  have ht : |(ξ - 3 ^ a * η₀) / 3 ^ a - ξ / 3 ^ ((k + 2) * a)| ≤
      |ξ - 3 ^ a * η₀| / 3 ^ a + |ξ| / 3 ^ ((k + 2) * a) := by
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_div, abs_of_pos h3, abs_of_pos h3']
  have := (abs_le.1 h2).2
  nlinarith [Real.pi_pos]

/-- **Window ratio.**  If `b ≤ 3^{s(ρ−1)}` and `H < 3^{sm}`, the ternary length of `H bᵐ` is
`< ρ·sm`: the top `y` of `Y = h bᵐ` sits below `ρ v`, `v = sm` (hypothesis `hy` of
`pair_classify_rep`). -/
theorem log_mul_pow_lt {b s ρ H m : ℕ} (hρ : 1 ≤ ρ) (hb : b ≤ 3 ^ (s * (ρ - 1)))
    (hH : H < 3 ^ (s * m)) (hsm : 0 < s * m) : Nat.log 3 (H * b ^ m) < ρ * (s * m) := by
  rcases Nat.eq_zero_or_pos (H * b ^ m) with h0 | hpos
  · rw [h0, Nat.log_zero_right]
    positivity
  refine Nat.log_lt_of_lt_pow hpos.ne' ?_
  calc H * b ^ m < 3 ^ (s * m) * (3 ^ (s * (ρ - 1))) ^ m := by
        have : 0 < b ^ m := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
        calc H * b ^ m < 3 ^ (s * m) * b ^ m := Nat.mul_lt_mul_of_pos_right hH this
          _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb m)
    _ = 3 ^ (ρ * (s * m)) := by
        rw [← pow_mul, ← pow_add]; congr 1
        obtain ⟨r, rfl⟩ : ∃ r, ρ = r + 1 := ⟨ρ - 1, by omega⟩
        simp only [Nat.add_sub_cancel]; ring

/-- The ternary length of `H (3ˢt)ᵐ` is at least `sm` (hypothesis `hvy` of
`pair_classify_rep`). -/
theorem le_log_mul_pow {s t H m : ℕ} (hH : 1 ≤ H) (ht : 1 ≤ t) :
    s * m ≤ Nat.log 3 (H * (3 ^ s * t) ^ m) := by
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  calc 3 ^ (s * m) = 1 * (3 ^ s * 1) ^ m := by rw [pow_mul]; ring
    _ ≤ H * (3 ^ s * t) ^ m := Nat.mul_le_mul hH (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ ht) m)

/-- The difference `(3ˢt)^{m+d} − (3ˢt)^m` (`d ≥ 1`, `t ≥ 2`) is at least `3^{s(m+d)}`. -/
theorem three_pow_le_pow_sub_pow {s t m d : ℕ} (ht : 2 ≤ t) (hd : 1 ≤ d) :
    3 ^ (s * (m + d)) ≤ (3 ^ s * t) ^ (m + d) - (3 ^ s * t) ^ m := by
  have h1 : (3 ^ s * t) ^ m * (3 ^ s * t) ^ d - (3 ^ s * t) ^ m =
      (3 ^ s * t) ^ m * ((3 ^ s * t) ^ d - 1) := by rw [Nat.mul_sub_one]
  rw [pow_add, h1]
  have hA : 3 ^ (s * m) ≤ (3 ^ s * t) ^ m := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by omega)) m
  have hB : 3 ^ (s * d) ≤ (3 ^ s * t) ^ d - 1 := by
    have : 3 ^ (s * d) * 2 ≤ (3 ^ s * t) ^ d := by
      rw [mul_pow, pow_mul]
      exact Nat.mul_le_mul_left _ ((show 2 ≤ 2 ^ d from by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd).trans (Nat.pow_le_pow_left ht d))
    have : 1 ≤ 3 ^ (s * d) := Nat.one_le_pow _ _ (by norm_num)
    omega
  rw [mul_add, pow_add]
  exact Nat.mul_le_mul hA hB

/-- The top `T` of `ξ = H((3ˢt)ⁿ − (3ˢt)ᵐ)`, `n > m`, is at least `u = sn` (hypothesis `huT`). -/
theorem le_log_pair {s t H m d : ℕ} (hH : 1 ≤ H) (ht : 2 ≤ t) (hd : 1 ≤ d) :
    s * (m + d) ≤ Nat.log 3 (H * ((3 ^ s * t) ^ (m + d) - (3 ^ s * t) ^ m)) :=
  Nat.le_log_of_pow_le (by norm_num) ((three_pow_le_pow_sub_pow ht hd).trans
    (Nat.le_mul_of_pos_left _ hH))

/-- The top of `ξ` is at most the top of `H bⁿ` (hypothesis `hT` via `log_mul_pow_lt`). -/
theorem log_pair_le_log {b H m d : ℕ} :
    Nat.log 3 (H * (b ^ (m + d) - b ^ m)) ≤ Nat.log 3 (H * b ^ (m + d)) :=
  Nat.log_mono_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- **Separation hypothesis `hsep` of `pair_classify_rep`.**  With `T ≤ ρ₁u`, `y ≤ ρ₀v` and
`K ≤ v`, an unseparated pair (`u < y + K`) has `T ≤ ρ₁(ρ₀+1)v`. -/
theorem hsep_of {ρ₀ ρ₁ v y u T K : ℕ} (hT : T ≤ ρ₁ * u) (hy : y ≤ ρ₀ * v) (hK : K ≤ v) :
    u < y + K → T ≤ ρ₁ * (ρ₀ + 1) * v := by
  intro hu
  have : u ≤ (ρ₀ + 1) * v := by nlinarith
  calc T ≤ ρ₁ * u := hT
    _ ≤ ρ₁ * ((ρ₀ + 1) * v) := Nat.mul_le_mul_left _ this
    _ = _ := by ring

theorem four_pow_le_runStart (k : ℕ) : 4 ^ (k + 1) ≤ runStart k := by
  induction k with
  | zero => simp [runStart]
  | succ k ih => rw [runStart_succ_eq, pow_succ]; nlinarith

theorem card_shift_le (s A L : ℕ) (hs : 1 ≤ s) (S : Finset ℕ)
    (hS : ∀ n ∈ S, A ≤ s * n + L ∧ s * n ≤ A) : S.card ≤ L + 1 := by
  have : S.card ≤ (Finset.Icc (A - L) A).card := by
    refine Finset.card_le_card_of_injOn (fun n => s * n) (fun n hn => ?_) ?_
    · have := hS n hn; simp only [Finset.coe_Icc, Set.mem_Icc]; omega
    · intro x _ y _ hxy
      exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
  simp at this; omega

open Classical in
/-- **Band count.**  At most `2(W+2K+1)(log₄(sN+W+K)+1)` of the `n < N` put `sn` in a copy-run
boundary band: these pairs are bounded by `1` in the assembly. -/
theorem card_nearCopyBdry_le (s W K N : ℕ) (hs : 1 ≤ s) :
    ((Finset.range N).filter fun n => NearCopyBdry W K (s * n)).card ≤
      2 * (W + 2 * K + 1) * (Nat.log 4 (s * N + W + K) + 1) := by
  set L := Nat.log 4 (s * N + W + K)
  have hsub : (Finset.range N).filter (fun n => NearCopyBdry W K (s * n)) ⊆
      (Finset.range (L + 1)).biUnion fun k =>
        ((Finset.range N).filter fun n => runStart k ≤ s * n + W + K ∧ s * n ≤ runStart k + K) ∪
        ((Finset.range N).filter fun n => (k + 2) * runStart k ≤ s * n + K ∧
          s * n ≤ (k + 2) * runStart k + W + K) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, k, -, hk⟩ := hn
    have hak : runStart k ≤ s * N + W + K := by
      have : s * n ≤ s * N := Nat.mul_le_mul_left _ hnN.le
      rcases hk with h | h
      · omega
      · have : runStart k ≤ (k + 2) * runStart k := Nat.le_mul_of_pos_left _ (by omega)
        omega
    have hkL : k < L + 1 := by
      have h4 := (four_pow_le_runStart k).trans hak
      have := Nat.le_log_of_pow_le (by norm_num) h4
      omega
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union, Finset.mem_filter]
    exact ⟨k, hkL, hk.imp (fun h => ⟨hnN, h⟩) (fun h => ⟨hnN, h⟩)⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  have hk : ∀ k ∈ Finset.range (L + 1),
      (((Finset.range N).filter fun n => runStart k ≤ s * n + W + K ∧ s * n ≤ runStart k + K) ∪
        ((Finset.range N).filter fun n => (k + 2) * runStart k ≤ s * n + K ∧
          s * n ≤ (k + 2) * runStart k + W + K)).card ≤ 2 * (W + 2 * K + 1) := by
    intro k _
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := card_shift_le s (runStart k + K) (W + 2 * K) hs
      ((Finset.range N).filter fun n => runStart k ≤ s * n + W + K ∧ s * n ≤ runStart k + K)
      (fun n hn => by simp only [Finset.mem_filter] at hn; omega)
    have h2 := card_shift_le s ((k + 2) * runStart k + W + K) (W + 2 * K) hs
      ((Finset.range N).filter fun n => (k + 2) * runStart k ≤ s * n + K ∧
          s * n ≤ (k + 2) * runStart k + W + K)
      (fun n hn => by simp only [Finset.mem_filter] at hn; omega)
    omega
  refine (Finset.sum_le_sum hk).trans ?_
  simp; ring_nf; omega

/-- **Class-1 sum (low window).**  For `h` prime to 3, summing the all-free majorant at
`X = h(bᵈ − 1)tᵐ` over `1 ≤ d < N`, `m < N` gives `N(N + 2·3ʲ)(3/2)^{tb}(2/3)ʲ`. -/
theorem sum_class_low_le {s t : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (h3 : ¬ 3 ∣ t) (h : ℕ)
    (hh : ¬ 3 ∣ h) (j N : ℕ) :
    ∑ d ∈ Finset.Ico 1 N, ∑ m ∈ Finset.range N,
      CantorLiouville.Hf (fun _ => true) 0 (j + 1) ((h * ((3 ^ s * t) ^ d - 1) * t ^ m : ℕ) : ℝ) ≤
      N * ((N + 2 * 3 ^ j) * (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t * (2 / 3 : ℝ) ^ j) := by
  have hc : ∀ d ∈ Finset.Ico 1 N, ¬ 3 ∣ h * ((3 ^ s * t) ^ d - 1) := by
    intro d hd h3d
    have hd1 : 1 ≤ d := (Finset.mem_Ico.1 hd).1
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3d with h1 | h1
    · exact hh h1
    · have h0 : 3 ∣ (3 ^ s * t) ^ d := by
        exact Dvd.dvd.pow (Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _) (by omega)
      have hpos : 1 ≤ (3 ^ s * t) ^ d := Nat.one_le_iff_ne_zero.2 (by positivity)
      have := Nat.dvd_sub h0 h1
      rw [Nat.sub_sub_self hpos] at this
      norm_num at this
  calc _ ≤ ∑ d ∈ Finset.Ico 1 N,
        ((N + 2 * 3 ^ j) * (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t * (2 / 3 : ℝ) ^ j) :=
        Finset.sum_le_sum fun d hd =>
          CantorExactExponentProfile.sum_hf_true_le ht h3 j _ (hc d hd) N
    _ ≤ _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ico]
        gcongr
        exact_mod_cast Nat.sub_le _ _

/-- **Class-3 pointwise bound.**  Separated pair: fresh low window `[sn+1, sn+W)` of the high part
and `|h bᵐ| ≤ 3^{sn−K}` give `repBound none ≤ Hf_true(h tⁿ) + π 3^{−K}`. -/
theorem repBound_class_sep_le {s t M W K n m : ℕ} (h : ℤ) (hM : s * n + W ≤ M)
    (hfr : ∀ p, s * n + 1 ≤ p → p < s * n + W → isFresh p = true)
    (hK : K ≤ s * n)
    (hY : |(h : ℝ) * ((3 ^ s * t : ℕ) : ℝ) ^ m| ≤ 3 ^ (s * n - K)) :
    repBound M none (h * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m)) ≤
      Hf (fun _ => true) 0 W ((h : ℝ) * (t : ℝ) ^ n) + Real.pi * (1 / 3 ^ K) := by
  simp only [repBound]
  have e : (h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m) =
      3 ^ (s * n) * ((h : ℝ) * (t : ℝ) ^ n) + -((h : ℝ) * ((3 ^ s * t : ℕ) : ℝ) ^ m) := by
    push_cast; rw [pow_mul, mul_pow]; ring
  rw [e]
  refine bf_le_hf_true_add isFresh hM hfr _ _ _ ?_
  rw [abs_neg]
  refine hY.trans (le_of_eq ?_)
  rw [show s * n = (s * n - K) + K by omega, pow_add]
  field_simp
  congr 1; omega

/-- **Class-6 pointwise bound.**  Separated pair with the high part in copy run `k`
(`a = a_k ≤ sn`): `repBound (some k) ≤ cycProd a (h tⁿ) + π(|h bᵐ|/3^a + |ξ|/3^{(k+2)a})`. -/
theorem repBound_class_copySep_le {s t M k n m : ℕ} (hk : Even k) (h : ℤ)
    (ha : runStart k ≤ s * n) :
    repBound M (some k) (h * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m)) ≤
      cycProd (runStart k) (h * (t : ℤ) ^ n) + Real.pi *
        (|(h : ℝ) * ((3 ^ s * t : ℕ) : ℝ) ^ m| / 3 ^ runStart k +
          |h * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m)| /
            3 ^ ((k + 2) * runStart k)) := by
  set a := runStart k
  have := repBound_some_le_cyc M k hk (h * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m))
    (3 ^ (s * n - a) * (h * (t : ℤ) ^ n))
  rw [cycProd_mul_three_pow] at this
  have e : (h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m) -
      3 ^ a * (((3 ^ (s * n - a) * (h * (t : ℤ) ^ n) : ℤ)) : ℝ) =
      -((h : ℝ) * ((3 ^ s * t : ℕ) : ℝ) ^ m) := by
    push_cast
    have e3 : (3 : ℝ) ^ a * 3 ^ (s * n - a) = 3 ^ (s * n) := by rw [← pow_add]; congr 1; omega
    rw [show (3 : ℝ) ^ a * (3 ^ (s * n - a) * (h * t ^ n)) = (3 ^ a * 3 ^ (s * n - a)) * (h * t ^ n)
      by ring, e3, pow_mul, mul_pow]; ring
  rwa [e, abs_neg] at this

/-- **Top phase of `c (3ˢt)ᵐ`.**  `{log₃|c bᵐ|} = {m log₃ t + log₃|c|}`: the top-window phases of
classes 2 (`c = h`) and 4 (`c = h(bᵈ − 1)`) are a Kronecker orbit, summed by `sum_topProd_le`. -/
theorem fract_logb_mul_pow {s t : ℕ} (ht : 1 ≤ t) (c : ℝ) (hc : c ≠ 0) (m : ℕ) :
    Int.fract (Real.logb 3 |c * ((3 ^ s * t : ℕ) : ℝ) ^ m|) =
      Int.fract (m * Real.logb 3 t + Real.logb 3 |c|) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have e : Real.logb 3 |c * ((3 ^ s * t : ℕ) : ℝ) ^ m| =
      (m * Real.logb 3 t + Real.logb 3 |c|) + ((s * m : ℕ) : ℤ) := by
    push_cast
    rw [abs_mul, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < 3 ^ s * t),
      Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_mul (by positivity)
      (by positivity), Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    ring
  rw [e, Int.fract_add_intCast]

/-- **Class-4 pointwise bound (top window of `ξ`).**  With `ξ = h(b^{m+d} − bᵐ)` and fresh
places `K` below its top `T = ⌊log₃|ξ|⌋`: `repBound none ξ ≤ topProd K {m log₃t + log₃|h(bᵈ−1)|}`. -/
theorem repBound_class_top_le {s t M K m d : ℕ} (ht : 1 ≤ t) (h : ℤ)
    (hξ : 1 ≤ |(h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℝ) ^ m)|)
    (hK : K ≤ ⌊Real.logb 3 |(h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ (m + d) -
      ((3 ^ s * t : ℕ) : ℝ) ^ m)|⌋₊)
    (hfr : ∀ k < K, isFresh (⌊Real.logb 3 |(h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ (m + d) -
      ((3 ^ s * t : ℕ) : ℝ) ^ m)|⌋₊ - 1 - k) = true)
    (hM : ⌊Real.logb 3 |(h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ (m + d) -
      ((3 ^ s * t : ℕ) : ℝ) ^ m)|⌋₊ ≤ M) :
    repBound M none ((h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℝ) ^ m)) ≤
      CantorExactExponentProfile.topProd K (Int.fract (m * Real.logb 3 t +
        Real.logb 3 |(h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ d - 1)|)) := by
  simp only [repBound]
  refine (CantorExactExponentProfile.bf_le_topProd isFresh M K _ hξ hK hfr hM).trans (le_of_eq ?_)
  have e : (h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℝ) ^ m) =
      ((h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ d - 1)) * ((3 ^ s * t : ℕ) : ℝ) ^ m := by ring
  have hc : (h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ d - 1) ≠ 0 := by
    intro h0; rw [e, h0, zero_mul, abs_zero] at hξ; norm_num at hξ
  rw [e, fract_logb_mul_pow ht _ hc]

/-- **Class-2 pointwise bound (top window of `Y = h bᵐ`).**  If the top `n_Y = ⌊log₃|Y|⌋` of
`Y` is at most `sn` and the `K` places below it are fresh, then
`repBound none (h(bⁿ − bᵐ)) ≤ topProd K {m log₃ t + log₃|h|}`. -/
theorem repBound_class_topY_le {s t M K n m : ℕ} (ht : 1 ≤ t) (h : ℤ)
    (hY : 1 ≤ |(((h * ((3 ^ s * t : ℕ) : ℤ) ^ m : ℤ)) : ℝ)|)
    (hK : K ≤ ⌊Real.logb 3 |(((h * ((3 ^ s * t : ℕ) : ℤ) ^ m : ℤ)) : ℝ)|⌋₊)
    (hfr : ∀ k < K, isFresh (⌊Real.logb 3 |(((h * ((3 ^ s * t : ℕ) : ℤ) ^ m : ℤ)) : ℝ)|⌋₊
      - 1 - k) = true)
    (hM : ⌊Real.logb 3 |(((h * ((3 ^ s * t : ℕ) : ℤ) ^ m : ℤ)) : ℝ)|⌋₊ ≤ M)
    (hyu : ⌊Real.logb 3 |(((h * ((3 ^ s * t : ℕ) : ℤ) ^ m : ℤ)) : ℝ)|⌋₊ ≤ s * n) :
    repBound M none ((h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m)) ≤
      CantorExactExponentProfile.topProd K (Int.fract (m * Real.logb 3 t +
        Real.logb 3 |(h : ℝ)|)) := by
  simp only [repBound]
  have hdvd : (3 : ℤ) ^ ⌊Real.logb 3 |(((h * ((3 ^ s * t : ℕ) : ℤ) ^ m : ℤ)) : ℝ)|⌋₊ ∣
      (h * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ m)) +
        h * ((3 ^ s * t : ℕ) : ℤ) ^ m := by
    rw [show h * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ m) +
        h * ((3 ^ s * t : ℕ) : ℤ) ^ m = h * ((3 ^ s * t : ℕ) : ℤ) ^ n by ring]
    refine Dvd.dvd.mul_left ((pow_dvd_pow 3 hyu).trans ?_) _
    push_cast
    rw [pow_mul, mul_pow]; exact Dvd.intro _ rfl
  have := CantorExactExponentProfile.bf_le_topProd_of_dvd isFresh M K _ _ hY hK hfr hM hdvd
  push_cast at this ⊢
  refine this.trans (le_of_eq ?_)
  have hh : (h : ℝ) ≠ 0 := by
    intro h0; push_cast at hY; rw [h0, zero_mul, abs_zero] at hY; norm_num at hY
  have := fract_logb_mul_pow (s := s) ht (h : ℝ) hh m
  push_cast at this
  rw [this]

theorem gcd_sq_le_of_natAbs {h : ℤ} (hh : h ≠ 0) (A : ℕ) (hA : (h.natAbs : ℝ) ^ 2 ≤ 3 ^ A - 1) :
    (Int.gcd h (3 ^ A - 1) : ℝ) ^ 2 ≤ 3 ^ A - 1 := by
  have : Int.gcd h (3 ^ A - 1) ≤ h.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hh)
    (Int.gcd_dvd_natAbs_left _ _)
  have : (Int.gcd h (3 ^ A - 1) : ℝ) ≤ h.natAbs := by exact_mod_cast this
  nlinarith [(Int.gcd h (3 ^ A - 1)).cast_nonneg (α := ℝ)]

/-- **Class-6 sum.**  Under `TOrbitCyclicDecay t`, for `|h|² ≤ 3^A − 1` and `A ≤ N' ≤ A³`, the
copy products `cycProd A (h tⁿ)` summed over `n < N'` and any `N` lower indices are
`≤ N·C N'^{1−δ}`. -/
theorem sum_class_copySep_le {t : ℕ} (hT : TOrbitCyclicDecay t) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ (h : ℤ), h ≠ 0 → ∀ A N' N : ℕ, 1 ≤ A → A ≤ N' → N' ≤ A ^ 3 →
      (h.natAbs : ℝ) ^ 2 ≤ 3 ^ A - 1 →
      ∑ _m ∈ Finset.range N, ∑ n ∈ Finset.range N', cycProd A (h * (t : ℤ) ^ n) ≤
        N * (C * (N' : ℝ) ^ (1 - δ)) := by
  obtain ⟨C, δ, hδ, hC⟩ := hT
  refine ⟨C, δ, hδ, fun h hh A N' N hA h1 h2 hg => ?_⟩
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  gcongr
  exact hC A N' hA h1 h2 h (gcd_sq_le_of_natAbs hh A hg)

/-- **Top-window class sums (classes 2 and 4).**  Under Baker, for any family of shifts `β_d`,
`Σ_{d<N''} Σ_{m<N} topProd K {m log₃t + β_d} ≤ N''(3N(2/3)^K + 4N(1/3)^K + C 9^K N^{1−κ})`. -/
theorem sum_class_top_le {t : ℕ} (ht : 2 ≤ t) (h3 : ¬ 3 ∣ t)
    (hB : CantorExactExponentProfile.Literature.BakerLogDiscrepancy) :
    ∃ C κ : ℝ, 0 < κ ∧ ∀ N : ℕ, 1 ≤ N → ∀ (K N'' : ℕ) (β : ℕ → ℝ),
      ∑ d ∈ Finset.range N'', ∑ m ∈ Finset.range N,
        CantorExactExponentProfile.topProd K (Int.fract (m * Real.logb 3 t + β d)) ≤
        N'' * (3 * N * (2 / 3 : ℝ) ^ K + 4 * N * (1 / 3 : ℝ) ^ K + C * 9 ^ K * (N : ℝ) ^ (1 - κ)) := by
  obtain ⟨C, κ, hκ, hC⟩ := CantorExactExponentProfile.sum_topProd_le (hB t ht h3)
  refine ⟨C, κ, hκ, fun N hN K N'' β => ?_⟩
  calc _ ≤ ∑ _d ∈ Finset.range N'',
        (3 * N * (2 / 3 : ℝ) ^ K + 4 * N * (1 / 3 : ℝ) ^ K + C * 9 ^ K * (N : ℝ) ^ (1 - κ)) :=
        Finset.sum_le_sum fun d _ => hC N hN K (β d)
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem hf_true_int_mul (W : ℕ) (h : ℤ) (x : ℝ) :
    Hf (fun _ => true) 0 W ((h : ℝ) * x) = Hf (fun _ => true) 0 W ((h.natAbs : ℝ) * x) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg h
  · simp
  · rw [Int.natAbs_neg, Int.natAbs_natCast]; push_cast
    rw [neg_mul, CantorExactExponentProfile.hf_neg]

/-- **Class-3 sum.**  For `h` prime to 3, `Σ_{m<N} Σ_{n<N} Hf_true(h tⁿ) ≤ N(N + 2·3ʲ)(3/2)^{tb}(2/3)ʲ`. -/
theorem sum_class_sep_le {t : ℕ} (ht : 2 ≤ t) (h3 : ¬ 3 ∣ t) (h : ℤ) (hh : ¬ (3 : ℤ) ∣ h)
    (j N : ℕ) :
    ∑ _m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      Hf (fun _ => true) 0 (j + 1) ((h : ℝ) * (t : ℝ) ^ n) ≤
      N * ((N + 2 * 3 ^ j) * (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t * (2 / 3 : ℝ) ^ j) := by
  have hc : ¬ 3 ∣ h.natAbs := by
    intro hd; exact hh (Int.natAbs_dvd_natAbs.1 (by simpa using hd))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  gcongr
  refine le_of_eq_of_le ?_ (CantorExactExponentProfile.sum_hf_true_le ht h3 j h.natAbs hc N)
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hf_true_int_mul]; push_cast; rfl

/-- **Class-5 sum.**  Under `TOrbitCyclicDecay t` and `BadGcdSparseH b`: pairs whose window lies in
copy run `k` (`a = a_k ≤ s·min(n,m)`, `|ξ| ≤ B`, below `N'` with `a ≤ N' ≤ a³`) sum to
`≤ C N'^{2−δ} + |P| π B / 3^{(k+2)a}`. -/
theorem sum_class_copy_le {s t : ℕ} (hT : TOrbitCyclicDecay t) (hS : BadGcdSparseH (3 ^ s * t))
    (h : ℤ) (hh : h ≠ 0) : ∃ C δ : ℝ, 0 < δ ∧ ∀ (M k : ℕ), Even k → 1 ≤ runStart k →
      ∀ (P : Finset (ℕ × ℕ)) (N' : ℕ) (B : ℝ), runStart k ≤ N' → N' ≤ runStart k ^ 3 →
      (∀ p ∈ P, p.1 < N' ∧ p.2 < N' ∧ runStart k ≤ s * min p.1 p.2 ∧
        |h * (((3 ^ s * t : ℕ) : ℝ) ^ p.1 - ((3 ^ s * t : ℕ) : ℝ) ^ p.2)| ≤ B) →
      ∑ p ∈ P, repBound M (some k) (h * (((3 ^ s * t : ℕ) : ℝ) ^ p.1 - ((3 ^ s * t : ℕ) : ℝ) ^ p.2))
        ≤ C * (N' : ℝ) ^ (2 - δ) + P.card * (Real.pi * B / 3 ^ ((k + 2) * runStart k)) := by
  obtain ⟨C, δ, hδ, hC⟩ := copyZoneDecayH_of hT hS h hh
  refine ⟨C, δ, hδ, fun M k hk ha P N' B h1 h2 hP => ?_⟩
  refine (copyRun_sum_le M k s t hk h P N' B hP).trans ?_
  have := hC (runStart k) N' ha h1 h2
  push_cast at this ⊢
  linarith

/-- **Run range fits the copy-zone range.**  `N' = (k+2)a_k + 1` satisfies `a_k ≤ N' ≤ a_k³`, so
the class-5/6 sums over run `k` (all `n` with `sn < (k+2)a_k`) meet the range hypothesis of
`TOrbitCyclicDecay`/`CopyZoneDecayH`. -/
theorem runEnd_succ_le_cube (k : ℕ) :
    runStart k ≤ (k + 2) * runStart k + 1 ∧ (k + 2) * runStart k + 1 ≤ runStart k ^ 3 := by
  have hk : k + 3 ≤ 4 ^ (k + 1) := by
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; omega
  have h4 := four_pow_le_runStart k
  refine ⟨by nlinarith, ?_⟩
  have ha : k + 3 ≤ runStart k := hk.trans h4
  have : 1 ≤ runStart k := by omega
  calc (k + 2) * runStart k + 1 ≤ runStart k * runStart k := by nlinarith
    _ = runStart k ^ 2 := by ring
    _ ≤ runStart k ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)

/-! ## Bases `3ˢt`, `t > 1`: the crux -/

/-- **Choosing the options.**  If every pair has some option bounded by `F n m`, a single choice
`κ` bounds the pair sum by `Σ F`.  With `F` a sum of nonnegative per-class majorants (each pair
bounded by the majorant of its class from `pair_classify_rep`, band pairs by `1`), the assembly's
pair sum is at most the sum of the class sums. -/
theorem exists_kappa_sum_le (M : ℕ) (ξ : ℕ → ℕ → ℝ) (F : ℕ → ℕ → ℝ)
    (hF : ∀ n m, ∃ o, repBound M o (ξ n m) ≤ F n m) (N : ℕ) :
    ∃ κ : ℕ → ℕ → Option ℕ, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      repBound M (κ n m) (ξ n m) ≤ ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, F n m := by
  choose κ hκ using hF
  exact ⟨κ, Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => hκ n m⟩

/-- `repBound` never exceeds `1`, so band / diagonal / small-index pairs cost at most `1`. -/
theorem repBound_le_one (M : ℕ) (o : Option ℕ) (ξ : ℝ) : repBound M o ξ ≤ 1 := by
  cases o <;> simp only [repBound]
  · exact Bf_le_one _ _ _
  · split_ifs
    · exact Finset.prod_le_one (fun _ _ => abs_nonneg _) fun _ _ => Real.abs_cos_le_one _
    · exact le_rfl

/-! ### Concrete per-pair bounds (`ξ = 3ᵉh'(b^{m+d} − bᵐ)`) -/
/-- Concrete pair frequency `ξ = 3ᵉh'(b^{m+d} − bᵐ)`, `b = 3ˢt`, as a natural number. -/
def pairNat (s t e h' m d : ℕ) : ℕ := 3 ^ e * h' * ((3 ^ s * t) ^ (m + d) - (3 ^ s * t) ^ m)

theorem pairNat_eq (s t e h' m d : ℕ) :
    (pairNat s t e h' m d : ℝ) =
      3 ^ (s * m + e) * ((h' * ((3 ^ s * t) ^ d - 1) * t ^ m : ℕ) : ℝ) := by
  unfold pairNat
  have h1 : 1 ≤ (3 ^ s * t) ^ d ∨ (3 ^ s * t) ^ d = 0 := by
    rcases Nat.eq_zero_or_pos ((3 ^ s * t) ^ d) with h | h
    · exact Or.inr h
    · exact Or.inl h
  have e1 : (3 ^ s * t) ^ (m + d) - (3 ^ s * t) ^ m = (3 ^ s * t) ^ m * ((3 ^ s * t) ^ d - 1) := by
    rw [pow_add, Nat.mul_sub_one]
  rw [e1]
  push_cast
  rw [pow_add, pow_mul]
  ring

/-- **Class 1, concrete.**  Fresh `[v+1, v+W)`, `v = sm + e`: the pair term is at most the
all-free majorant at `h'(bᵈ − 1)tᵐ`. -/
theorem pair_class1 {s t e h' m d M W : ℕ} (hM : s * m + e + W ≤ M)
    (hfr : ∀ p, s * m + e + 1 ≤ p → p < s * m + e + W → isFresh p = true) :
    repBound M none (pairNat s t e h' m d) ≤
      Hf (fun _ => true) 0 W ((h' * ((3 ^ s * t) ^ d - 1) * t ^ m : ℕ) : ℝ) := by
  simp only [repBound]
  rw [pairNat_eq, ← add_zero (3 ^ (s * m + e) * _)]
  have := bf_le_hf_true_add isFresh hM hfr ((h' * ((3 ^ s * t) ^ d - 1) * t ^ m : ℕ) : ℝ) 0 0
    (by simp)
  simpa using this

theorem pairNat_eq_sub {s t : ℕ} (ht : 1 ≤ t) (e h' m d : ℕ) :
    (pairNat s t e h' m d : ℝ) = 3 ^ (s * (m + d) + e) * ((h' * t ^ (m + d) : ℕ) : ℝ) +
      -((3 ^ e * h' * (3 ^ s * t) ^ m : ℕ) : ℝ) := by
  unfold pairNat
  have hle : (3 ^ s * t) ^ m ≤ (3 ^ s * t) ^ (m + d) := by
    exact Nat.pow_le_pow_right (by positivity) (by omega)
  rw [Nat.mul_sub, Nat.cast_sub (Nat.mul_le_mul_left _ hle)]
  push_cast
  rw [pow_add 3, mul_pow, ← pow_mul]
  ring

/-- **Class 3, concrete.**  Separated (`y + K ≤ u`, `y` the top of `Y = 3ᵉh'bᵐ`, `u = sn + e`),
fresh `[u+1, u+W)`: the pair term is at most `Hf_true(h' tⁿ) + 3π/3^K`. -/
theorem pair_class3 {s t e h' m d M W K : ℕ} (ht : 1 ≤ t) (hM : s * (m + d) + e + W ≤ M)
    (hfr : ∀ p, s * (m + d) + e + 1 ≤ p → p < s * (m + d) + e + W → isFresh p = true)
    (hsep : Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) + K ≤ s * (m + d) + e) :
    repBound M none (pairNat s t e h' m d) ≤
      Hf (fun _ => true) 0 W ((h' * t ^ (m + d) : ℕ) : ℝ) + Real.pi * (3 / 3 ^ K) := by
  simp only [repBound]
  rw [pairNat_eq_sub ht]
  refine bf_le_hf_true_add isFresh hM hfr _ _ _ ?_
  rw [abs_neg, Nat.abs_cast]
  set Y := 3 ^ e * h' * (3 ^ s * t) ^ m
  have hY : Y < 3 ^ (Nat.log 3 Y + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hY' : (Y : ℝ) ≤ 3 ^ (Nat.log 3 Y + 1) := by exact_mod_cast hY.le
  refine hY'.trans (le_of_eq_of_le (by ring) (?_ : (3 : ℝ) ^ (Nat.log 3 Y + 1) ≤ _))
  rw [show s * (m + d) + e = (s * (m + d) + e - K) + K by omega, pow_add]
  field_simp
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem pairNat_eq_mul (s t e h' m d : ℕ) :
    (pairNat s t e h' m d : ℝ) = ((3 ^ e * h' * ((3 ^ s * t) ^ d - 1) : ℕ) : ℝ) *
      ((3 ^ s * t : ℕ) : ℝ) ^ m := by
  unfold pairNat
  have e1 : (3 ^ s * t) ^ (m + d) - (3 ^ s * t) ^ m = (3 ^ s * t) ^ m * ((3 ^ s * t) ^ d - 1) := by
    rw [pow_add, Nat.mul_sub_one]
  rw [e1]; push_cast; ring

/-- **Class 4, concrete (top window of `ξ`).**  `T = log₃ ξ` (natural), `W` fresh places below
it: the pair term is at most `topProd W {m log₃ t + log₃(3ᵉh'(bᵈ−1))}`. -/
theorem pair_class4 {s t e h' m d M W : ℕ} (ht : 1 ≤ t) (h1 : 1 ≤ pairNat s t e h' m d)
    (hW : W ≤ Nat.log 3 (pairNat s t e h' m d))
    (hfr : ∀ k < W, isFresh (Nat.log 3 (pairNat s t e h' m d) - 1 - k) = true)
    (hM : Nat.log 3 (pairNat s t e h' m d) ≤ M) :
    repBound M none (pairNat s t e h' m d) ≤
      CantorExactExponentProfile.topProd W (Int.fract (m * Real.logb 3 t +
        Real.logb 3 ((3 ^ e * h' * ((3 ^ s * t) ^ d - 1) : ℕ) : ℝ))) := by
  simp only [repBound]
  have hT : ⌊Real.logb 3 |((pairNat s t e h' m d : ℕ) : ℝ)|⌋₊ = Nat.log 3 (pairNat s t e h' m d) := by
    rw [Nat.abs_cast]; exact_mod_cast Real.natFloor_logb_natCast 3 _
  have h1' : (1 : ℝ) ≤ |((pairNat s t e h' m d : ℕ) : ℝ)| := by
    rw [Nat.abs_cast]; exact_mod_cast h1
  refine (CantorExactExponentProfile.bf_le_topProd isFresh M W _ h1' (hT ▸ hW)
    (hT ▸ hfr) (hT ▸ hM)).trans (le_of_eq ?_)
  have hc : ((3 ^ e * h' * ((3 ^ s * t) ^ d - 1) : ℕ) : ℝ) ≠ 0 := by
    intro h0
    have := pairNat_eq_mul s t e h' m d
    rw [h0, zero_mul] at this
    have : (1 : ℝ) ≤ 0 := by rw [← this]; exact_mod_cast h1
    norm_num at this
  rw [pairNat_eq_mul, fract_logb_mul_pow ht _ hc, Nat.abs_cast]

/-- **Class 2, concrete (top window of `Y = 3ᵉh'bᵐ`).**  If `y = log₃ Y ≤ s(m+d) + e` and the `W`
places below `y` are fresh, the pair term is at most `topProd W {m log₃ t + log₃(3ᵉh')}`. -/
theorem pair_class2 {s t e h' m d M W : ℕ} (ht : 1 ≤ t) (hY1 : 1 ≤ 3 ^ e * h' * (3 ^ s * t) ^ m)
    (hW : W ≤ Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m))
    (hfr : ∀ k < W, isFresh (Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) - 1 - k) = true)
    (hM : Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) ≤ M)
    (hyu : Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) ≤ s * (m + d) + e) :
    repBound M none (pairNat s t e h' m d) ≤
      CantorExactExponentProfile.topProd W (Int.fract (m * Real.logb 3 t +
        Real.logb 3 ((3 ^ e * h' : ℕ) : ℝ))) := by
  simp only [repBound]
  set Y : ℕ := 3 ^ e * h' * (3 ^ s * t) ^ m with hYdef
  have hT : ⌊Real.logb 3 |((Y : ℤ) : ℝ)|⌋₊ = Nat.log 3 Y := by
    push_cast; rw [Nat.abs_cast]; exact_mod_cast Real.natFloor_logb_natCast 3 _
  have h1' : (1 : ℝ) ≤ |((Y : ℤ) : ℝ)| := by push_cast; rw [Nat.abs_cast]; exact_mod_cast hY1
  have hle : (3 ^ s * t) ^ m ≤ (3 ^ s * t) ^ (m + d) := Nat.pow_le_pow_right (by positivity) (by omega)
  have hdvd : (3 : ℤ) ^ ⌊Real.logb 3 |((Y : ℤ) : ℝ)|⌋₊ ∣ ((pairNat s t e h' m d : ℕ) : ℤ) + (Y : ℤ) := by
    rw [hT]
    have : ((pairNat s t e h' m d : ℕ) : ℤ) + (Y : ℤ) = ((3 ^ e * h' * (3 ^ s * t) ^ (m + d) : ℕ) : ℤ) := by
      unfold pairNat; rw [hYdef, ← Nat.cast_add, Nat.mul_sub, Nat.sub_add_cancel
        (Nat.mul_le_mul_left _ hle)]
    rw [this]
    refine Int.natCast_dvd_natCast.2 ?_ |> (by push_cast; exact ·)
    refine (Nat.pow_dvd_pow 3 hyu).trans ?_
    exact ⟨h' * t ^ (m + d), by rw [mul_pow, ← pow_mul, pow_add]; ring⟩
  have := CantorExactExponentProfile.bf_le_topProd_of_dvd isFresh M W
    ((pairNat s t e h' m d : ℕ) : ℤ) (Y : ℤ) h1' (hT ▸ hW) (hT ▸ hfr) (hT ▸ hM) hdvd
  push_cast at this
  refine this.trans (le_of_eq ?_)
  have hc : ((3 ^ e * h' : ℕ) : ℝ) ≠ 0 := by
    intro h0; push_cast at h0
    have : ((Y : ℕ) : ℝ) = 0 := by rw [hYdef]; push_cast; rw [h0, zero_mul]
    have h2 : (1 : ℝ) ≤ Y := by exact_mod_cast hY1
    linarith
  have := fract_logb_mul_pow (s := s) ht ((3 ^ e * h' : ℕ) : ℝ) hc m
  push_cast at this ⊢
  rw [show ((Y : ℕ) : ℝ) = 3 ^ e * (h' : ℝ) * (3 ^ s * (t : ℝ)) ^ m by rw [hYdef]; push_cast; ring,
    this, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 ^ e * (h' : ℝ))]

theorem pairNat_lt (s t e h' m d : ℕ) :
    (pairNat s t e h' m d : ℝ) < 3 ^ (Nat.log 3 (pairNat s t e h' m d) + 1) := by
  exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) _

/-- **Class 5, concrete (window of `ξ` inside copy run `k`).**  `a = a_k ≤ sm + e` and
`T + K < (k+2)a`: the pair term is at most `cycProd a (h'(bⁿ − bᵐ)) + π/3^K`. -/
theorem pair_class5 {s t e h' m d M k K : ℕ} (ht : 1 ≤ t) (hk : Even k)
    (ha : runStart k ≤ s * m + e)
    (hT : Nat.log 3 (pairNat s t e h' m d) + K < (k + 2) * runStart k) :
    repBound M (some k) (pairNat s t e h' m d) ≤
      cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℤ) ^ m))
        + Real.pi * (1 / 3 ^ K) := by
  set a := runStart k
  have hB : 1 ≤ (3 ^ s * t) ^ d := Nat.one_le_pow _ _ (by positivity)
  set η : ℤ := (t : ℤ) ^ m * ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1))
  have := repBound_some_le_cyc M k hk (pairNat s t e h' m d) (3 ^ (s * m + e - a) * η)
  rw [cycProd_mul_three_pow, ← cycProd_pairH] at this
  refine this.trans ?_
  have e0 : (pairNat s t e h' m d : ℝ) - 3 ^ a * (((3 ^ (s * m + e - a) * η : ℤ)) : ℝ) = 0 := by
    rw [pairNat_eq]
    simp only [η]
    push_cast [Nat.cast_sub hB]
    rw [show (3 : ℝ) ^ (s * m + e) = 3 ^ a * 3 ^ (s * m + e - a) by
      rw [← pow_add]; congr 1; omega]
    ring
  rw [e0, abs_zero, zero_div, zero_add]
  have key : |(pairNat s t e h' m d : ℝ)| / 3 ^ ((k + 2) * a) ≤ 1 / 3 ^ K := by
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    refine (mul_le_mul_of_nonneg_right (pairNat_lt s t e h' m d).le (by positivity)).trans ?_
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have := Real.pi_pos
  nlinarith

/-- **Class 6, concrete (separated, high part in copy run `k`).**  `a = a_k ≤ s(m+d) + e`,
`T + K < (k+2)a`, `y + K ≤ a` (`y` the top of `Y = 3ᵉh'bᵐ`): the pair term is at most
`cycProd a (h' t^{m+d}) + 4π/3^K`. -/
theorem pair_class6 {s t e h' m d M k K : ℕ} (ht : 1 ≤ t) (hk : Even k)
    (ha : runStart k ≤ s * (m + d) + e)
    (hT : Nat.log 3 (pairNat s t e h' m d) + K < (k + 2) * runStart k)
    (hy : Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) + K ≤ runStart k) :
    repBound M (some k) (pairNat s t e h' m d) ≤
      cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ (m + d)) + Real.pi * (4 / 3 ^ K) := by
  set a := runStart k
  have := repBound_some_le_cyc M k hk (pairNat s t e h' m d)
    (3 ^ (s * (m + d) + e - a) * ((h' : ℤ) * (t : ℤ) ^ (m + d)))
  rw [cycProd_mul_three_pow] at this
  refine this.trans ?_
  set Y := 3 ^ e * h' * (3 ^ s * t) ^ m
  have e0 : (pairNat s t e h' m d : ℝ) -
      3 ^ a * (((3 ^ (s * (m + d) + e - a) * ((h' : ℤ) * (t : ℤ) ^ (m + d)) : ℤ)) : ℝ) =
      -((Y : ℕ) : ℝ) := by
    rw [pairNat_eq_sub ht]
    push_cast
    rw [show (3 : ℝ) ^ (s * (m + d) + e) = 3 ^ a * 3 ^ (s * (m + d) + e - a) by
      rw [← pow_add]; congr 1; omega]
    simp only [Y]; push_cast; rw [mul_pow, ← pow_mul]; ring
  rw [e0, abs_neg, Nat.abs_cast]
  have k1 : ((Y : ℕ) : ℝ) / 3 ^ a ≤ 3 / 3 ^ K := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hY : (Y : ℝ) < 3 ^ (Nat.log 3 Y + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) _
    refine (mul_le_mul_of_nonneg_right hY.le (by positivity)).trans ?_
    have : (3 : ℝ) ^ (Nat.log 3 Y + K) ≤ 3 ^ a := pow_le_pow_right₀ (by norm_num) hy
    rw [pow_add] at this
    rw [pow_succ]
    nlinarith
  have k2 : |(pairNat s t e h' m d : ℝ)| / 3 ^ ((k + 2) * a) ≤ 1 / 3 ^ K := by
    rw [abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    refine (mul_le_mul_of_nonneg_right (pairNat_lt s t e h' m d).le (by positivity)).trans ?_
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have := Real.pi_pos
  have : (3 : ℝ) / 3 ^ K + 1 / 3 ^ K = 4 / 3 ^ K := by ring
  nlinarith

theorem lt_runStart (k : ℕ) : k < runStart k := by
  have h := four_pow_le_runStart k
  have : k < 4 ^ (k + 1) := by
    calc k < k + 1 := Nat.lt_succ_self k
      _ < 4 ^ (k + 1) := Nat.lt_pow_self (by norm_num)
  omega

/-- The runs whose copy coins can bound the pair `(m, d)`: `a_k ≤ u` and `T < (k+2)a_k`. -/
noncomputable def copyRuns (s t e h' m d M : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter fun k =>
    runStart k ≤ s * (m + d) + e ∧ Nat.log 3 (pairNat s t e h' m d) < (k + 2) * runStart k

/-- **The per-pair majorant.**  Sum of the six class majorants (`pair_class1`–`pair_class6`),
the copy terms summed over runs `k ≤ M`. -/
noncomputable def pairMaj (s t e h' m d M W K : ℕ) : ℝ :=
  Hf (fun _ => true) 0 W ((h' * ((3 ^ s * t) ^ d - 1) * t ^ m : ℕ) : ℝ) +
  CantorExactExponentProfile.topProd W (Int.fract (m * Real.logb 3 t +
    Real.logb 3 ((3 ^ e * h' : ℕ) : ℝ))) +
  Hf (fun _ => true) 0 W ((h' * t ^ (m + d) : ℕ) : ℝ) +
  CantorExactExponentProfile.topProd W (Int.fract (m * Real.logb 3 t +
    Real.logb 3 ((3 ^ e * h' * ((3 ^ s * t) ^ d - 1) : ℕ) : ℝ))) +
  ∑ k ∈ copyRuns s t e h' m d M,
    (cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℤ) ^ m))
      + cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ (m + d))) +
  Real.pi * (8 / 3 ^ K)

theorem topProd_nonneg' (K : ℕ) (y : ℝ) : 0 ≤ CantorExactExponentProfile.topProd K y :=
  Finset.prod_nonneg fun _ _ => abs_nonneg _

theorem pairMaj_ge {s t e h' m d M W K : ℕ} :
    (Hf (fun _ => true) 0 W ((h' * ((3 ^ s * t) ^ d - 1) * t ^ m : ℕ) : ℝ) ≤ pairMaj s t e h' m d M W K) ∧
    (CantorExactExponentProfile.topProd W (Int.fract (m * Real.logb 3 t +
      Real.logb 3 ((3 ^ e * h' : ℕ) : ℝ))) ≤ pairMaj s t e h' m d M W K) ∧
    (Hf (fun _ => true) 0 W ((h' * t ^ (m + d) : ℕ) : ℝ) + Real.pi * (3 / 3 ^ K) ≤
      pairMaj s t e h' m d M W K) ∧
    (CantorExactExponentProfile.topProd W (Int.fract (m * Real.logb 3 t +
      Real.logb 3 ((3 ^ e * h' * ((3 ^ s * t) ^ d - 1) : ℕ) : ℝ))) ≤ pairMaj s t e h' m d M W K) ∧
    (∀ k ≤ M, runStart k ≤ s * (m + d) + e →
      Nat.log 3 (pairNat s t e h' m d) < (k + 2) * runStart k →
      cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ (m + d) -
      ((3 ^ s * t : ℕ) : ℤ) ^ m)) + Real.pi * (1 / 3 ^ K) ≤ pairMaj s t e h' m d M W K) ∧
    (∀ k ≤ M, runStart k ≤ s * (m + d) + e →
      Nat.log 3 (pairNat s t e h' m d) < (k + 2) * runStart k →
      cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ (m + d)) + Real.pi * (4 / 3 ^ K) ≤
      pairMaj s t e h' m d M W K) := by
  have h1 := Hf_nonneg (fun _ => true) 0 W ((h' * ((3 ^ s * t) ^ d - 1) * t ^ m : ℕ) : ℝ)
  have h3 := Hf_nonneg (fun _ => true) 0 W ((h' * t ^ (m + d) : ℕ) : ℝ)
  have h2 := topProd_nonneg' W (Int.fract (m * Real.logb 3 t + Real.logb 3 ((3 ^ e * h' : ℕ) : ℝ)))
  have h4 := topProd_nonneg' W (Int.fract (m * Real.logb 3 t +
      Real.logb 3 ((3 ^ e * h' * ((3 ^ s * t) ^ d - 1) : ℕ) : ℝ)))
  set S := ∑ k ∈ copyRuns s t e h' m d M,
    (cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℤ) ^ m))
      + cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ (m + d))) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => add_nonneg (cycProd_nonneg _ _) (cycProd_nonneg _ _)
  have hk : ∀ k ≤ M, runStart k ≤ s * (m + d) + e →
      Nat.log 3 (pairNat s t e h' m d) < (k + 2) * runStart k → cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ (m + d) -
      ((3 ^ s * t : ℕ) : ℤ) ^ m)) + cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ (m + d)) ≤ S :=
    fun k hk ha hT => Finset.single_le_sum (f := fun k => cycProd (runStart k) ((h' : ℤ) *
      (((3 ^ s * t : ℕ) : ℤ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℤ) ^ m)) + cycProd (runStart k)
        ((h' : ℤ) * (t : ℤ) ^ (m + d)))
      (fun k _ => add_nonneg (cycProd_nonneg _ _) (cycProd_nonneg _ _))
      (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ha, hT⟩)
  have hp : 0 ≤ Real.pi * (1 / 3 ^ K) := by positivity
  have e8 : Real.pi * (8 / 3 ^ K) = 8 * (Real.pi * (1 / 3 ^ K)) := by ring
  have e3 : Real.pi * (3 / 3 ^ K) = 3 * (Real.pi * (1 / 3 ^ K)) := by ring
  have e4 : Real.pi * (4 / 3 ^ K) = 4 * (Real.pi * (1 / 3 ^ K)) := by ring
  unfold pairMaj
  rw [← hS]
  refine ⟨by linarith, by linarith, by linarith, by linarith, fun k hkM ha hT => ?_, fun k hkM ha hT => ?_⟩
  · have := hk k hkM ha hT; have := cycProd_nonneg (runStart k) ((h' : ℤ) * (t : ℤ) ^ (m + d)); linarith
  · have := hk k hkM ha hT
    have := cycProd_nonneg (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ (m + d) -
      ((3 ^ s * t : ℕ) : ℤ) ^ m)); linarith


/-- **Combine.**  If the pair `(m, d)` (positions `v = sm+e`, `y = log₃ Y`, `u = s(m+d)+e`,
`T = log₃ ξ`) falls into one of the six classes of `pair_classify_rep`, some option bounds its
term by `pairMaj`.  `M` must dominate every position. -/
theorem exists_option_le_pairMaj {s t e h' m d M W K : ℕ} (ht : 1 ≤ t) (hh : 1 ≤ h')
    (hd : 1 ≤ d) (hs : 1 ≤ s) (hMu : s * (m + d) + e + W ≤ M)
    (hMT : Nat.log 3 (pairNat s t e h' m d) ≤ M)
    (hcls : (∀ p, s * m + e + 1 ≤ p → p < s * m + e + W → isFresh p = true) ∨
      (W ≤ Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) ∧
        Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) ≤ s * (m + d) + e ∧
        ∀ j < W, isFresh (Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) - 1 - j) = true) ∨
      (Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) + K ≤ s * (m + d) + e ∧
        ∀ p, s * (m + d) + e + 1 ≤ p → p < s * (m + d) + e + W → isFresh p = true) ∨
      (W ≤ Nat.log 3 (pairNat s t e h' m d) ∧
        ∀ j < W, isFresh (Nat.log 3 (pairNat s t e h' m d) - 1 - j) = true) ∨
      (∃ k, Even k ∧ runStart k ≤ s * m + e ∧
        Nat.log 3 (pairNat s t e h' m d) + K < (k + 2) * runStart k) ∨
      (∃ k, Even k ∧ runStart k ≤ s * (m + d) + e ∧
        Nat.log 3 (pairNat s t e h' m d) + K < (k + 2) * runStart k ∧
        Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) + K ≤ runStart k)) :
    ∃ o, repBound M o (pairNat s t e h' m d) ≤ pairMaj s t e h' m d M W K := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := pairMaj_ge (s := s) (t := t) (e := e) (h' := h') (m := m)
    (d := d) (M := M) (W := W) (K := K)
  have hY1 : 1 ≤ 3 ^ e * h' * (3 ^ s * t) ^ m :=
    Nat.mul_pos (Nat.mul_pos (by positivity) hh) (by positivity)
  have hYle : Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) ≤ s * m + e + Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) := by omega
  have hsm : s * m ≤ s * (m + d) := Nat.mul_le_mul_left _ (by omega)
  rcases hcls with c | c | c | c | c | c
  · exact ⟨none, (pair_class1 (by omega) c).trans g1⟩
  · obtain ⟨c1, c2, c3⟩ := c
    exact ⟨none, (pair_class2 ht hY1 c1 c3 (by omega) c2).trans g2⟩
  · obtain ⟨c1, c2⟩ := c
    exact ⟨none, (pair_class3 ht hMu c2 c1).trans g3⟩
  · obtain ⟨c1, c2⟩ := c
    have hp : 1 ≤ pairNat s t e h' m d := by
      have h0 := pairNat_eq_mul s t e h' m d
      have hB : 2 ≤ (3 ^ s * t) ^ d := by
        calc 2 ≤ 3 ^ s * t := by
              have : 3 ≤ 3 ^ s := by
                calc 3 = 3 ^ 1 := by norm_num
                  _ ≤ 3 ^ s := Nat.pow_le_pow_right (by norm_num) hs
              nlinarith
          _ ≤ (3 ^ s * t) ^ d := by
              calc 3 ^ s * t = (3 ^ s * t) ^ 1 := (pow_one _).symm
                _ ≤ _ := Nat.pow_le_pow_right (by positivity) hd
      have : 1 ≤ 3 ^ e * h' * ((3 ^ s * t) ^ d - 1) :=
        Nat.mul_pos (Nat.mul_pos (by positivity) hh) (by omega)
      have h2 : (1 : ℝ) ≤ ((3 ^ e * h' * ((3 ^ s * t) ^ d - 1) : ℕ) : ℝ) *
          ((3 ^ s * t : ℕ) : ℝ) ^ m := by
        have a1 : (1 : ℝ) ≤ ((3 ^ e * h' * ((3 ^ s * t) ^ d - 1) : ℕ) : ℝ) := by exact_mod_cast this
        have a2 : (1 : ℝ) ≤ ((3 ^ s * t : ℕ) : ℝ) ^ m := one_le_pow₀ (by
          have : 1 ≤ 3 ^ s * t := Nat.mul_pos (by positivity) ht
          exact_mod_cast this)
        nlinarith
      rw [← h0] at h2; exact_mod_cast h2
    exact ⟨none, (pair_class4 ht hp c1 c2 hMT).trans g4⟩
  · obtain ⟨k, hk, c1, c2⟩ := c
    have : k ≤ M := by have := lt_runStart k; omega
    exact ⟨some k, (pair_class5 ht hk c1 c2).trans (g5 k this (by omega) (by omega))⟩
  · obtain ⟨k, hk, c1, c2, c3⟩ := c
    have : k ≤ M := by have := lt_runStart k; omega
    exact ⟨some k, (pair_class6 ht hk c1 c2 c3).trans (g6 k this c1 (by omega))⟩

/-- **The six-way disjunction at concrete positions.**  `pair_classify_rep` with `ρ' = ρ(ρ+1)`,
from `b ≤ 3^{s(ρ−1)}`, `3ᵉh' < 3^{sm}` (i.e. `m` large), past run `k₀`, away from the bands. -/
theorem pair_classes {s t e h' m d ρ k₀ W K : ℕ} (ht : 2 ≤ t) (hh : 1 ≤ h')
    (hd : 1 ≤ d) (hρ1 : 1 ≤ ρ) (hb : 3 ^ s * t ≤ 3 ^ (s * (ρ - 1)))
    (hH : 3 ^ e * h' < 3 ^ (s * m)) (hρ : ρ * (ρ + 1) ≤ 4 * (k₀ + 3))
    (hv0 : runStart k₀ ≤ s * m + e) (hW : W ≤ s * m + e) (hK : K ≤ s * m + e)
    (hnv : ¬ NearCopyBdry W K (s * m + e))
    (hny : ¬ NearCopyBdry W K (Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m)))
    (hnu : ¬ NearCopyBdry W K (s * (m + d) + e))
    (hnT : ¬ NearCopyBdry W K (Nat.log 3 (pairNat s t e h' m d))) :
    (∀ p, s * m + e + 1 ≤ p → p < s * m + e + W → isFresh p = true) ∨
      (W ≤ Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) ∧
        Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) ≤ s * (m + d) + e ∧
        ∀ j < W, isFresh (Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) - 1 - j) = true) ∨
      (Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) + K ≤ s * (m + d) + e ∧
        ∀ p, s * (m + d) + e + 1 ≤ p → p < s * (m + d) + e + W → isFresh p = true) ∨
      (W ≤ Nat.log 3 (pairNat s t e h' m d) ∧
        ∀ j < W, isFresh (Nat.log 3 (pairNat s t e h' m d) - 1 - j) = true) ∨
      (∃ k, Even k ∧ runStart k ≤ s * m + e ∧
        Nat.log 3 (pairNat s t e h' m d) + K < (k + 2) * runStart k) ∨
      (∃ k, Even k ∧ runStart k ≤ s * (m + d) + e ∧
        Nat.log 3 (pairNat s t e h' m d) + K < (k + 2) * runStart k ∧
        Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) + K ≤ runStart k) := by
  set B := 3 ^ s * t
  set v := s * m + e
  set u := s * (m + d) + e
  set y := Nat.log 3 (3 ^ e * h' * B ^ m)
  set T := Nat.log 3 (pairNat s t e h' m d)
  have hsm : s * m ≤ s * (m + d) := Nat.mul_le_mul_left _ (by omega)
  have hsm0 : 0 < s * m := by
    rcases Nat.eq_zero_or_pos (s * m) with h0 | h0
    · rw [h0, pow_zero] at hH; have : 1 ≤ 3 ^ e * h' := Nat.mul_pos (by positivity) hh; omega
    · exact h0
  have hBpos : 1 ≤ B := Nat.mul_pos (by positivity) (by omega)
  -- v ≤ y
  have hvy : v ≤ y := by
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    calc 3 ^ v = 3 ^ e * 1 * (3 ^ s) ^ m := by simp only [v]; rw [pow_add, ← pow_mul]; ring
      _ ≤ 3 ^ e * h' * B ^ m := Nat.mul_le_mul (Nat.mul_le_mul_left _ hh)
          (Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by omega)) m)
  -- y < ρ v
  have hyρ : y ≤ ρ * v := by
    have := log_mul_pow_lt hρ1 hb hH hsm0
    have : ρ * (s * m) ≤ ρ * v := Nat.mul_le_mul_left _ (by omega)
    omega
  -- u ≤ T
  have huT : u ≤ T := by
    refine Nat.le_log_of_pow_le (by norm_num) ?_
    have h1 := three_pow_le_pow_sub_pow (s := s) (m := m) ht hd
    calc 3 ^ u = 3 ^ e * 1 * 3 ^ (s * (m + d)) := by simp only [u]; rw [pow_add]; ring
      _ ≤ 3 ^ e * h' * ((3 ^ s * t) ^ (m + d) - (3 ^ s * t) ^ m) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hh) h1
  -- T ≤ ρ u
  have hTρ : T ≤ ρ * u := by
    have h1 : T ≤ Nat.log 3 (3 ^ e * h' * B ^ (m + d)) := Nat.log_mono_right
      (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have hH' : 3 ^ e * h' < 3 ^ (s * (m + d)) := lt_of_lt_of_le hH (Nat.pow_le_pow_right (by norm_num) hsm)
    have h2 := log_mul_pow_lt (m := m + d) hρ1 hb hH' (by omega)
    have : ρ * (s * (m + d)) ≤ ρ * u := Nat.mul_le_mul_left _ (by omega)
    omega
  have hsep := hsep_of (K := K) hTρ hyρ hK
  have hρρ : ρ ≤ ρ * (ρ + 1) := Nat.le_mul_of_pos_right _ (by omega)
  refine pair_classify_rep (ρ := ρ * (ρ + 1)) hρ hv0 hW hvy (hyρ.trans (Nat.mul_le_mul_right _ hρρ))
    (by omega) huT (hTρ.trans (Nat.mul_le_mul_right _ hρρ))
    (fun h => (hsep h).trans (le_of_eq (by ring))) hnv hny hnu hnT

theorem card_injOn_window_le (f : ℕ → ℕ) (A L : ℕ) (S : Finset ℕ) (hf : Set.InjOn f S)
    (hS : ∀ n ∈ S, A ≤ f n + L ∧ f n ≤ A) : S.card ≤ L + 1 := by
  have : S.card ≤ (Finset.Icc (A - L) A).card := by
    refine Finset.card_le_card_of_injOn f (fun n hn => ?_) hf
    have := hS n hn; simp only [Finset.coe_Icc, Set.mem_Icc]; omega
  simp at this; omega

open Classical in
/-- **Band count, general positions.**  For `f` injective on `range N` with `f n ≤ X`, at most
`2(W+2K+1)(log₄(X+W+K)+1)` of the `n < N` put `f n` in a copy-run boundary band.  Used with
`f m = log₃(3ᵉh'bᵐ)` (top of `Y`) and, for fixed `m`, `f d = log₃ ξ(m, d)` (top of `ξ`). -/
theorem card_nearCopyBdry_le_of (f : ℕ → ℕ) (W K N X : ℕ)
    (hf : Set.InjOn f (Finset.range N)) (hX : ∀ n < N, f n ≤ X) :
    ((Finset.range N).filter fun n => NearCopyBdry W K (f n)).card ≤
      2 * (W + 2 * K + 1) * (Nat.log 4 (X + W + K) + 1) := by
  set L := Nat.log 4 (X + W + K)
  have hsub : (Finset.range N).filter (fun n => NearCopyBdry W K (f n)) ⊆
      (Finset.range (L + 1)).biUnion fun k =>
        ((Finset.range N).filter fun n => runStart k ≤ f n + W + K ∧ f n ≤ runStart k + K) ∪
        ((Finset.range N).filter fun n => (k + 2) * runStart k ≤ f n + K ∧
          f n ≤ (k + 2) * runStart k + W + K) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, k, -, hk⟩ := hn
    have hak : runStart k ≤ X + W + K := by
      have := hX n hnN
      rcases hk with h | h
      · omega
      · have : runStart k ≤ (k + 2) * runStart k := Nat.le_mul_of_pos_left _ (by omega)
        omega
    have hkL : k < L + 1 := by
      have h4 := (four_pow_le_runStart k).trans hak
      have := Nat.le_log_of_pow_le (by norm_num) h4
      omega
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_union, Finset.mem_filter]
    exact ⟨k, hkL, hk.imp (fun h => ⟨hnN, h⟩) (fun h => ⟨hnN, h⟩)⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  have hk : ∀ k ∈ Finset.range (L + 1),
      (((Finset.range N).filter fun n => runStart k ≤ f n + W + K ∧ f n ≤ runStart k + K) ∪
        ((Finset.range N).filter fun n => (k + 2) * runStart k ≤ f n + K ∧
          f n ≤ (k + 2) * runStart k + W + K)).card ≤ 2 * (W + 2 * K + 1) := by
    intro k _
    refine (Finset.card_union_le _ _).trans ?_
    have h1 := card_injOn_window_le f (runStart k + K) (W + 2 * K)
      ((Finset.range N).filter fun n => runStart k ≤ f n + W + K ∧ f n ≤ runStart k + K)
      (hf.mono (by intro x hx; simp only [Finset.coe_filter, Finset.coe_range, Set.mem_ofPred_eq,
        Set.mem_Iio] at hx ⊢; exact Finset.mem_range.1 hx.1))
      (fun n hn => by simp only [Finset.mem_filter] at hn; omega)
    have h2 := card_injOn_window_le f ((k + 2) * runStart k + W + K) (W + 2 * K)
      ((Finset.range N).filter fun n => (k + 2) * runStart k ≤ f n + K ∧
          f n ≤ (k + 2) * runStart k + W + K)
      (hf.mono (by intro x hx; simp only [Finset.coe_filter, Finset.coe_range, Set.mem_ofPred_eq,
        Set.mem_Iio] at hx ⊢; exact Finset.mem_range.1 hx.1))
      (fun n hn => by simp only [Finset.mem_filter] at hn; omega)
    omega
  refine (Finset.sum_le_sum hk).trans ?_
  simp; ring_nf; omega

theorem log_lt_log_of_three_mul {x y : ℕ} (hx : 1 ≤ x) (hxy : 3 * x ≤ y) :
    Nat.log 3 x < Nat.log 3 y := by
  have h1 : Nat.log 3 (x * 3) = Nat.log 3 x + 1 := Nat.log_mul_base (by norm_num) (by omega)
  have h2 : Nat.log 3 (x * 3) ≤ Nat.log 3 y := Nat.log_mono_right (by omega)
  omega

/-- The top of `Y = Hbᵐ` is strictly increasing in `m` (`b ≥ 3`, `H ≥ 1`). -/
theorem strictMono_log_mul_pow {H B : ℕ} (hH : 1 ≤ H) (hB : 3 ≤ B) :
    StrictMono fun m => Nat.log 3 (H * B ^ m) := by
  refine strictMono_nat_of_lt_succ fun m => log_lt_log_of_three_mul
    (Nat.mul_pos hH (by positivity)) ?_
  rw [pow_succ]; nlinarith [Nat.mul_le_mul_left (H * B ^ m) hB]

/-- The top of `ξ = H(b^{m+d} − bᵐ)` is strictly increasing in `d ≥ 1` (`b ≥ 3`, `H ≥ 1`). -/
theorem strictMono_log_pair {H B m : ℕ} (hH : 1 ≤ H) (hB : 3 ≤ B) :
    StrictMono fun d => Nat.log 3 (H * (B ^ (m + (d + 1)) - B ^ m)) := by
  refine strictMono_nat_of_lt_succ fun d => log_lt_log_of_three_mul ?_ ?_
  · have : B ^ m < B ^ (m + (d + 1)) := Nat.pow_lt_pow_right (by omega) (by omega)
    exact Nat.mul_pos hH (by omega)
  · have e : ∀ j, B ^ (m + j) - B ^ m = B ^ m * (B ^ j - 1) := fun j => by
      rw [pow_add, Nat.mul_sub_one]
    rw [e, e]
    have h1 : 1 ≤ B ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
    have h2 : B ^ (d + 1 + 1) = B ^ (d + 1) * B := pow_succ _ _
    have h3 : 3 * (B ^ (d + 1) - 1) ≤ B ^ (d + 1 + 1) - 1 := by
      rw [h2]; have := Nat.mul_le_mul_left (B ^ (d + 1)) hB; omega
    calc 3 * (H * (B ^ m * (B ^ (d + 1) - 1))) = H * (B ^ m * (3 * (B ^ (d + 1) - 1))) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3)

theorem u_le_T {s t e h' m d : ℕ} (ht : 2 ≤ t) (hh : 1 ≤ h') (hd : 1 ≤ d) :
    s * (m + d) + e ≤ Nat.log 3 (pairNat s t e h' m d) := by
  refine Nat.le_log_of_pow_le (by norm_num) ?_
  have h1 := three_pow_le_pow_sub_pow (s := s) (m := m) ht hd
  calc 3 ^ (s * (m + d) + e) = 3 ^ e * 1 * 3 ^ (s * (m + d)) := by rw [pow_add]; ring
    _ ≤ 3 ^ e * h' * ((3 ^ s * t) ^ (m + d) - (3 ^ s * t) ^ m) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hh) h1

/-- **Copy-run bookkeeping.**  Pairs `(m, d)` (`m < N`, `1 ≤ d < N`) with run `k` in
`copyRuns` have `m < m + d < (k+2)a_k + 1`, and only runs `k ≤ log₄(2sN + e)` with `a_k ≤ 2sN + e` occur (so `(k+2)a_k + 1 ≤ (L+2)(2sN+e)+1`;
note `a_L` itself can be superpolynomial in `N`).  So for any
nonnegative `g k n m`, the copy-term sum is at most `Σ_{k ≤ L} Σ_{n,m < (k+2)a_k+1} g k n m`. -/
theorem sum_copyRuns_le {s t e h' : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (hh : 1 ≤ h') (N M : ℕ)
    (g : ℕ → ℕ → ℕ → ℝ) (hg : ∀ k n m, 0 ≤ g k n m) :
    ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N, ∑ k ∈ copyRuns s t e h' m d M, g k (m + d) m ≤
      ∑ k ∈ (Finset.range (Nat.log 4 (s * (2 * N) + e) + 1)).filter (fun k => runStart k ≤ s * (2 * N) + e),
        ∑ n ∈ Finset.range ((k + 2) * runStart k + 1),
          ∑ m ∈ Finset.range ((k + 2) * runStart k + 1), g k n m := by
  set L := Nat.log 4 (s * (2 * N) + e)
  set S : Finset (ℕ × ℕ × ℕ) := ((Finset.range N ×ˢ Finset.Ico 1 N).sigma
    (fun p => copyRuns s t e h' p.1 p.2 M)).map ⟨fun x => (x.2, x.1.1 + x.1.2, x.1.1), by
      rintro ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1 h3
      have : b = b' := by omega
      subst this; rfl⟩
  have lhs : ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N, ∑ k ∈ copyRuns s t e h' m d M,
      g k (m + d) m = ∑ x ∈ S, g x.1 x.2.1 x.2.2 := by
    rw [Finset.sum_map, Finset.sum_sigma, Finset.sum_product]; rfl
  have rhs : ∑ k ∈ (Finset.range (L + 1)).filter (fun k => runStart k ≤ s * (2 * N) + e), ∑ n ∈ Finset.range ((k + 2) * runStart k + 1),
      ∑ m ∈ Finset.range ((k + 2) * runStart k + 1), g k n m =
      ∑ x ∈ ((Finset.range (L + 1)).filter (fun k => runStart k ≤ s * (2 * N) + e)).sigma (fun k => Finset.range ((k + 2) * runStart k + 1) ×ˢ
        Finset.range ((k + 2) * runStart k + 1)), g x.1 x.2.1 x.2.2 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_product]
  rw [lhs, rhs]
  have hsub : S ⊆ (((Finset.range (L + 1)).filter (fun k => runStart k ≤ s * (2 * N) + e)).sigma (fun k => Finset.range ((k + 2) * runStart k + 1) ×ˢ
        Finset.range ((k + 2) * runStart k + 1))).map (Equiv.sigmaEquivProd ℕ (ℕ × ℕ)).toEmbedding := by
    intro x hx
    simp only [S, Finset.mem_map, Finset.mem_sigma, Finset.mem_product, Finset.mem_range,
      Finset.mem_Ico] at hx
    obtain ⟨⟨⟨m, d⟩, k⟩, ⟨⟨hm, hd1, hdN⟩, hk⟩, rfl⟩ := hx
    dsimp only at hm hd1 hdN hk ⊢
    simp only [copyRuns, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨-, ha, hT⟩ := hk
    have huT := u_le_T (s := s) (e := e) (m := m) ht hh hd1
    have hsn : m + d ≤ s * (m + d) := Nat.le_mul_of_pos_left _ hs
    have h1 : runStart k ≤ s * (2 * N) + e := by
      have : s * (m + d) ≤ s * (2 * N) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hkL := Nat.le_log_of_pow_le (by norm_num) ((four_pow_le_runStart k).trans h1)
    simp only [Finset.mem_map, Finset.mem_sigma, Finset.mem_product, Finset.mem_range,
      Finset.mem_filter, Equiv.toEmbedding_apply]
    have hkL' : k < L + 1 := by simp only [L]; omega
    have hn : m + d < (k + 2) * runStart k + 1 := by omega
    have hm' : m < (k + 2) * runStart k + 1 := by omega
    exact ⟨⟨k, (m + d, m)⟩, ⟨⟨hkL', h1⟩, hn, hm'⟩, rfl⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => hg _ _ _).trans (le_of_eq ?_)
  rw [Finset.sum_map]
  rfl

/-- Run-end lengths are monotone. -/
theorem runLen_mono {k L : ℕ} (h : k ≤ L) :
    (k + 2) * runStart k + 1 ≤ (L + 2) * runStart L + 1 := by
  have := runStart_mono h
  have : (k + 2) * runStart k ≤ (L + 2) * runStart L := Nat.mul_le_mul (by omega) this
  omega

/-- **Class-5 copy total.**  Under `CopyZoneDecayH b h'`, the run-by-run copy sums for any
set `Ks` of runs with lengths `≤ Nmax` are at most `|Ks|·|C| Nmax^{2−δ}`. -/
theorem copy5_total_le {b : ℕ} {h' : ℤ} (hC : CopyZoneDecayH b h') :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ (Ks : Finset ℕ) (Nmax : ℕ), (∀ k ∈ Ks, (k + 2) * runStart k + 1 ≤ Nmax) →
      ∑ k ∈ Ks, ∑ n ∈ Finset.range ((k + 2) * runStart k + 1),
        ∑ m ∈ Finset.range ((k + 2) * runStart k + 1),
          cycProd (runStart k) (h' * ((b : ℤ) ^ n - (b : ℤ) ^ m)) ≤
        Ks.card * (|C| * (Nmax : ℝ) ^ (2 - δ)) := by
  obtain ⟨C, δ, hδ, hC⟩ := hC
  refine ⟨C, min δ 1, lt_min hδ one_pos, fun Ks Nmax hKs => ?_⟩
  have hterm : ∀ k ∈ Ks, ∑ n ∈ Finset.range ((k + 2) * runStart k + 1),
        ∑ m ∈ Finset.range ((k + 2) * runStart k + 1),
          cycProd (runStart k) (h' * ((b : ℤ) ^ n - (b : ℤ) ^ m)) ≤
        |C| * (Nmax : ℝ) ^ (2 - min δ 1) := by
    intro k hk
    obtain ⟨h1, h2⟩ := runEnd_succ_le_cube k
    have ha : 1 ≤ runStart k := by have := lt_runStart k; have := four_pow_le_runStart k
                                   have : 1 ≤ 4 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
                                   omega
    refine (hC (runStart k) _ ha h1 h2).trans ?_
    have hN1 : (1 : ℝ) ≤ (((k + 2) * runStart k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hmono : (((k + 2) * runStart k + 1 : ℕ) : ℝ) ≤ (Nmax : ℝ) := by
      exact_mod_cast hKs k hk
    calc C * (((k + 2) * runStart k + 1 : ℕ) : ℝ) ^ (2 - δ)
        ≤ |C| * (((k + 2) * runStart k + 1 : ℕ) : ℝ) ^ (2 - δ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C| * (((k + 2) * runStart k + 1 : ℕ) : ℝ) ^ (2 - min δ 1) := by
          gcongr
          exact min_le_left _ _
      _ ≤ |C| * (Nmax : ℝ) ^ (2 - min δ 1) := by
          gcongr
          have : min δ 1 ≤ 1 := min_le_right _ _
          linarith
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul]


/-- **Class-6 copy total.**  Under `TOrbitCyclicDecay t`, with `h'² ≤ 3^{a_k} − 1` for `k ≥ k₁`:
the run-by-run sums of `cycProd a_k (h' tⁿ)` for `k ≤ L` are at most
`(L+1)|C| N_L^{2−δ} + Σ_{k<k₁} N_k²`. -/
theorem copy6_total_le {t : ℕ} (hT : TOrbitCyclicDecay t) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ (h' : ℤ), h' ≠ 0 → ∀ k₁ : ℕ,
      (∀ k, k₁ ≤ k → (h'.natAbs : ℝ) ^ 2 ≤ 3 ^ runStart k - 1) → ∀ (Ks : Finset ℕ) (Nmax : ℕ),
      (∀ k ∈ Ks, (k + 2) * runStart k + 1 ≤ Nmax) →
      ∑ k ∈ Ks, ∑ n ∈ Finset.range ((k + 2) * runStart k + 1),
        ∑ _m ∈ Finset.range ((k + 2) * runStart k + 1),
          cycProd (runStart k) (h' * (t : ℤ) ^ n) ≤
        Ks.card * (|C| * (Nmax : ℝ) ^ (2 - δ)) +
          ∑ k ∈ Finset.range k₁, ((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2 := by
  obtain ⟨C, δ, hδ, hC⟩ := hT
  refine ⟨C, min δ 1, lt_min hδ one_pos, fun h' hh k₁ hk₁ Ks Nmax hKs => ?_⟩
  set F : ℕ → ℝ := fun k => ∑ n ∈ Finset.range ((k + 2) * runStart k + 1),
        ∑ _m ∈ Finset.range ((k + 2) * runStart k + 1), cycProd (runStart k) (h' * (t : ℤ) ^ n)
  have hF : ∀ k ∈ Ks, F k ≤
      |C| * (Nmax : ℝ) ^ (2 - min δ 1) +
        if k < k₁ then ((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2 else 0 := by
    intro k hk
    set Nk := (k + 2) * runStart k + 1
    have hN1 : (1 : ℝ) ≤ (Nk : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hpos : 0 ≤ |C| * (Nmax : ℝ) ^ (2 - min δ 1) := by positivity
    split_ifs with hlt
    · have : F k ≤ (Nk : ℝ) ^ 2 := by
        simp only [F]
        calc _ ≤ ∑ _n ∈ Finset.range Nk, ∑ _m ∈ Finset.range Nk, (1 : ℝ) :=
              Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => cycProd_le_one _ _
          _ = _ := by simp; ring
      linarith
    · have hg := hk₁ k (by omega)
      obtain ⟨h1, h2⟩ := runEnd_succ_le_cube k
      have ha : 1 ≤ runStart k := by
        have := four_pow_le_runStart k
        have : 1 ≤ 4 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      have hO := hC (runStart k) Nk ha h1 h2 h' (gcd_sq_le_of_natAbs hh _ hg)
      have : F k = Nk * ∑ n ∈ Finset.range Nk, cycProd (runStart k) (h' * (t : ℤ) ^ n) := by
        simp only [F]; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [this, add_zero]
      have hmono : (Nk : ℝ) ≤ (Nmax : ℝ) := by
        exact_mod_cast hKs k hk
      calc (Nk : ℝ) * ∑ n ∈ Finset.range Nk, cycProd (runStart k) (h' * (t : ℤ) ^ n)
          ≤ Nk * (|C| * (Nk : ℝ) ^ (1 - δ)) :=
            mul_le_mul_of_nonneg_left (hO.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
              (by positivity))) (by positivity)
        _ = |C| * (Nk : ℝ) ^ (2 - δ) := by
            rw [show (2 : ℝ) - δ = 1 + (1 - δ) by ring, Real.rpow_add (by linarith),
              Real.rpow_one]; ring
        _ ≤ |C| * (Nk : ℝ) ^ (2 - min δ 1) := by gcongr; exact min_le_left _ _
        _ ≤ _ := by
            gcongr
            have : min δ 1 ≤ 1 := min_le_right _ _
            linarith
  refine (Finset.sum_le_sum hF).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  gcongr
  rw [← Finset.sum_filter]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) (fun _ _ _ => by positivity)
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢; exact hk.2

theorem sum_shift_le (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) {m N : ℕ} (hm : m < N) :
    ∑ d ∈ Finset.Ico 1 N, f (m + d) ≤ ∑ n ∈ Finset.range (2 * N), f n := by
  have : ∑ d ∈ Finset.Ico 1 N, f (m + d) = ∑ n ∈ (Finset.Ico 1 N).map (addLeftEmbedding m), f n := by
    rw [Finset.sum_map]; rfl
  rw [this]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => hf n)
  simp only [Finset.mem_map, Finset.mem_Ico, addLeftEmbedding_apply] at hn
  obtain ⟨d, ⟨-, hd⟩, rfl⟩ := hn
  exact Finset.mem_range.2 (by omega)

/-- **Class-3 sum, concrete.**  For `h'` prime to 3,
`Σ_{m<N} Σ_{1≤d<N} Hf_true(h' t^{m+d}) ≤ N(2N + 2·3ʲ)(3/2)^{tb}(2/3)ʲ`. -/
theorem sum_pair_class3_le {t : ℕ} (ht : 2 ≤ t) (h3 : ¬ 3 ∣ t) {h' : ℕ} (hh : ¬ 3 ∣ h')
    (j N : ℕ) :
    ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N,
      Hf (fun _ => true) 0 (j + 1) ((h' * t ^ (m + d) : ℕ) : ℝ) ≤
      N * ((2 * N + 2 * 3 ^ j) * (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t * (2 / 3 : ℝ) ^ j) := by
  have hs := CantorExactExponentProfile.sum_hf_true_le ht h3 j h' hh (2 * N)
  calc _ ≤ ∑ _m ∈ Finset.range N, ∑ n ∈ Finset.range (2 * N),
        Hf (fun _ => true) 0 (j + 1) ((h' * t ^ n : ℕ) : ℝ) :=
        Finset.sum_le_sum fun m hm => sum_shift_le
          (fun n => Hf (fun _ => true) 0 (j + 1) ((h' * t ^ n : ℕ) : ℝ))
          (fun n => Hf_nonneg _ _ _ _) (Finset.mem_range.1 hm)
    _ ≤ _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        gcongr
        push_cast at hs ⊢
        exact hs

/-- **Total of the pair majorant.**  With `W = j + 1`, `h'` prime to 3 and `t` as usual: the
sum of `pairMaj` over `m < N`, `1 ≤ d < N` is at most the class-1/3 orbit sums, `2N` top-window
sums (each bounded by `Btop`), the copy-run totals `Σ_{k ∈ Ks} Σ_{n,m < N_k}` and the error
`N²·8π/3^K`.  `Btop` is any bound for `Σ_{m<N} topProd W {m log₃ t + β}` uniform in `β`
(`sum_class_top_le`). -/
theorem sum_pairMaj_le {s t e h' : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (h3 : ¬ 3 ∣ t) (hh1 : 1 ≤ h')
    (hh : ¬ 3 ∣ h') (j K N M : ℕ) (Btop : ℝ)
    (hBtop : ∀ β : ℝ, ∑ m ∈ Finset.range N,
      CantorExactExponentProfile.topProd (j + 1) (Int.fract (m * Real.logb 3 t + β)) ≤ Btop) :
    ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N, pairMaj s t e h' m d M (j + 1) K ≤
      N * ((N + 2 * 3 ^ j) * (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t * (2 / 3 : ℝ) ^ j) +
      N * ((2 * N + 2 * 3 ^ j) * (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t * (2 / 3 : ℝ) ^ j) +
      2 * N * Btop +
      ∑ k ∈ (Finset.range (Nat.log 4 (s * (2 * N) + e) + 1)).filter
          (fun k => runStart k ≤ s * (2 * N) + e),
        ∑ n ∈ Finset.range ((k + 2) * runStart k + 1),
          ∑ m ∈ Finset.range ((k + 2) * runStart k + 1),
            (cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ m))
              + cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ n)) +
      N * N * (Real.pi * (8 / 3 ^ K)) := by
  unfold pairMaj
  simp only [Finset.sum_add_distrib]
  -- class 1
  have c1 : ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N,
      Hf (fun _ => true) 0 (j + 1) ((h' * ((3 ^ s * t) ^ d - 1) * t ^ m : ℕ) : ℝ) ≤
      N * ((N + 2 * 3 ^ j) * (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t * (2 / 3 : ℝ) ^ j) := by
    rw [Finset.sum_comm]; exact sum_class_low_le hs ht h3 h' hh j N
  have c3 := sum_pair_class3_le ht h3 hh j N
  have c2 : ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N,
      CantorExactExponentProfile.topProd (j + 1) (Int.fract (m * Real.logb 3 t +
        Real.logb 3 ((3 ^ e * h' : ℕ) : ℝ))) ≤ N * Btop := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _d ∈ Finset.Ico 1 N, Btop := Finset.sum_le_sum fun d _ => hBtop _
      _ ≤ _ := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        have : 0 ≤ Btop := (Finset.sum_nonneg fun _ _ => topProd_nonneg' _ _).trans (hBtop 0)
        gcongr; exact_mod_cast Nat.sub_le _ _
  have c4 : ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N,
      CantorExactExponentProfile.topProd (j + 1) (Int.fract (m * Real.logb 3 t +
        Real.logb 3 ((3 ^ e * h' * ((3 ^ s * t) ^ d - 1) : ℕ) : ℝ))) ≤ N * Btop := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _d ∈ Finset.Ico 1 N, Btop := Finset.sum_le_sum fun d _ => hBtop _
      _ ≤ _ := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        have : 0 ≤ Btop := (Finset.sum_nonneg fun _ _ => topProd_nonneg' _ _).trans (hBtop 0)
        gcongr; exact_mod_cast Nat.sub_le _ _
  have c56 := sum_copyRuns_le (t := t) (e := e) (h' := h') hs ht hh1 N M
    (fun k n m => cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ n -
      ((3 ^ s * t : ℕ) : ℤ) ^ m)) + cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ n))
    (fun k n m => add_nonneg (cycProd_nonneg _ _) (cycProd_nonneg _ _))
  simp only [Finset.sum_add_distrib] at c56
  have ce : ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N, Real.pi * (8 / 3 ^ K) ≤
      N * N * (Real.pi * (8 / 3 ^ K)) := by
    simp only [Finset.sum_const, Finset.card_range, Nat.card_Ico, nsmul_eq_mul]
    have h1 : 0 ≤ Real.pi * (8 / 3 ^ K) := by positivity
    have h2 : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le _ _
    have h3 : (0 : ℝ) ≤ N := by positivity
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 h1) h3
    calc _ = (N : ℝ) * (((N - 1 : ℕ) : ℝ) * (Real.pi * (8 / 3 ^ K))) := by ring
      _ ≤ _ := this.trans (le_of_eq (by ring))
  refine (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add c1 c2) c3) c4) c56) ce).trans
    (le_of_eq ?_)
  ring

theorem pairMaj_nonneg (s t e h' m d M W K : ℕ) : 0 ≤ pairMaj s t e h' m d M W K := by
  unfold pairMaj
  have := Hf_nonneg (fun _ => true) 0 W ((h' * ((3 ^ s * t) ^ d - 1) * t ^ m : ℕ) : ℝ)
  have := Hf_nonneg (fun _ => true) 0 W ((h' * t ^ (m + d) : ℕ) : ℝ)
  have := topProd_nonneg' W (Int.fract (m * Real.logb 3 t + Real.logb 3 ((3 ^ e * h' : ℕ) : ℝ)))
  have := topProd_nonneg' W (Int.fract (m * Real.logb 3 t +
    Real.logb 3 ((3 ^ e * h' * ((3 ^ s * t) ^ d - 1) : ℕ) : ℝ)))
  have : 0 ≤ ∑ k ∈ copyRuns s t e h' m d M,
    (cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℤ) ^ m))
      + cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ (m + d))) :=
    Finset.sum_nonneg fun _ _ => add_nonneg (cycProd_nonneg _ _) (cycProd_nonneg _ _)
  have : 0 ≤ Real.pi * (8 / 3 ^ K) := by positivity
  linarith

/-- The pair `(m, d)` is **good** when `pair_classes` applies: `m` large, past run `k₀`, and none
of the four window ends in a copy-boundary band. -/
def PairGood (s t e h' m d k₀ W K : ℕ) : Prop :=
  3 ^ e * h' < 3 ^ (s * m) ∧ runStart k₀ ≤ s * m + e ∧ W ≤ s * m + e ∧ K ≤ s * m + e ∧
    ¬ NearCopyBdry W K (s * m + e) ∧
    ¬ NearCopyBdry W K (Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m)) ∧
    ¬ NearCopyBdry W K (s * (m + d) + e) ∧
    ¬ NearCopyBdry W K (Nat.log 3 (pairNat s t e h' m d))

open Classical in
/-- **Every pair has an option bounded by `pairMaj` plus a bad-pair indicator.** -/
theorem exists_option_le_pairMaj_bad {s t e h' m d ρ k₀ M W K : ℕ} (ht : 2 ≤ t) (hh : 1 ≤ h')
    (hd : 1 ≤ d) (hs : 1 ≤ s) (hρ1 : 1 ≤ ρ) (hb : 3 ^ s * t ≤ 3 ^ (s * (ρ - 1)))
    (hρ : ρ * (ρ + 1) ≤ 4 * (k₀ + 3)) (hMu : s * (m + d) + e + W ≤ M)
    (hMT : Nat.log 3 (pairNat s t e h' m d) ≤ M) :
    ∃ o, repBound M o (pairNat s t e h' m d) ≤
      pairMaj s t e h' m d M W K + (if PairGood s t e h' m d k₀ W K then 0 else 1) := by
  by_cases hg : PairGood s t e h' m d k₀ W K
  · obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hg
    obtain ⟨o, ho⟩ := exists_option_le_pairMaj (K := K) (by omega) hh hd hs hMu hMT
      (pair_classes ht hh hd hρ1 hb g1 hρ g2 g3 g4 g5 g6 g7 g8)
    exact ⟨o, by rw [if_pos ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩]; linarith⟩
  · refine ⟨none, ?_⟩
    rw [if_neg hg]
    linarith [repBound_le_one M none (pairNat s t e h' m d), pairMaj_nonneg s t e h' m d M W K]

theorem sum_Ico_ite_le (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    ∑ d ∈ Finset.Ico 1 N, (if P d then 1 else 0 : ℕ) ≤
      ((Finset.range N).filter fun d => P (d + 1)).card := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.card_filter]
  simp only [add_comm 1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (Nat.sub_le N 1))
    (fun _ _ _ => Nat.zero_le _)

open Classical in
/-- **Bad-pair count.**  Pairs failing `PairGood` number at most `N(m₀ + 4·band)`: `m < m₀` (small
`m`), or one of four window ends in a copy-boundary band (`card_nearCopyBdry_le_of`, each end
injective in `m` or in `d`). -/
theorem sum_bad_le {s t e h' k₀ W K N m₀ X : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (hh : 1 ≤ h')
    (hm₀ : ∀ m, m₀ ≤ m → 3 ^ e * h' < 3 ^ (s * m) ∧ runStart k₀ ≤ s * m + e ∧ W ≤ s * m + e ∧
      K ≤ s * m + e)
    (hX : ∀ m < N, ∀ d ≤ N, s * m + e ≤ X ∧ Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) ≤ X ∧
      s * (m + d) + e ≤ X ∧ Nat.log 3 (pairNat s t e h' m d) ≤ X) :
    ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N,
        (if PairGood s t e h' m d k₀ W K then 0 else 1 : ℕ) ≤
      N * (m₀ + 4 * (2 * (W + 2 * K + 1) * (Nat.log 4 (X + W + K) + 1))) := by
  set Bd := 2 * (W + 2 * K + 1) * (Nat.log 4 (X + W + K) + 1)
  have hB3 : 3 ≤ 3 ^ s * t := by
    have : 3 ≤ 3 ^ s := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ s := Nat.pow_le_pow_right (by norm_num) hs
    nlinarith
  have hpt : ∀ m d, (if PairGood s t e h' m d k₀ W K then 0 else 1 : ℕ) ≤
      (if m < m₀ then 1 else 0) + (if NearCopyBdry W K (s * m + e) then 1 else 0) +
      (if NearCopyBdry W K (Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m)) then 1 else 0) +
      (if NearCopyBdry W K (s * (m + d) + e) then 1 else 0) +
      (if NearCopyBdry W K (Nat.log 3 (pairNat s t e h' m d)) then 1 else 0) := by
    intro m d
    by_cases hg : PairGood s t e h' m d k₀ W K
    · simp [hg]
    · rw [if_neg hg]
      by_contra hc
      apply hg
      have h1 : ¬ m < m₀ := fun h => hc (by rw [if_pos h]; omega)
      obtain ⟨a1, a2, a3, a4⟩ := hm₀ m (by omega)
      refine ⟨a1, a2, a3, a4, fun h => hc (by rw [if_pos h]; omega),
        fun h => hc (by rw [if_pos h]; omega),
        fun h => hc (by rw [if_pos h]; omega), fun h => hc (by rw [if_pos h]; omega)⟩
  refine (Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun d _ => hpt m d).trans ?_
  simp only [Finset.sum_add_distrib]
  -- small m
  have s1 : ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N, (if m < m₀ then 1 else 0 : ℕ) ≤ N * m₀ := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _d ∈ Finset.Ico 1 N, m₀ := Finset.sum_le_sum fun d _ => by
          rw [Finset.sum_boole]; simp only [Nat.cast_id]
          calc _ ≤ (Finset.range m₀).card := Finset.card_le_card fun x hx => by
                simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢; exact hx.2
            _ = m₀ := Finset.card_range _
      _ ≤ N * m₀ := by simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; nlinarith [Nat.sub_le N 1]
  have sm : ∀ f : ℕ → ℕ, Set.InjOn f (Finset.range N) → (∀ m < N, f m ≤ X) →
      ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N, (if NearCopyBdry W K (f m) then 1 else 0 : ℕ) ≤
        N * Bd := by
    intro f hf hfX
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _d ∈ Finset.Ico 1 N, Bd := Finset.sum_le_sum fun d _ => by
          rw [Finset.sum_boole]; simp only [Nat.cast_id]
          exact card_nearCopyBdry_le_of f W K N X hf hfX
      _ ≤ N * Bd := by simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; nlinarith [Nat.sub_le N 1]
  have sd : ∀ g : ℕ → ℕ → ℕ, (∀ m < N, Set.InjOn (fun d => g m (d + 1)) (Finset.range N)) →
      (∀ m < N, ∀ d < N, g m (d + 1) ≤ X) →
      ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N, (if NearCopyBdry W K (g m d) then 1 else 0 : ℕ) ≤
        N * Bd := by
    intro g hg hgX
    calc _ ≤ ∑ _m ∈ Finset.range N, Bd := Finset.sum_le_sum fun m hm => by
          have hm := Finset.mem_range.1 hm
          refine (sum_Ico_ite_le (fun d => NearCopyBdry W K (g m d)) N).trans ?_
          exact card_nearCopyBdry_le_of (fun d => g m (d + 1)) W K N X (hg m hm) (hgX m hm)
      _ = N * Bd := by simp
  have s2 := sm (fun m => s * m + e) (fun a _ b _ hab => by
    exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_right_cancel hab))
    (fun m hm => (hX m hm 0 (Nat.zero_le _)).1)
  have s3 := sm (fun m => Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m))
    ((strictMono_log_mul_pow (Nat.mul_pos (by positivity) hh) hB3).injective.injOn)
    (fun m hm => (hX m hm 0 (Nat.zero_le _)).2.1)
  have s4 := sd (fun m d => s * (m + d) + e) (fun m _ a _ b _ hab => by
    simp only at hab; have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < s) (by omega : s * (m + (a + 1)) = s * (m + (b + 1))); omega)
    (fun m hm d hd => (hX m hm (d + 1) (by omega)).2.2.1)
  have s5 := sd (fun m d => Nat.log 3 (pairNat s t e h' m d))
    (fun m _ => (strictMono_log_pair (m := m) (Nat.mul_pos (by positivity) hh) hB3).injective.injOn)
    (fun m hm d hd => (hX m hm (d + 1) (by omega)).2.2.2)
  have : N * (m₀ + 4 * Bd) = N * m₀ + N * Bd + N * Bd + N * Bd + N * Bd := by ring
  rw [this]
  omega

/-- `repBound` is even in `ξ`. -/
theorem repBound_neg (M : ℕ) (o : Option ℕ) (ξ : ℝ) : repBound M o (-ξ) = repBound M o ξ := by
  cases o with
  | none => exact Bf_neg _ _ _
  | some k => exact repBound_some_neg M k ξ

theorem sum_ite_shift_le (G : ℕ → ℝ) (hG : ∀ d, 0 ≤ G d) (m N : ℕ) :
    ∑ n ∈ Finset.range N, (if m < n then G (n - m) else 0) ≤ ∑ d ∈ Finset.Ico 1 N, G d := by
  rw [← Finset.sum_filter]
  rw [← Finset.sum_image (g := fun n => n - m) (f := G) (fun a ha b hb hab => by
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb; simp at hab; omega)]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun d hd => ?_) (fun d _ _ => hG d)
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hd
  obtain ⟨n, ⟨h1, h2⟩, rfl⟩ := hd
  simp only [Finset.mem_Ico]; omega

/-- **Half-sum reduction.**  Diagonal pairs cost `≤ 1`; by `repBound_neg` the pair `(m+d, m)`
and `(m, m+d)` share an option; so per-`(m, d)` options bounded by `G m d ≥ 0` give options for
the full square with sum `≤ N + 2 Σ_{m<N} Σ_{1≤d<N} G m d`. -/
theorem exists_kappa_half (M : ℕ) (b h : ℝ) (G : ℕ → ℕ → ℝ) (hG0 : ∀ m d, 0 ≤ G m d)
    (hG : ∀ m d, 1 ≤ d → ∃ o, repBound M o (h * (b ^ (m + d) - b ^ m)) ≤ G m d) (N : ℕ) :
    ∃ κ : ℕ → ℕ → Option ℕ, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      repBound M (κ n m) (h * (b ^ n - b ^ m)) ≤
        N + 2 * ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N, G m d := by
  set P : ℕ → ℕ → ℝ := fun m n => if m < n then G m (n - m) else 0
  have hP0 : ∀ m n, 0 ≤ P m n := fun m n => by simp only [P]; split_ifs <;> simp [hG0]
  obtain ⟨κ, hκ⟩ := exists_kappa_sum_le M (fun n m => h * (b ^ n - b ^ m))
    (fun n m => (if n = m then 1 else 0) + P m n + P n m) (fun n m => by
      rcases lt_trichotomy m n with hl | rfl | hl
      · obtain ⟨o, ho⟩ := hG m (n - m) (by omega)
        refine ⟨o, ?_⟩
        have e : m + (n - m) = n := by omega
        rw [e] at ho
        simp only [P, if_pos hl, if_neg (by omega : ¬ n < m), if_neg (by omega : n ≠ m)]
        linarith
      · exact ⟨none, by simp only [if_true, P, lt_irrefl, if_false]; linarith [repBound_le_one M none (h * (b ^ m - b ^ m))]⟩
      · obtain ⟨o, ho⟩ := hG n (m - n) (by omega)
        refine ⟨o, ?_⟩
        have e : n + (m - n) = m := by omega
        rw [e, ← repBound_neg] at ho
        simp only [P, if_pos hl, if_neg (by omega : ¬ m < n), if_neg (by omega : n ≠ m)]
        rw [show h * (b ^ n - b ^ m) = -(h * (b ^ m - b ^ n)) by ring]; linarith)
    N
  refine ⟨κ, hκ.trans ?_⟩
  simp only [Finset.sum_add_distrib]
  have hdiag : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (if n = m then (1 : ℝ) else 0) = N := by
    simp [Finset.sum_ite_eq, Finset.filter_true_of_mem (fun x hx => Finset.mem_range.1 hx)]
  have hA : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, P m n ≤
      ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N, G m d := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun m _ => sum_ite_shift_le (G m) (hG0 m) m N
  have hB : ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, P n m ≤
      ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N, G m d :=
    Finset.sum_le_sum fun m _ => sum_ite_shift_le (G m) (hG0 m) m N
  linarith

theorem pairNat_cast {s t : ℕ} (e h' m d : ℕ) (ht : 1 ≤ t) :
    (pairNat s t e h' m d : ℝ) = ((3 ^ e * h' : ℕ) : ℝ) *
      (((3 ^ s * t : ℕ) : ℝ) ^ (m + d) - ((3 ^ s * t : ℕ) : ℝ) ^ m) := by
  unfold pairNat
  have : (3 ^ s * t) ^ m ≤ (3 ^ s * t) ^ (m + d) :=
    Nat.pow_le_pow_right (Nat.mul_pos (by positivity) ht) (by omega)
  push_cast [this]
  ring

open Classical in
/-- **Per-`N` bound for `h = 3ᵉh' > 0`.**  Combines `exists_kappa_half`,
`exists_option_le_pairMaj_bad`: the full pair sum is at most `N + 2(Σ pairMaj + #bad)`. -/
theorem exists_kappa_pos {s t e h' ρ k₀ M W K N : ℕ} (ht : 2 ≤ t) (hh : 1 ≤ h') (hs : 1 ≤ s)
    (hρ1 : 1 ≤ ρ) (hb : 3 ^ s * t ≤ 3 ^ (s * (ρ - 1))) (hρ : ρ * (ρ + 1) ≤ 4 * (k₀ + 3))
    (hM : ∀ m < N, ∀ d < N, s * (m + d) + e + W ≤ M ∧ Nat.log 3 (pairNat s t e h' m d) ≤ M) :
    ∃ κ : ℕ → ℕ → Option ℕ, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      repBound M (κ n m) (((3 ^ e * h' : ℕ) : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ n -
        ((3 ^ s * t : ℕ) : ℝ) ^ m)) ≤
        N + 2 * (∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N, pairMaj s t e h' m d M W K +
          ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N,
            ((if PairGood s t e h' m d k₀ W K then 0 else 1 : ℕ) : ℝ)) := by
  set G : ℕ → ℕ → ℝ := fun m d => if m < N ∧ d < N then pairMaj s t e h' m d M W K +
    ((if PairGood s t e h' m d k₀ W K then 0 else 1 : ℕ) : ℝ) else 1
  have hG0 : ∀ m d, 0 ≤ G m d := fun m d => by
    simp only [G]; split_ifs <;> push_cast <;> linarith [pairMaj_nonneg s t e h' m d M W K]
  obtain ⟨κ, hκ⟩ := exists_kappa_half M ((3 ^ s * t : ℕ) : ℝ) ((3 ^ e * h' : ℕ) : ℝ) G hG0 (fun m d hd => by
    by_cases hmd : m < N ∧ d < N
    · obtain ⟨o, ho⟩ := exists_option_le_pairMaj_bad (k₀ := k₀) (K := K) ht hh hd hs hρ1 hb hρ
        (hM m hmd.1 d hmd.2).1 (hM m hmd.1 d hmd.2).2
      refine ⟨o, ?_⟩
      rw [← pairNat_cast e h' m d (by omega)]
      simp only [G, if_pos hmd]
      rw [Nat.cast_ite, Nat.cast_zero, Nat.cast_one]; exact ho
    · exact ⟨none, by simp only [G, if_neg hmd]; exact repBound_le_one _ _ _⟩) N
  refine ⟨κ, hκ.trans (le_of_eq ?_)⟩
  rw [← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  simp only [G, if_pos (⟨Finset.mem_range.1 hm, (Finset.mem_Ico.1 hd).2⟩ : m < N ∧ d < N)]

/-- **Pair sums with a power saving.**  For each `h ≠ 0` and each `N ≥ 1` some choice of options
makes the pair sum `≤ C N^{2−δ}`.  This is the per-`N` content of the assembly; summability along
`sched` is then automatic (`repPairArith_of_power`). -/
def RepPairPower (b : ℕ) : Prop :=
  ∀ h : ℤ, h ≠ 0 → ∃ C δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N → ∃ (M : ℕ) (κ : ℕ → ℕ → Option ℕ),
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      repBound M (κ n m) (h * ((b : ℝ) ^ n - (b : ℝ) ^ m)) ≤ C * (N : ℝ) ^ (2 - δ)

theorem one_le_sched (j : ℕ) : 1 ≤ sched j := by
  unfold sched
  have : 1 ≤ ⌊Real.exp (Real.sqrt j)⌋₊ :=
    Nat.le_floor (by push_cast; exact Real.one_le_exp (Real.sqrt_nonneg _))
  omega

/-- Proved: a power saving is summable along `sched`. -/
theorem repPairArith_of_power {b : ℕ} (hP : RepPairPower b) : RepPairArith b := by
  intro h hh
  obtain ⟨C, δ, hδ, hC⟩ := hP h hh
  choose M κ hMκ using fun j => hC (sched j) (one_le_sched j)
  refine ⟨M, κ, ?_⟩
  refine ((CantorExactExponentProfile.summable_sched_rpow hδ).mul_left C).of_nonneg_of_le
    (fun j => div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_)
      (by positivity)) (fun j => ?_)
  · cases κ j _ _ <;> simp only [repBound]
    · exact Bf_nonneg _ _ _
    · split_ifs
      · exact Finset.prod_nonneg fun _ _ => abs_nonneg _
      · exact zero_le_one
  · have hN : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
    rw [div_le_iff₀ (by positivity)]
    refine (hMκ j).trans (le_of_eq ?_)
    rw [mul_assoc, ← Real.rpow_natCast (sched j : ℝ) 2, ← Real.rpow_add hN]
    norm_num; ring_nf; simp


/-- **Sign and 3-part reduction.**  `RepPairPower b` follows from its case `h = 3ᵉh' > 0`,
`3 ∤ h'`, by `repBound_neg`. -/
theorem repPairPower_of_pos {b : ℕ}
    (hP : ∀ e h' : ℕ, 1 ≤ h' → ¬ 3 ∣ h' → ∃ C δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N →
      ∃ (M : ℕ) (κ : ℕ → ℕ → Option ℕ), ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        repBound M (κ n m) (((3 ^ e * h' : ℕ) : ℝ) * ((b : ℝ) ^ n - (b : ℝ) ^ m)) ≤
          C * (N : ℝ) ^ (2 - δ)) :
    RepPairPower b := by
  intro h hh
  obtain ⟨e, h', hnd, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hh) 3
    (by norm_num)
  have h1 : 1 ≤ h' := Nat.pos_of_ne_zero (by rintro rfl; simp at hnd)
  obtain ⟨C, δ, hδ, hC⟩ := hP e h' h1 hnd
  refine ⟨C, δ, hδ, fun N hN => ?_⟩
  obtain ⟨M, κ, hκ⟩ := hC N hN
  refine ⟨M, κ, le_of_eq_of_le ?_ hκ⟩
  have habs : ((3 ^ e * h' : ℕ) : ℝ) = |(h : ℝ)| := by
    rw [← he, Nat.cast_natAbs, Int.cast_abs]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [habs]
  rcases abs_choice (h : ℝ) with ha | ha <;> rw [ha]
  rw [show -(h : ℝ) * ((b : ℝ) ^ n - (b : ℝ) ^ m) = -((h : ℝ) * ((b : ℝ) ^ n - (b : ℝ) ^ m)) by ring,
    repBound_neg]


/-- The trivial bound: every pair term is `≤ 1`, so some (any) option choice gives `≤ N²`. -/
theorem repPair_sum_le_sq (M N : ℕ) (κ : ℕ → ℕ → Option ℕ) (ξ : ℕ → ℕ → ℝ) :
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, repBound M (κ n m) (ξ n m) ≤ (N : ℝ) ^ 2 := by
  calc _ ≤ ∑ _n ∈ Finset.range N, ∑ _m ∈ Finset.range N, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => repBound_le_one _ _ _
    _ = (N : ℝ) ^ 2 := by simp; ring

/-- **Eventual power bounds suffice.**  A bound `C N^{2−δ}` for `N ≥ N₀` extends to all
`N ≥ 1` (small `N` by `repPair_sum_le_sq`). -/
theorem power_of_eventually (ξ : ℕ → ℕ → ℕ → ℝ)
    (hev : ∃ C δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N → ∃ (M : ℕ) (κ : ℕ → ℕ → Option ℕ),
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, repBound M (κ n m) (ξ N n m) ≤
        C * (N : ℝ) ^ (2 - δ)) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N → ∃ (M : ℕ) (κ : ℕ → ℕ → Option ℕ),
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, repBound M (κ n m) (ξ N n m) ≤
        C * (N : ℝ) ^ (2 - δ) := by
  obtain ⟨C, δ, hδ, N₀, hC⟩ := hev
  refine ⟨|C| + N₀, min δ 1, lt_min hδ one_pos, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℝ) ≤ (N : ℝ) ^ (2 - min δ 1) := by positivity
  by_cases h : N₀ ≤ N
  · obtain ⟨M, κ, hMκ⟩ := hC N h hN
    refine ⟨M, κ, hMκ.trans ?_⟩
    have : (N : ℝ) ^ (2 - δ) ≤ (N : ℝ) ^ (2 - min δ 1) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [min_le_left δ 1])
    have h0 : (0 : ℝ) ≤ (N : ℝ) ^ (2 - δ) := by positivity
    nlinarith [le_abs_self C, abs_nonneg C, (Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)]
  · refine ⟨0, fun _ _ => none, (repPair_sum_le_sq 0 N _ (ξ N)).trans ?_⟩
    have hsplit : (N : ℝ) ^ 2 = (N : ℝ) ^ (min δ 1) * (N : ℝ) ^ (2 - min δ 1) := by
      rw [← Real.rpow_add (by linarith), ← Real.rpow_natCast]; norm_num
    have h1 : (N : ℝ) ^ (min δ 1) ≤ N₀ := by
      calc (N : ℝ) ^ (min δ 1) ≤ (N : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _)
        _ ≤ N₀ := by rw [Real.rpow_one]; exact_mod_cast (by omega : N ≤ N₀)
    rw [hsplit]
    nlinarith [abs_nonneg C]

/-! ### Asymptotic helpers for the per-`N` arithmetic -/

theorem natLog_le_rpow {b : ℕ} (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) (x : ℕ) :
    (Nat.log b x : ℝ) ≤ (x : ℝ) ^ ε / (ε * Real.log 2) := by
  have h1 := Real.natLog_le_logb x b
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlb : Real.log 2 ≤ Real.log b := Real.log_le_log (by norm_num) (by exact_mod_cast hb)
  have hx : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  have h2 : Real.logb b x ≤ Real.log x / Real.log 2 := by
    rw [Real.logb]; exact div_le_div_of_nonneg_left hx hl2 hlb
  have h3 : Real.log x / Real.log 2 ≤ ((x : ℝ) ^ ε / ε) / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_rpow_div (by positivity) hε) hl2.le
  calc (Nat.log b x : ℝ) ≤ _ := h1.trans (h2.trans h3)
    _ = _ := by rw [div_div]

/-- `log_b(aN + c) + 2 ≤ A N^ε` for `N ≥ 1`. -/
theorem natLog_lin_le_rpow {b : ℕ} (hb : 2 ≤ b) {ε : ℝ} (hε : 0 < ε) (a c : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ, 1 ≤ N → (Nat.log b (a * N + c) : ℝ) + 2 ≤ A * (N : ℝ) ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨((a + c : ℕ) : ℝ) ^ ε / (ε * Real.log 2) + 2, by positivity, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 := natLog_le_rpow hb hε (a * N + c)
  have h2 : ((a * N + c : ℕ) : ℝ) ≤ ((a + c : ℕ) : ℝ) * N := by
    push_cast; nlinarith [(Nat.cast_nonneg c : (0 : ℝ) ≤ c)]
  have h3 : ((a * N + c : ℕ) : ℝ) ^ ε ≤ ((a + c : ℕ) : ℝ) ^ ε * (N : ℝ) ^ ε := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) h2 hε.le
  have h4 : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have h5 : ((a * N + c : ℕ) : ℝ) ^ ε / (ε * Real.log 2) ≤
      ((a + c : ℕ) : ℝ) ^ ε / (ε * Real.log 2) * (N : ℝ) ^ ε := by
    rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right h3 (by positivity)
  nlinarith

/-- `j = ⌊log₃ N / q⌋`: `3ʲ ≤ N^{1/q} < 3^{j+1}`. -/
theorem three_pow_logdiv {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) :
    (3 : ℝ) ^ (Nat.log 3 N / q) ≤ (N : ℝ) ^ ((q : ℝ)⁻¹) ∧
      (N : ℝ) ^ ((q : ℝ)⁻¹) < 3 ^ (Nat.log 3 N / q + 1) := by
  set L := Nat.log 3 N
  set j := L / q
  have hq0 : q ≠ 0 := by omega
  have hpos : (0 : ℝ) < (q : ℝ)⁻¹ := by positivity
  constructor
  · have h1 : 3 ^ (j * q) ≤ N :=
      (Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self L q)).trans
        (Nat.pow_log_le_self 3 (by omega))
    have h2 : ((3 : ℝ) ^ j) ^ q ≤ N := by rw [← pow_mul]; exact_mod_cast h1
    calc (3 : ℝ) ^ j = (((3 : ℝ) ^ j) ^ q) ^ ((q : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (by positivity) hq0).symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h2 hpos.le
  · have h1 : N < 3 ^ ((j + 1) * q) := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) N
      have h3 : L + 1 ≤ (j + 1) * q := by
        have := Nat.lt_div_mul_add (a := L) (Nat.pos_of_ne_zero hq0)
        simp only [j]; nlinarith
      exact this.trans_le (Nat.pow_le_pow_right (by norm_num) h3)
    have h2 : (N : ℝ) < ((3 : ℝ) ^ (j + 1)) ^ q := by rw [← pow_mul]; exact_mod_cast h1
    calc (N : ℝ) ^ ((q : ℝ)⁻¹) < (((3 : ℝ) ^ (j + 1)) ^ q) ^ ((q : ℝ)⁻¹) :=
          Real.rpow_lt_rpow (by positivity) h2 hpos
      _ = _ := Real.pow_rpow_inv_natCast (by positivity) hq0

/-- Decay `α^{j+1} ≤ N^{log₃α / q}` for `0 < α ≤ 1`, `j = ⌊log₃ N / q⌋`. -/
theorem pow_logdiv_le {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    α ^ (Nat.log 3 N / q + 1) ≤ (N : ℝ) ^ (Real.logb 3 α / q) := by
  have hc : Real.logb 3 α ≤ 0 := Real.logb_nonpos (by norm_num) hα0.le hα1
  have h := (three_pow_logdiv hq hN).2
  have hN0 : (0 : ℝ) < (N : ℝ) ^ ((q : ℝ)⁻¹) := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  calc α ^ (Nat.log 3 N / q + 1) = ((3 : ℝ) ^ (Nat.log 3 N / q + 1)) ^ Real.logb 3 α := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
          Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hα0]
    _ ≤ ((N : ℝ) ^ ((q : ℝ)⁻¹)) ^ Real.logb 3 α := Real.rpow_le_rpow_of_nonpos hN0 h.le hc
    _ = _ := by rw [← Real.rpow_mul (by positivity)]; ring_nf

theorem rpow_mul_rpow_nat {N : ℕ} (hN : 1 ≤ N) (a b : ℝ) :
    (N : ℝ) ^ a * (N : ℝ) ^ b = (N : ℝ) ^ (a + b) :=
  (Real.rpow_add (by exact_mod_cast hN) a b).symm

theorem nat_sq_rpow {N : ℕ} (hN : 1 ≤ N) (a : ℝ) :
    (N : ℝ) * (N : ℝ) * (N : ℝ) ^ a = (N : ℝ) ^ (2 + a) := by
  rw [Real.rpow_add (by exact_mod_cast hN), Real.rpow_two]; ring

theorem nat_mul_rpow {N : ℕ} (hN : 1 ≤ N) (a : ℝ) :
    (N : ℝ) * (N : ℝ) ^ a = (N : ℝ) ^ (1 + a) := by
  rw [Real.rpow_add (by exact_mod_cast hN), Real.rpow_one]

/-- Class-1/3 terms at `j = ⌊log₃ N/q⌋`. -/
theorem classTerms_le {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) {c : ℝ} (hc : 0 ≤ c) :
    (N : ℝ) * ((N + 2 * 3 ^ (Nat.log 3 N / q)) * c * (2 / 3 : ℝ) ^ (Nat.log 3 N / q)) +
      N * ((2 * N + 2 * 3 ^ (Nat.log 3 N / q)) * c * (2 / 3 : ℝ) ^ (Nat.log 3 N / q)) ≤
      c * (9 / 2 * (N : ℝ) ^ (2 + Real.logb 3 (2 / 3) / q) + 4 * (N : ℝ) ^ (1 + (q : ℝ)⁻¹)) := by
  set j := Nat.log 3 N / q
  have h1 := pow_logdiv_le hq hN (α := 2 / 3) (by norm_num) (by norm_num)
  have h2 := (three_pow_logdiv hq hN).1
  have e1 : (2 / 3 : ℝ) ^ j = 3 / 2 * (2 / 3 : ℝ) ^ (j + 1) := by rw [pow_succ]; ring
  have e2 : (3 : ℝ) ^ j * (2 / 3 : ℝ) ^ j = 2 ^ j := by rw [← mul_pow]; norm_num
  have h3 : (2 : ℝ) ^ j ≤ 3 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hp : 0 ≤ (2 / 3 : ℝ) ^ (j + 1) := by positivity
  have hA : (N : ℝ) * N * (2 / 3 : ℝ) ^ j ≤ 3 / 2 * (N : ℝ) ^ (2 + Real.logb 3 (2 / 3) / q) := by
    rw [← nat_sq_rpow hN, e1]
    have : (0 : ℝ) ≤ N * N := by positivity
    nlinarith
  have hB : (N : ℝ) * (3 ^ j * (2 / 3 : ℝ) ^ j) ≤ (N : ℝ) ^ (1 + (q : ℝ)⁻¹) := by
    rw [← nat_mul_rpow hN, e2]
    exact mul_le_mul_of_nonneg_left (h3.trans h2) hN0
  have : (N : ℝ) * ((N + 2 * 3 ^ j) * c * (2 / 3 : ℝ) ^ j) +
      N * ((2 * N + 2 * 3 ^ j) * c * (2 / 3 : ℝ) ^ j) =
      c * (3 * ((N : ℝ) * N * (2 / 3 : ℝ) ^ j) + 4 * ((N : ℝ) * (3 ^ j * (2 / 3 : ℝ) ^ j))) := by ring
  rw [this]
  apply mul_le_mul_of_nonneg_left _ hc
  linarith

/-- Top-window and error terms at `W = K = j + 1`. -/
theorem topTerms_le {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N) (Cb κ : ℝ) :
    2 * (N : ℝ) * (3 * N * (2 / 3 : ℝ) ^ (Nat.log 3 N / q + 1) +
        4 * N * (1 / 3 : ℝ) ^ (Nat.log 3 N / q + 1) +
        Cb * 9 ^ (Nat.log 3 N / q + 1) * (N : ℝ) ^ (1 - κ)) +
      N * N * (Real.pi * (8 / 3 ^ (Nat.log 3 N / q + 1))) ≤
      6 * (N : ℝ) ^ (2 + Real.logb 3 (2 / 3) / q) + (8 + 8 * Real.pi) * (N : ℝ) ^ (2 - (q : ℝ)⁻¹) +
        18 * |Cb| * (N : ℝ) ^ (2 + 2 * (q : ℝ)⁻¹ - κ) := by
  set j := Nat.log 3 N / q
  have h1 := pow_logdiv_le hq hN (α := 2 / 3) (by norm_num) (by norm_num)
  have h1' := pow_logdiv_le hq hN (α := 1 / 3) (by norm_num) (by norm_num)
  have hl : Real.logb 3 (1 / 3) = -1 := by
    rw [one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]
  rw [hl] at h1'
  have h2 := (three_pow_logdiv hq hN).1
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hNN : (0 : ℝ) ≤ N * N := by positivity
  have e3 : (8 : ℝ) / 3 ^ (j + 1) = 8 * (1 / 3 : ℝ) ^ (j + 1) := by rw [one_div_pow]; ring
  have h9 : (9 : ℝ) ^ (j + 1) ≤ 9 * (N : ℝ) ^ (2 * (q : ℝ)⁻¹) := by
    have : (9 : ℝ) ^ (j + 1) = 9 * ((3 : ℝ) ^ j) ^ 2 := by
      rw [pow_succ, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring
    rw [this, mul_comm (2 : ℝ), Real.rpow_mul hN0, Real.rpow_two]
    have : ((3 : ℝ) ^ j) ^ 2 ≤ ((N : ℝ) ^ (q : ℝ)⁻¹) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    nlinarith
  have hA : (N : ℝ) * N * (2 / 3 : ℝ) ^ (j + 1) ≤ (N : ℝ) ^ (2 + Real.logb 3 (2 / 3) / q) := by
    rw [← nat_sq_rpow hN]; exact mul_le_mul_of_nonneg_left h1 hNN
  have hB : (N : ℝ) * N * (1 / 3 : ℝ) ^ (j + 1) ≤ (N : ℝ) ^ (2 - (q : ℝ)⁻¹) := by
    rw [show (2 : ℝ) - (q : ℝ)⁻¹ = 2 + -1 / q by ring, ← nat_sq_rpow hN]
    exact mul_le_mul_of_nonneg_left h1' hNN
  have hC : (N : ℝ) * (Cb * 9 ^ (j + 1) * (N : ℝ) ^ (1 - κ)) ≤
      9 * |Cb| * (N : ℝ) ^ (2 + 2 * (q : ℝ)⁻¹ - κ) := by
    have e : (N : ℝ) ^ (2 + 2 * (q : ℝ)⁻¹ - κ) = N * ((N : ℝ) ^ (2 * (q : ℝ)⁻¹) * (N : ℝ) ^ (1 - κ)) := by
      rw [rpow_mul_rpow_nat hN, nat_mul_rpow hN]; ring_nf
    rw [e]
    have hr : (0 : ℝ) ≤ (N : ℝ) ^ (1 - κ) := by positivity
    have h99 : (0 : ℝ) ≤ 9 ^ (j + 1) := by positivity
    have : Cb * 9 ^ (j + 1) ≤ |Cb| * (9 * (N : ℝ) ^ (2 * (q : ℝ)⁻¹)) :=
      (mul_le_mul_of_nonneg_right (le_abs_self Cb) h99).trans
        (mul_le_mul_of_nonneg_left h9 (abs_nonneg _))
    have := mul_le_mul_of_nonneg_right this hr
    have := mul_le_mul_of_nonneg_left this hN0
    nlinarith
  have : 2 * (N : ℝ) * (3 * N * (2 / 3 : ℝ) ^ (j + 1) + 4 * N * (1 / 3 : ℝ) ^ (j + 1) +
        Cb * 9 ^ (j + 1) * (N : ℝ) ^ (1 - κ)) + N * N * (Real.pi * (8 / 3 ^ (j + 1))) =
      6 * ((N : ℝ) * N * (2 / 3 : ℝ) ^ (j + 1)) + (8 + 8 * Real.pi) * ((N : ℝ) * N * (1 / 3 : ℝ) ^ (j + 1)) +
        2 * ((N : ℝ) * (Cb * 9 ^ (j + 1) * (N : ℝ) ^ (1 - κ))) := by rw [e3]; ring
  rw [this]
  have hpi : 0 ≤ 8 + 8 * Real.pi := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hB hpi]

/-- **Copy-run total, power form.**  The copy-run sum in `repPairPos_explicit` (runs
`k ≤ log₄(2sN+e)` with `a_k ≤ 2sN+e`) is `O(N^{2−δ})`: `O(log N)` runs, each of length
`≤ Nmax = O(N log N)`, each bounded by `copy5_total_le`/`copy6_total_le`. -/
theorem copyTotal_le {s t e h' : ℕ} (hs : 1 ≤ s) (hh : 1 ≤ h') (hT : TOrbitCyclicDecay t)
    (hS : BadGcdSparseH (3 ^ s * t)) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ k ∈ (Finset.range (Nat.log 4 (s * (2 * N) + e) + 1)).filter
          (fun k => runStart k ≤ s * (2 * N) + e),
        ∑ n ∈ Finset.range ((k + 2) * runStart k + 1),
          ∑ m ∈ Finset.range ((k + 2) * runStart k + 1),
            (cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ m))
              + cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ n)) ≤ C * (N : ℝ) ^ (2 - δ) := by
  have hh0 : (h' : ℤ) ≠ 0 := by exact_mod_cast (by omega : h' ≠ 0)
  obtain ⟨C5, δ5, hδ5, hC5⟩ := copy5_total_le (copyZoneDecayH_of hT hS (h' : ℤ) hh0)
  obtain ⟨C6, δ6, hδ6, hC6⟩ := copy6_total_le hT
  set δc := min (min δ5 δ6) 1 with hδc
  have hδc0 : 0 < δc := lt_min (lt_min hδ5 hδ6) one_pos
  have hδc1 : δc ≤ 1 := min_le_right _ _
  set ε := δc / 6
  have hε : 0 < ε := by positivity
  obtain ⟨A, hA, hAN⟩ := natLog_lin_le_rpow (b := 4) (by norm_num) hε (2 * s) e
  set S6 : ℝ := ∑ k ∈ Finset.range (h' ^ 2), ((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2
  have hS6 : 0 ≤ S6 := Finset.sum_nonneg fun _ _ => by positivity
  set B : ℝ := A * (2 * s + e) + 1
  have hB1 : 1 ≤ B := by simp only [B]; nlinarith [(Nat.cast_nonneg s : (0:ℝ) ≤ s), (Nat.cast_nonneg e : (0:ℝ) ≤ e)]
  refine ⟨A * (|C5| + |C6|) * B ^ (2 - δc) + S6, δc / 2, by positivity, fun N hN => ?_⟩
  set L := Nat.log 4 (s * (2 * N) + e)
  set Ks := (Finset.range (L + 1)).filter (fun k => runStart k ≤ s * (2 * N) + e)
  set Nmax := (L + 2) * (s * (2 * N) + e) + 1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNε : (1 : ℝ) ≤ (N : ℝ) ^ ε := Real.one_le_rpow hN1 hε.le
  have hLA : (L : ℝ) + 2 ≤ A * (N : ℝ) ^ ε := by
    have := hAN N hN; rwa [show 2 * s * N + e = s * (2 * N) + e by ring] at this
  have hKs : ∀ k ∈ Ks, (k + 2) * runStart k + 1 ≤ Nmax := by
    intro k hk
    simp only [Ks, Finset.mem_filter, Finset.mem_range] at hk
    have : (k + 2) * runStart k ≤ (L + 2) * (s * (2 * N) + e) := Nat.mul_le_mul (by omega) hk.2
    omega
  have hcard : (Ks.card : ℝ) ≤ A * (N : ℝ) ^ ε := by
    have : Ks.card ≤ L + 1 := (Finset.card_filter_le _ _).trans (by simp)
    have : (Ks.card : ℝ) ≤ L + 1 := by exact_mod_cast this
    linarith
  have hNmax1 : (1 : ℝ) ≤ Nmax := by exact_mod_cast (by omega : 1 ≤ Nmax)
  have hNmax : (Nmax : ℝ) ≤ B * (N : ℝ) ^ (1 + ε) := by
    rw [← nat_mul_rpow hN]
    simp only [Nmax, B]; push_cast
    have h1 : (2 * (s : ℝ) * N + e) ≤ (2 * s + e) * N := by nlinarith [(Nat.cast_nonneg e : (0:ℝ) ≤ e)]
    have h2 : ((L : ℝ) + 2) * (s * (2 * N) + e) ≤ A * (N : ℝ) ^ ε * ((2 * s + e) * N) :=
      mul_le_mul hLA (by linarith) (by positivity) (by positivity)
    have h3 : (1 : ℝ) ≤ N * (N : ℝ) ^ ε := by nlinarith
    nlinarith
  -- per-run bound with exponent `2 − δc`
  have hpow : ∀ δ' : ℝ, δc ≤ δ' → (Nmax : ℝ) ^ (2 - δ') ≤ B ^ (2 - δc) * (N : ℝ) ^ ((1 + ε) * (2 - δc)) := by
    intro δ' hδ'
    calc (Nmax : ℝ) ^ (2 - δ') ≤ (Nmax : ℝ) ^ (2 - δc) :=
          Real.rpow_le_rpow_of_exponent_le hNmax1 (by linarith)
      _ ≤ (B * (N : ℝ) ^ (1 + ε)) ^ (2 - δc) :=
          Real.rpow_le_rpow (by positivity) hNmax (by linarith)
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
  have h5 := hC5 Ks Nmax hKs
  have h6 := hC6 (h' : ℤ) hh0 (h' ^ 2) (fun k hk => by
    have hk' : h' ^ 2 ≤ runStart k := hk.trans (lt_runStart k).le
    have : runStart k < 3 ^ runStart k := Nat.lt_pow_self (by norm_num)
    have h7 : ((h' ^ 2 + 1 : ℕ) : ℝ) ≤ ((3 ^ runStart k : ℕ) : ℝ) := by exact_mod_cast (by omega)
    push_cast at h7
    rw [Int.natAbs_natCast]; linarith) Ks Nmax hKs
  rw [show ∑ k ∈ Ks, ∑ n ∈ Finset.range ((k + 2) * runStart k + 1),
      ∑ m ∈ Finset.range ((k + 2) * runStart k + 1),
        (cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ m))
          + cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ n)) =
    ∑ k ∈ Ks, ∑ n ∈ Finset.range ((k + 2) * runStart k + 1),
      ∑ m ∈ Finset.range ((k + 2) * runStart k + 1),
        cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ m)) +
    ∑ k ∈ Ks, ∑ n ∈ Finset.range ((k + 2) * runStart k + 1),
      ∑ _m ∈ Finset.range ((k + 2) * runStart k + 1), cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ n) by
    simp only [Finset.sum_add_distrib]]
  have p5 := hpow δ5 (le_trans (min_le_left _ _) (min_le_left _ _))
  have p6 := hpow δ6 (le_trans (min_le_left _ _) (min_le_right _ _))
  -- exponent bookkeeping
  have hexp : (N : ℝ) ^ ε * (N : ℝ) ^ ((1 + ε) * (2 - δc)) ≤ (N : ℝ) ^ (2 - δc / 2) := by
    rw [rpow_mul_rpow_nat hN]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    simp only [ε]; nlinarith
  have hc0 : (0 : ℝ) ≤ Ks.card := by positivity
  have hP : 0 ≤ B ^ (2 - δc) * (N : ℝ) ^ ((1 + ε) * (2 - δc)) := by positivity
  have k5 : (Ks.card : ℝ) * (|C5| * (Nmax : ℝ) ^ (2 - δ5)) ≤
      A * |C5| * B ^ (2 - δc) * (N : ℝ) ^ (2 - δc / 2) := by
    calc (Ks.card : ℝ) * (|C5| * (Nmax : ℝ) ^ (2 - δ5)) ≤
        (A * (N : ℝ) ^ ε) * (|C5| * (B ^ (2 - δc) * (N : ℝ) ^ ((1 + ε) * (2 - δc)))) :=
          mul_le_mul hcard (mul_le_mul_of_nonneg_left p5 (abs_nonneg _)) (by positivity) (by positivity)
      _ = A * |C5| * B ^ (2 - δc) * ((N : ℝ) ^ ε * (N : ℝ) ^ ((1 + ε) * (2 - δc))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
  have k6 : (Ks.card : ℝ) * (|C6| * (Nmax : ℝ) ^ (2 - δ6)) ≤
      A * |C6| * B ^ (2 - δc) * (N : ℝ) ^ (2 - δc / 2) := by
    calc (Ks.card : ℝ) * (|C6| * (Nmax : ℝ) ^ (2 - δ6)) ≤
        (A * (N : ℝ) ^ ε) * (|C6| * (B ^ (2 - δc) * (N : ℝ) ^ ((1 + ε) * (2 - δc)))) :=
          mul_le_mul hcard (mul_le_mul_of_nonneg_left p6 (abs_nonneg _)) (by positivity) (by positivity)
      _ = A * |C6| * B ^ (2 - δc) * ((N : ℝ) ^ ε * (N : ℝ) ^ ((1 + ε) * (2 - δc))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
  have hS6N : S6 ≤ S6 * (N : ℝ) ^ (2 - δc / 2) :=
    le_mul_of_one_le_right hS6 (Real.one_le_rpow hN1 (by linarith))
  nlinarith

/-- **Bad-pair term, power form.**  `N(c₀ + J + 8(3J+1)(log₄(aN + c + 2J) + 1)) = O(N^{3/2})`,
`J = ⌊log₃N/q⌋ + 1`. -/
theorem badTerm_le {q : ℕ} (hq : 1 ≤ q) (c₀ a c : ℕ) :
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ((N * (c₀ + (Nat.log 3 N / q + 1) + 4 * (2 * ((Nat.log 3 N / q + 1) +
        2 * (Nat.log 3 N / q + 1) + 1) * (Nat.log 4 (a * N + c + (Nat.log 3 N / q + 1) +
          (Nat.log 3 N / q + 1)) + 1))) : ℕ) : ℝ) ≤ C * (N : ℝ) ^ ((3 : ℝ) / 2) := by
  obtain ⟨A1, hA1, h1⟩ := natLog_lin_le_rpow (b := 3) (by norm_num) (ε := 1 / 4) (by norm_num) 1 0
  obtain ⟨A2, hA2, h2⟩ := natLog_lin_le_rpow (b := 4) (by norm_num) (ε := 1 / 4) (by norm_num)
    (a + 4) c
  refine ⟨c₀ + A1 + 32 * A1 * A2, fun N hN => ?_⟩
  set j := Nat.log 3 N / q
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hjN : j ≤ Nat.log 3 N := Nat.div_le_self _ _
  have hlN : Nat.log 3 N < N := Nat.log_lt_self 3 (by omega)
  have hJ : ((j + 1 : ℕ) : ℝ) ≤ A1 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    have := h1 N hN; simp only [one_mul, add_zero] at this
    have : ((j + 1 : ℕ) : ℝ) ≤ (Nat.log 3 N : ℝ) + 2 := by push_cast; exact_mod_cast (by omega : j + 1 ≤ Nat.log 3 N + 2)
    linarith
  have hLg : ((Nat.log 4 (a * N + c + (j + 1) + (j + 1)) + 1 : ℕ) : ℝ) ≤ A2 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
    have hmono : Nat.log 4 (a * N + c + (j + 1) + (j + 1)) ≤ Nat.log 4 ((a + 4) * N + c) :=
      Nat.log_mono_right (by nlinarith)
    have := h2 N hN
    have : ((Nat.log 4 (a * N + c + (j + 1) + (j + 1)) + 1 : ℕ) : ℝ) ≤ (Nat.log 4 ((a + 4) * N + c) : ℝ) + 2 := by
      push_cast; exact_mod_cast (by omega)
    linarith
  have hq4 : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := Real.one_le_rpow hN1 (by norm_num)
  have hq2 : (N : ℝ) ^ ((1 : ℝ) / 4) * (N : ℝ) ^ ((1 : ℝ) / 4) = (N : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [rpow_mul_rpow_nat hN]; norm_num
  have e32 : (N : ℝ) * (N : ℝ) ^ ((1 : ℝ) / 2) = (N : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [nat_mul_rpow hN]; norm_num
  set u := (N : ℝ) ^ ((1 : ℝ) / 4)
  set J : ℝ := ((j + 1 : ℕ) : ℝ)
  set G : ℝ := ((Nat.log 4 (a * N + c + (j + 1) + (j + 1)) + 1 : ℕ) : ℝ)
  have hJ0 : 0 ≤ J := by positivity
  have hG0 : 0 ≤ G := by positivity
  have hcast : ((N * (c₀ + (j + 1) + 4 * (2 * ((j + 1) + 2 * (j + 1) + 1) *
      (Nat.log 4 (a * N + c + (j + 1) + (j + 1)) + 1))) : ℕ) : ℝ) =
      N * (c₀ + J + 8 * (3 * J + 1) * G) := by simp only [J, G]; push_cast; ring
  rw [hcast, ← e32, ← hq2]
  have hc0 : (0 : ℝ) ≤ c₀ := by positivity
  have k1 : J ≤ A1 * (u * u) := by nlinarith
  have hA1u : 2 ≤ A1 * u := by
    have := h1 N hN; have := (Nat.cast_nonneg (Nat.log 3 (1 * N + 0)) : (0 : ℝ) ≤ _); linarith
  have k2 : (3 * J + 1) * G ≤ (4 * A1 * u) * (A2 * u) := by
    apply mul_le_mul _ hLg hG0 (by positivity); nlinarith
  have k3 : (c₀ : ℝ) ≤ c₀ * (u * u) := le_mul_of_one_le_right hc0 (by nlinarith)
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have : c₀ + J + 8 * (3 * J + 1) * G ≤ (c₀ + A1 + 32 * A1 * A2) * (u * u) := by nlinarith
  nlinarith

theorem log_le_posBound {s t e h' N y : ℕ} (ht : 1 ≤ t)
    (hy : y ≤ 3 ^ e * h' * (3 ^ s * t) ^ (2 * N)) :
    Nat.log 3 y ≤ 3 ^ e * h' + 2 * (s + t) * N + e := by
  rcases Nat.eq_zero_or_pos y with h0 | hpos
  · simp [h0]
  have h1 : 3 ^ e * h' < 3 ^ (3 ^ e * h') := Nat.lt_pow_self (by norm_num)
  have h2 : 3 ^ s * t ≤ 3 ^ (s + t) := by
    rw [pow_add]; exact Nat.mul_le_mul_left _ (Nat.lt_pow_self (by norm_num)).le
  have h3 : (3 ^ s * t) ^ (2 * N) ≤ 3 ^ (2 * (s + t) * N) := by
    calc (3 ^ s * t) ^ (2 * N) ≤ (3 ^ (s + t)) ^ (2 * N) := Nat.pow_le_pow_left h2 _
      _ = _ := by rw [← pow_mul]; ring_nf
  have h4 : y < 3 ^ (3 ^ e * h' + 2 * (s + t) * N) := by
    rw [pow_add]
    calc y ≤ _ := hy
      _ < 3 ^ (3 ^ e * h') * 3 ^ (2 * (s + t) * N) :=
          Nat.mul_lt_mul_of_lt_of_le h1 h3 (by positivity)
  have := Nat.log_lt_of_lt_pow (by omega) h4
  omega

open Classical in
/-- **Explicit per-`N` bound.**  With `W = K = j + 1`, `ρ = t + 2`, `k₀ = ρ(ρ+1)`, positions
bounded by `X = 3ᵉh' + 2(s+t)N + e`, small-`m` cut `m₀ = 3ᵉh' + a_{k₀} + (j+1)`: the pair sum is at
most the explicit majorant below, given a top-window bound `Btop` and a copy-run bound `Copy`. -/
theorem repPairPos_explicit {s t e h' : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (h3t : ¬ 3 ∣ t)
    (hh : 1 ≤ h') (hnd : ¬ 3 ∣ h') (j N : ℕ) (Btop Copy : ℝ)
    (hBtop : ∀ β : ℝ, ∑ m ∈ Finset.range N,
      CantorExactExponentProfile.topProd (j + 1) (Int.fract (m * Real.logb 3 t + β)) ≤ Btop)
    (hCopy : ∑ k ∈ (Finset.range (Nat.log 4 (s * (2 * N) + e) + 1)).filter
          (fun k => runStart k ≤ s * (2 * N) + e),
        ∑ n ∈ Finset.range ((k + 2) * runStart k + 1),
          ∑ m ∈ Finset.range ((k + 2) * runStart k + 1),
            (cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ m))
              + cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ n)) ≤ Copy) :
    ∃ (M : ℕ) (κ : ℕ → ℕ → Option ℕ), ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      repBound M (κ n m) (((3 ^ e * h' : ℕ) : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ n -
        ((3 ^ s * t : ℕ) : ℝ) ^ m)) ≤
      N + 2 * (N * ((N + 2 * 3 ^ j) * (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t * (2 / 3 : ℝ) ^ j) +
        N * ((2 * N + 2 * 3 ^ j) * (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t * (2 / 3 : ℝ) ^ j) +
        2 * N * Btop + Copy + N * N * (Real.pi * (8 / 3 ^ (j + 1))) +
        ((N * ((3 ^ e * h' + runStart ((t + 2) * (t + 3)) + (j + 1)) +
          4 * (2 * ((j + 1) + 2 * (j + 1) + 1) *
            (Nat.log 4 ((3 ^ e * h' + 2 * (s + t) * N + e) + (j + 1) + (j + 1)) + 1))) : ℕ) : ℝ)) := by
  set X := 3 ^ e * h' + 2 * (s + t) * N + e with hXd
  set W := j + 1 with hWd
  set ρ := t + 2
  set k₀ := (t + 2) * (t + 3)
  set M := X + 2 * s * N + e + W with hMd
  have hB2 : 1 ≤ 3 ^ s * t := Nat.mul_pos (by positivity) (by omega)
  have hpos : ∀ m d, m < N → d ≤ N → 3 ^ e * h' * (3 ^ s * t) ^ (m + d) ≤
      3 ^ e * h' * (3 ^ s * t) ^ (2 * N) := fun m d hm hd =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB2 (by omega))
  have hpairle : ∀ m d, pairNat s t e h' m d ≤ 3 ^ e * h' * (3 ^ s * t) ^ (m + d) := fun m d =>
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hX : ∀ m < N, ∀ d ≤ N, s * m + e ≤ X ∧ Nat.log 3 (3 ^ e * h' * (3 ^ s * t) ^ m) ≤ X ∧
      s * (m + d) + e ≤ X ∧ Nat.log 3 (pairNat s t e h' m d) ≤ X := by
    intro m hm d hd
    have hsm : s * (m + d) ≤ 2 * (s + t) * N := by nlinarith
    have : s * m ≤ s * (m + d) := Nat.mul_le_mul_left _ (by omega)
    refine ⟨by rw [hXd]; omega, log_le_posBound (by omega) ((Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right hB2 (by omega))).trans (hpos m 0 hm (Nat.zero_le _))), by omega,
      log_le_posBound (by omega) ((hpairle m d).trans (hpos m d hm hd))⟩
  have hρ1 : 1 ≤ ρ := by omega
  have hb : 3 ^ s * t ≤ 3 ^ (s * (ρ - 1)) := by
    have : ρ - 1 = 1 + t := by omega
    rw [this, mul_add, mul_one, pow_add, pow_mul]
    refine Nat.mul_le_mul_left _ ((Nat.lt_pow_self (by norm_num : 1 < 3)).le.trans ?_)
    exact Nat.pow_le_pow_left (Nat.le_self_pow (by omega) 3) t
  have hρ : ρ * (ρ + 1) ≤ 4 * (k₀ + 3) := by simp only [ρ, k₀]; nlinarith
  have hM : ∀ m < N, ∀ d < N, s * (m + d) + e + W ≤ M ∧ Nat.log 3 (pairNat s t e h' m d) ≤ M := by
    intro m hm d hd
    have := hX m hm d hd.le
    have h1 : s * (m + d) ≤ 2 * s * N := by nlinarith
    refine ⟨by rw [hMd]; omega, by omega⟩
  obtain ⟨κ, hκ⟩ := exists_kappa_pos (k₀ := k₀) (W := W) (K := W) ht hh hs hρ1 hb hρ hM
  refine ⟨M, κ, hκ.trans ?_⟩
  have hmaj := sum_pairMaj_le (e := e) hs ht h3t hh hnd j W N M Btop hBtop
  have hbad := sum_bad_le (k₀ := k₀) (W := W) (K := W)
    (m₀ := 3 ^ e * h' + runStart k₀ + W) hs ht hh (fun m hm => by
      have hm' : m ≤ s * m := Nat.le_mul_of_pos_left _ (by omega)
      refine ⟨?_, by omega, by omega, by omega⟩
      calc 3 ^ e * h' ≤ m := by omega
        _ < 3 ^ m := Nat.lt_pow_self (by norm_num)
        _ ≤ 3 ^ (s * m) := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_left _ (by omega))) hX
  have hbadR : ∑ m ∈ Finset.range N, ∑ d ∈ Finset.Ico 1 N,
      ((if PairGood s t e h' m d k₀ W W then 0 else 1 : ℕ) : ℝ) ≤
      ((N * ((3 ^ e * h' + runStart k₀ + W) +
        4 * (2 * (W + 2 * W + 1) * (Nat.log 4 (X + W + W) + 1))) : ℕ) : ℝ) := by
    exact_mod_cast hbad
  have := hCopy
  have h2 : 0 ≤ (2 : ℝ) := by norm_num
  nlinarith

/-- **Per-`N` assembly, `h = 3ᵉh' > 0`, large `N` (proved 2026-10-07).**  The content
of `repPairPower_of_inputs`.  Route: `exists_kappa_pos` with `ρ, k₀` fixed by `b`, `W = K = j+1`,
`j = ⌊log₃ N / q⌋` (`2/q < κ_Baker`); `sum_pairMaj_le` (Btop from `sum_class_top_le`, copy totals
from `copy5_total_le`/`copy6_total_le` with `Ks` the runs `≤ log₄(2sN+e)`), `sum_bad_le`
(`m₀ = O(log N)`).  Every piece is `O(N^{2−δ})`. -/
theorem repPairPos_eventually {s t : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (h3t : ¬ 3 ∣ t)
    (hB : CantorExactExponentProfile.Literature.BakerLogDiscrepancy) (hT : TOrbitCyclicDecay t)
    (hS : BadGcdSparseH (3 ^ s * t)) (e h' : ℕ) (hh : 1 ≤ h') (hnd : ¬ 3 ∣ h') :
    ∃ C δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N → ∃ (M : ℕ) (κ : ℕ → ℕ → Option ℕ),
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        repBound M (κ n m) (((3 ^ e * h' : ℕ) : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ n -
          ((3 ^ s * t : ℕ) : ℝ) ^ m)) ≤ C * (N : ℝ) ^ (2 - δ) := by
  obtain ⟨Cb, κb, hκb, hCb⟩ := sum_class_top_le ht h3t hB
  obtain ⟨Cc, δc, hδc, hCc⟩ := copyTotal_le (e := e) hs hh hT hS
  set q : ℕ := ⌈4 / κb⌉₊ + 2 with hqd
  have hq : 1 ≤ q := by omega
  have hq2 : (2 : ℝ) ≤ q := by simp only [hqd]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈4 / κb⌉₊]
  have hqκ : 4 / κb ≤ q := by
    simp only [hqd]; push_cast; linarith [Nat.le_ceil (4 / κb)]
  have hq0 : (0 : ℝ) < q := by linarith
  obtain ⟨Cd, hCd⟩ := badTerm_le hq (3 ^ e * h' + runStart ((t + 2) * (t + 3))) (2 * (s + t))
    (3 ^ e * h' + e)
  have hlg : Real.logb 3 (2 / 3) < 0 := Real.logb_neg (by norm_num) (by norm_num) (by norm_num)
  set η : ℝ := -(Real.logb 3 (2 / 3)) / q
  have hη : 0 < η := div_pos (by linarith) hq0
  set δ : ℝ := min (min η (q : ℝ)⁻¹) (min (κb / 2) (min δc (1 / 4)))
  have hδ0 : 0 < δ := lt_min (lt_min hη (by positivity)) (lt_min (by positivity) (lt_min hδc (by norm_num)))
  have hδη : δ ≤ η := (min_le_left _ _).trans (min_le_left _ _)
  have hδq : δ ≤ (q : ℝ)⁻¹ := (min_le_left _ _).trans (min_le_right _ _)
  have hδκ : δ ≤ κb / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδc' : δ ≤ δc := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ4 : δ ≤ 1 / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hqinv : (q : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hq0 (by norm_num)]; linarith
  have h2q : 2 * (q : ℝ)⁻¹ ≤ κb / 2 := by
    have : 4 ≤ κb * q := by rwa [div_le_iff₀ hκb, mul_comm] at hqκ
    rw [← div_eq_mul_inv, div_le_iff₀ hq0]; nlinarith
  set cc : ℝ := (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t
  have hcc : 0 ≤ cc := by positivity
  refine ⟨1 + 2 * (cc * (9 / 2 + 4) + 6 + (8 + 8 * Real.pi) + 18 * |Cb| + |Cc| + |Cd|), δ, hδ0,
    1, fun N _ hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have mono : ∀ a : ℝ, a ≤ 2 - δ → (N : ℝ) ^ a ≤ (N : ℝ) ^ (2 - δ) :=
    fun a ha => Real.rpow_le_rpow_of_exponent_le hN1 ha
  set j := Nat.log 3 N / q
  set Btop : ℝ := 3 * N * (2 / 3 : ℝ) ^ (j + 1) + 4 * N * (1 / 3 : ℝ) ^ (j + 1) +
    Cb * 9 ^ (j + 1) * (N : ℝ) ^ (1 - κb)
  have hBtop : ∀ β : ℝ, ∑ m ∈ Finset.range N,
      CantorExactExponentProfile.topProd (j + 1) (Int.fract (m * Real.logb 3 t + β)) ≤ Btop := by
    intro β
    have := hCb N hN (j + 1) 1 (fun _ => β)
    simp only [Finset.sum_range_one, Nat.cast_one, one_mul] at this; exact this
  obtain ⟨M, κ, hMκ⟩ := repPairPos_explicit hs ht h3t hh hnd j N Btop (Cc * (N : ℝ) ^ (2 - δc))
    hBtop (hCc N hN)
  refine ⟨M, κ, hMκ.trans ?_⟩
  have e1 : 3 ^ e * h' + 2 * (s + t) * N + e = 2 * (s + t) * N + (3 ^ e * h' + e) := by ring
  rw [e1]
  have hcl := classTerms_le hq hN hcc
  have htop := topTerms_le hq hN Cb κb
  have hbad := hCd N hN
  -- exponents
  have x1 := mono (2 + Real.logb 3 (2 / 3) / q) (by
    have : Real.logb 3 (2 / 3) / q = -η := by simp only [η]; ring
    rw [this]; linarith)
  have x2 := mono (1 + (q : ℝ)⁻¹) (by linarith)
  have x3 := mono (2 - (q : ℝ)⁻¹) (by linarith)
  have x4 := mono (2 + 2 * (q : ℝ)⁻¹ - κb) (by linarith)
  have x5 := mono (2 - δc) (by linarith)
  have x6 := mono (3 / 2) (by linarith)
  have x7 := mono 1 (by linarith)
  rw [Real.rpow_one] at x7
  have hP : 0 ≤ (N : ℝ) ^ (2 - δ) := by positivity
  have hpi : 0 ≤ 8 + 8 * Real.pi := by positivity
  have y1 : cc * (9 / 2 * (N : ℝ) ^ (2 + Real.logb 3 (2 / 3) / q) + 4 * (N : ℝ) ^ (1 + (q : ℝ)⁻¹)) ≤
      cc * (9 / 2 + 4) * (N : ℝ) ^ (2 - δ) := by
    rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hcc; linarith
  have y2 : 6 * (N : ℝ) ^ (2 + Real.logb 3 (2 / 3) / q) + (8 + 8 * Real.pi) * (N : ℝ) ^ (2 - (q : ℝ)⁻¹) +
      18 * |Cb| * (N : ℝ) ^ (2 + 2 * (q : ℝ)⁻¹ - κb) ≤
      (6 + (8 + 8 * Real.pi) + 18 * |Cb|) * (N : ℝ) ^ (2 - δ) := by
    have := mul_le_mul_of_nonneg_left x3 hpi
    have := mul_le_mul_of_nonneg_left x4 (by positivity : (0 : ℝ) ≤ 18 * |Cb|)
    nlinarith
  have y3 : Cc * (N : ℝ) ^ (2 - δc) ≤ |Cc| * (N : ℝ) ^ (2 - δ) :=
    (mul_le_mul_of_nonneg_right (le_abs_self Cc) (by positivity)).trans
      (mul_le_mul_of_nonneg_left x5 (abs_nonneg _))
  have y4 : Cd * (N : ℝ) ^ ((3 : ℝ) / 2) ≤ |Cd| * (N : ℝ) ^ (2 - δ) :=
    (mul_le_mul_of_nonneg_right (le_abs_self Cd) (by positivity)).trans
      (mul_le_mul_of_nonneg_left x6 (abs_nonneg _))
  have htop' : 2 * (N : ℝ) * Btop + N * N * (Real.pi * (8 / 3 ^ (j + 1))) ≤
      6 * (N : ℝ) ^ (2 + Real.logb 3 (2 / 3) / q) + (8 + 8 * Real.pi) * (N : ℝ) ^ (2 - (q : ℝ)⁻¹) +
        18 * |Cb| * (N : ℝ) ^ (2 + 2 * (q : ℝ)⁻¹ - κb) := htop
  clear_value Btop
  linarith

/-- **Per-`N` assembly (open; believed, 60%; the remaining content of `repPairArith_of_inputs`).**
Plan: `W = K = ⌈ε log₃ N⌉`; `κ` per `pair_classify_rep` (hypotheses: `le_log_mul_pow`,
`log_mul_pow_lt`, `le_log_pair`, `log_pair_le_log`, `hsep_of`); class sums `sum_class_low_le`,
`sum_class_top_le`, `sum_class_sep_le`, `sum_class_copy_le`, `sum_class_copySep_le` (range glue
`runEnd_succ_le_cube`, `≤ log₄ N` runs); band pairs `card_nearCopyBdry_le`, small `m` and the
diagonal bounded by `1`; general `h = 3^e h'` shifts every window by `e`. -/
theorem repPairPower_of_inputs {s t : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (h3t : ¬ 3 ∣ t)
    (hB : CantorExactExponentProfile.Literature.BakerLogDiscrepancy) (hT : TOrbitCyclicDecay t)
    (hS : BadGcdSparseH (3 ^ s * t)) : RepPairPower (3 ^ s * t) :=
  repPairPower_of_pos fun e h' h1 hnd =>
    power_of_eventually _ (repPairPos_eventually hs ht h3t hB hT hS e h' h1 hnd)

/-- **Assembly of the crux from its inputs (PROVED 2026-10-07; axiom-clean modulo its hypotheses).**  For `b = 3ˢt`, `t > 1`:
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
A positive fraction of `m` falls here.  RESOLVED by construction (2026-10-07): only even runs
copy (`src`), so the free stretch after copy run `k` is `[E_k, a_{k+2})`, ratio `4(k+3) → ∞`, and
for each `b` eventually every window starting in run `k` tops out in that stretch.  (The odd
run inside the stretch carries fresh coins, but those are not `isFree`; the top-window bound
must use the fresh-coin set `isFree ∨ odd run`, not `Bf isFree`.)  Numerically the class is harmless
(`scripts/rep_arith.py 12 300,380`: `N⁻²Σ = .0034, .0027`, the `1/N` floor, and `N = 380` reaches
the gap-spanning windows `n ≥ 340` of run 2; `b = 6`, `N = 300`: `.0034`): a proof-plan gap,
not evidence against `RepPairArith`. -/
theorem repPairArith_of_inputs {s t : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (h3t : ¬ 3 ∣ t)
    (hB : CantorExactExponentProfile.Literature.BakerLogDiscrepancy) (hT : TOrbitCyclicDecay t)
    (hS : BadGcdSparseH (3 ^ s * t)) : RepPairArith (3 ^ s * t) :=
  repPairArith_of_power (repPairPower_of_inputs hs ht h3t hB hT hS)

/-! ### The copy zone through sparse pairs (review lap 7, 2026-10-07)

`TOrbitCyclicDecay` asks for a power saving, which is an open digits-of-powers problem; the
assembly needs only a saving summable along `sched`.  Route (`SparseIdentity`):
* a residue with large `cycProd` is cyclically sparse (`cycSparse_of_cycProd_ge`, via
  `card_changes_lt`: `2y = 3y − y ≡ Σ (dg_{i+1} − dg_i) 3^{P−1−i}`);
* two sparse points `c tᵐ`, `c tᵐ⁺ᵟ` of one orbit with `t^δ + 2 ≤ 3^{⌊A/(2K+1)⌋}` give an exact
  sparse identity `tᵟ U = V` (`SparseIdentity.cyclic_pair_identity`, proved), hence `δ ≤ L_K`
  (`SparseIdentity.SparseIdentityBound`, from Matveev);
* so sparse points of an orbit cluster (`card_cluster_le`) and the run orbit sums are
  `≤ N θ + (N/D + 1)(L_K + 1)` with `D ≍ A/(K log₃ t)`, `N/D = O(K k log t)` (`RunOrbitDecay`).
`BadGcdSparseH` is not needed: only fully degenerate rows (`3^A − 1 ∣ 2 c t^N`) escape, and they
are counted elementarily (`card_degRows_le`). -/

section CycSparse
open Finset

theorem dg_period {P y : ℕ} (hP : 1 ≤ P) : dg P y P = dg P y 0 := by
  have hq1 : (1 : ℝ) < 3 ^ P := one_lt_pow₀ (by norm_num) (by omega)
  have : (3 : ℝ) ^ P * ((y : ℝ) / (3 ^ P - 1)) = (y : ℝ) / (3 ^ P - 1) + ((y : ℤ) : ℝ) := by
    have hq : (3 : ℝ) ^ P - 1 ≠ 0 := by linarith
    field_simp; push_cast; ring
  simp only [dg, rd, this, Int.fract_add_intCast, pow_zero, one_mul]

theorem dg_bounds (P y i : ℕ) : 0 ≤ dg P y i ∧ dg P y i ≤ 2 :=
  ⟨rd_nonneg _, by have := rd_lt (3 ^ i * ((y : ℝ) / (3 ^ P - 1))); simp only [dg]; omega⟩

theorem two_mul_eq_sum {Q y : ℕ} (hy : y < 3 ^ (Q + 1) - 1) :
    2 * (y : ℤ) = ∑ j ∈ range (Q + 1), (dg (Q + 1) y (j + 1) - dg (Q + 1) y j) * 3 ^ (Q - j) +
      dg (Q + 1) y 0 * (3 ^ (Q + 1) - 1) := by
  have hr := eq_sum_rd (P := Q + 1) (by omega) hy
  have hz : (y : ℤ) = ∑ i ∈ range (Q + 1), dg (Q + 1) y i * 3 ^ (Q - i) := by
    have : ((y : ℤ) : ℝ) = ((∑ i ∈ range (Q + 1), dg (Q + 1) y i * 3 ^ (Q - i) : ℤ) : ℝ) := by
      push_cast; rw [hr]; refine sum_congr rfl fun i _ => ?_; simp [dg]
    exact_mod_cast this
  set D := dg (Q + 1) y
  have hper : D (Q + 1) = D 0 := dg_period (by omega)
  -- 3y
  have h3 : 3 * (y : ℤ) = D 0 * 3 ^ (Q + 1) + ∑ j ∈ range Q, D (j + 1) * 3 ^ (Q - j) := by
    rw [hz, mul_sum, sum_range_succ']
    simp only [Nat.sub_zero]
    rw [add_comm, pow_succ]
    congr 1
    · ring
    · refine sum_congr rfl fun j hj => ?_
      have : Q - j = (Q - (j + 1)) + 1 := by have := mem_range.1 hj; omega
      rw [this, pow_succ]; ring
  have h4 : ∑ j ∈ range (Q + 1), D (j + 1) * 3 ^ (Q - j) =
      ∑ j ∈ range Q, D (j + 1) * 3 ^ (Q - j) + D 0 := by
    rw [sum_range_succ, Nat.sub_self, pow_zero, mul_one, hper]
  simp only [sub_mul, sum_sub_distrib, h4, ← hz]
  linarith

/-- **Large cyclic product forces cyclic sparsity.**  If `cos(π/9)^K < θ ≤ cycProd P η`, then `η`
is cyclically `K`-sparse modulo `3^P − 1`. -/
theorem cycSparse_of_cycProd_ge {P K : ℕ} (hP : 1 ≤ P) {θ : ℝ}
    (hK : Real.cos (Real.pi / 9) ^ K < θ) (η : ℤ) (hη : θ ≤ cycProd P η) :
    SparseIdentity.CycSparse P K η := by
  obtain ⟨Q, rfl⟩ : ∃ Q, P = Q + 1 := ⟨P - 1, by omega⟩
  set q : ℤ := 3 ^ (Q + 1) - 1 with hqdef
  have hq : 0 < q := by
    have : (1 : ℤ) < 3 ^ (Q + 1) := one_lt_pow₀ (by norm_num) (by omega)
    omega
  set y : ℕ := (η % q).toNat
  have hy0 : (y : ℤ) = η % q := Int.toNat_of_nonneg (Int.emod_nonneg _ hq.ne')
  have hyq : (y : ℤ) < q := hy0 ▸ Int.emod_lt_of_pos _ hq
  have hy : y < 3 ^ (Q + 1) - 1 := by
    have : ((3 ^ (Q + 1) - 1 : ℕ) : ℤ) = q := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]; push_cast; rfl
    omega
  have hηy : η = (y : ℤ) + (η / q) * (3 ^ (Q + 1) - 1) := by
    rw [hy0]; have := Int.emod_def η q; linarith
  have hcyc : θ ≤ cycProd (Q + 1) (y : ℤ) := by
    rw [hηy, cycProd_add] at hη; exact hη
  have hcard := card_changes_lt hK hcyc
  set C := (range (Q + 1)).filter fun i => dg (Q + 1) y i ≠ dg (Q + 1) y (i + 1)
  set D := dg (Q + 1) y
  refine ⟨C.image (fun j => Q - j), fun e => D (Q - e + 1) - D (Q - e), ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨j, -, rfl⟩ := mem_image.1 he
    exact mem_range.2 (by omega)
  · exact card_image_le.trans hcard.le
  · intro e he
    obtain ⟨j, hj, rfl⟩ := mem_image.1 he
    have hjr := mem_range.1 (mem_filter.1 hj).1
    have hjc := (mem_filter.1 hj).2
    have hQ : Q - (Q - j) = j := by omega
    dsimp only; rw [hQ]
    have h1 : 0 ≤ D j ∧ D j ≤ 2 := dg_bounds _ _ _
    have h2 : 0 ≤ D (j + 1) ∧ D (j + 1) ≤ 2 := dg_bounds _ _ _
    refine ⟨sub_ne_zero.2 (Ne.symm hjc), abs_le.2 ⟨by omega, by omega⟩⟩
  · have hinj : Set.InjOn (fun j => Q - j) C := by
      intro a ha b hb h
      have := mem_range.1 (mem_filter.1 ha).1; have := mem_range.1 (mem_filter.1 hb).1
      simp only at h; omega
    rw [sum_image hinj]
    have h2 := two_mul_eq_sum hy
    have hsum : ∑ j ∈ range (Q + 1), (D (j + 1) - D j) * 3 ^ (Q - j) =
        ∑ j ∈ C, (D (Q - (Q - j) + 1) - D (Q - (Q - j))) * 3 ^ (Q - j) := by
      rw [sum_filter]
      refine sum_congr rfl fun j hj => ?_
      have : Q - (Q - j) = j := by have := mem_range.1 hj; omega
      rw [this]
      split_ifs with h
      · rfl
      · have h' : D (j + 1) = D j := (not_not.1 h).symm
        rw [h', sub_self, zero_mul]
    rw [← hsum]
    have : 2 * η = 2 * (y : ℤ) + 2 * (η / q) * (3 ^ (Q + 1) - 1) := by linear_combination 2 * hηy
    rw [this, h2, Int.modEq_iff_dvd]
    exact ⟨-(D 0 + 2 * (η / q)), by ring⟩

end CycSparse

/-- **Cluster count (pure combinatorics).**  A set `B ⊆ [0, N)` any two of whose points within
distance `D` are within distance `L < D` has at most `(N/D + 1)(L + 1)` points. -/
theorem card_cluster_le {N D L : ℕ} (hLD : L < D) (B : Finset ℕ) (hB : B ⊆ Finset.range N)
    (hcl : ∀ m ∈ B, ∀ m' ∈ B, m < m' → m' - m ≤ D → m' - m ≤ L) :
    B.card ≤ (N / D + 1) * (L + 1) := by
  have hD : 0 < D := by omega
  rw [Finset.card_eq_sum_card_fiberwise (f := fun m => m / D) (t := Finset.range (N / D + 1))
    (fun m hm => Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right (Finset.mem_range.1 (hB hm)).le)))]
  refine (Finset.sum_le_sum fun i _ => ?_).trans (by rw [Finset.sum_const, Finset.card_range, smul_eq_mul])
  set F := B.filter fun m => m / D = i
  rcases F.eq_empty_or_nonempty with h | hne
  · rw [h]; simp
  set m0 := F.min' hne
  have hm0 := Finset.mem_filter.1 (F.min'_mem hne)
  have hsub : F ⊆ Finset.Icc m0 (m0 + L) := by
    intro m hm
    have hle : m0 ≤ m := F.min'_le m hm
    have hmF := Finset.mem_filter.1 hm
    have hlt : m - m0 < D := by
      have h1 := Nat.div_add_mod m D; have h2 := Nat.div_add_mod m0 D
      have := Nat.mod_lt m hD; have := Nat.mod_lt m0 hD
      rw [hmF.2] at h1; rw [hm0.2] at h2
      have : D * i ≤ m0 := by omega
      omega
    rcases hle.lt_or_eq with h | h
    · exact Finset.mem_Icc.2 ⟨hle, by have := hcl m0 hm0.1 m hmF.1 h hlt.le; omega⟩
    · exact Finset.mem_Icc.2 ⟨hle, by omega⟩
  exact (Finset.card_le_card hsub).trans (by simp; omega)

/-- **Run orbit decay (the copy-zone node of the sparse-pair route).**  For the runs
`A = a_k`, `N_k = (k+2)a_k + 1`, the orbit sums `Σ_{m < N_k} cycProd a_k (c tᵐ)` are `≤ N_k ψ_k`
for every non-degenerate `c` (`3^{a_k} − 1 ∤ 2 c t^{N_k}`), with `Σ ψ_k (k+3)⁴ < ∞`.  Weaker than
`TOrbitCyclicDecay` (no power saving, but no gcd hypothesis and no `BadGcdSparseH`). -/
def RunOrbitDecay (t : ℕ) : Prop :=
  ∃ ψ : ℕ → ℝ, (∀ k, 0 ≤ ψ k) ∧ Summable (fun k => ψ k * ((k : ℝ) + 3) ^ 4) ∧ ∃ k₁ : ℕ,
    ∀ k, k₁ ≤ k → ∀ c : ℤ,
      ¬ ((3 : ℤ) ^ runStart k - 1 ∣ 2 * c * (t : ℤ) ^ ((k + 2) * runStart k + 1)) →
      ∑ m ∈ Finset.range ((k + 2) * runStart k + 1), cycProd (runStart k) (c * (t : ℤ) ^ m) ≤
        (((k + 2) * runStart k + 1 : ℕ) : ℝ) * ψ k

section RunOrbit
open Finset

open Nat in
section

theorem summable_sqrt_geom {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Summable (fun k : ℕ => c ^ (Nat.sqrt k + 1) * ((k : ℝ) + 3) ^ 4) := by
  rcases hc0.eq_or_lt with rfl | hc0
  · simp
  set a := -Real.log c
  have ha : 0 < a := by have := Real.log_neg hc0 hc1; simp only [a]; linarith
  have hca : c = Real.exp (-a) := by simp [a, Real.exp_log hc0]
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2)).mul_left (81 * 12 ! / a ^ 12)
      |>.comp_injective (add_left_injective 1))
  set s : ℝ := ((Nat.sqrt k + 1 : ℕ) : ℝ)
  have hs : (k : ℝ) + 1 ≤ s ^ 2 := by
    have : k + 1 ≤ (Nat.sqrt k + 1) ^ 2 := by have := Nat.lt_succ_sqrt k; nlinarith
    simp only [s]; exact_mod_cast this
  have hs0 : 0 < s := by positivity
  have hexp : (a * s) ^ 12 / 12 ! ≤ Real.exp (a * s) := Real.pow_div_factorial_le_exp (x := a * s) (by positivity) 12
  have hcs : c ^ (Nat.sqrt k + 1) = Real.exp (-(a * s)) := by
    rw [hca, ← Real.exp_nat_mul]; congr 1; simp only [s]; push_cast; ring
  rw [hcs, Real.exp_neg]
  have hf : (0 : ℝ) < 12 ! := by positivity
  have hpos : 0 < (a * s) ^ 12 := by positivity
  have h1 : (Real.exp (a * s))⁻¹ ≤ 12 ! / (a * s) ^ 12 := by
    rw [inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]; exact hexp
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : ((k : ℝ) + 3) ^ 4 ≤ 81 * ((k : ℝ) + 1) ^ 4 := by
    have : (k : ℝ) + 3 ≤ 3 * ((k : ℝ) + 1) := by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    calc ((k : ℝ) + 3) ^ 4 ≤ (3 * ((k : ℝ) + 1)) ^ 4 := by gcongr
      _ = 81 * ((k : ℝ) + 1) ^ 4 := by ring
  have h3 : ((k : ℝ) + 1) ^ 6 ≤ s ^ 12 := by
    calc ((k : ℝ) + 1) ^ 6 ≤ (s ^ 2) ^ 6 := by gcongr
      _ = s ^ 12 := by ring
  simp only [Function.comp, one_div]
  push_cast
  rw [show (a * s) ^ 12 = a ^ 12 * s ^ 12 by ring] at h1
  calc (Real.exp (a * s))⁻¹ * ((k : ℝ) + 3) ^ 4 ≤ 12 ! / (a ^ 12 * s ^ 12) * (81 * ((k : ℝ) + 1) ^ 4) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ ≤ 12 ! / (a ^ 12 * ((k : ℝ) + 1) ^ 6) * (81 * ((k : ℝ) + 1) ^ 4) := by
        gcongr
    _ = 81 * 12 ! / a ^ 12 * (((k : ℝ) + 1) ^ 2)⁻¹ := by field_simp

open Nat in
theorem summable_poly_exp_div_fact (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun k : ℕ => ((k : ℝ) + 3) ^ p * x ^ k / k !) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((Real.summable_pow_div_factorial (Real.exp 1 * x)).mul_left (p ! * Real.exp 3))
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ) + 3) (by positivity) p
  have hp : (0 : ℝ) < p ! := by positivity
  have h' : ((k : ℝ) + 3) ^ p ≤ p ! * (Real.exp 3 * Real.exp 1 ^ k) := by
    rw [div_le_iff₀ hp] at h
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    calc _ ≤ Real.exp ((k : ℝ) + 3) * p ! := h
      _ = _ := by ring_nf
  rw [mul_pow, mul_div_assoc, mul_div_assoc]
  calc ((k : ℝ) + 3) ^ p * (x ^ k / k !) ≤ p ! * (Real.exp 3 * Real.exp 1 ^ k) * (x ^ k / k !) :=
        mul_le_mul_of_nonneg_right h' (by positivity)
    _ = _ := by ring

end

theorem orbit_sum_le {t A K N D L : ℕ} {C θ : ℝ} (ht : 1 ≤ t) (hA : 1 ≤ A)
    (hS : ∀ (K δ : ℕ) (U V : ℤ), SparseIdentity.IsSparse3 K U → SparseIdentity.IsSparse3 K V →
      U ≠ 0 → (t : ℤ) ^ δ * U = V → (δ : ℝ) ≤ Real.exp (C * (K + 1) ^ 2))
    (hθ : Real.cos (Real.pi / 9) ^ K < θ) (hθ0 : 0 ≤ θ)
    (hL : ∀ δ : ℕ, (δ : ℝ) ≤ Real.exp (C * (K + 1) ^ 2) → δ ≤ L)
    (hD : t ^ D + 2 ≤ 3 ^ (A / (2 * K + 1))) (hDN : D ≤ N) (c : ℤ)
    (hnd : ¬ ((3 : ℤ) ^ A - 1 ∣ 2 * c * (t : ℤ) ^ N)) :
    ∑ m ∈ range N, cycProd A (c * (t : ℤ) ^ m) ≤
      (N : ℝ) * (θ + min 1 (2 * ((L : ℝ) + 1) / max (D : ℝ) 1)) := by
  set Bad := (range N).filter fun m => θ ≤ cycProd A (c * (t : ℤ) ^ m)
  have hsplit : ∑ m ∈ range N, cycProd A (c * (t : ℤ) ^ m) ≤ Bad.card + N * θ := by
    rw [← sum_filter_add_sum_filter_not (range N) (fun m => θ ≤ cycProd A (c * (t : ℤ) ^ m))]
    have h1 : ∑ m ∈ Bad, cycProd A (c * (t : ℤ) ^ m) ≤ Bad.card := by
      have := sum_le_sum (s := Bad) fun m _ => cycProd_le_one A (c * (t : ℤ) ^ m)
      simpa using this
    have h2 : ∑ m ∈ (range N).filter (fun m => ¬ θ ≤ cycProd A (c * (t : ℤ) ^ m)),
        cycProd A (c * (t : ℤ) ^ m) ≤ N * θ := by
      have := sum_le_sum (s := (range N).filter (fun m => ¬ θ ≤ cycProd A (c * (t : ℤ) ^ m)))
        fun m hm => (not_le.1 (mem_filter.1 hm).2).le
      rw [sum_const, nsmul_eq_mul] at this
      refine this.trans (mul_le_mul_of_nonneg_right ?_ hθ0)
      exact_mod_cast (card_filter_le _ _).trans (card_range N).le
    linarith
  have hBN : (Bad.card : ℝ) ≤ N := by exact_mod_cast (card_filter_le _ _).trans (card_range N).le
  set r := 2 * ((L : ℝ) + 1) / max (D : ℝ) 1
  -- the cluster bound
  have hclust : L < D → (Bad.card : ℝ) ≤ N * r := by
    intro hLD
    have hcl : ∀ m ∈ Bad, ∀ m' ∈ Bad, m < m' → m' - m ≤ D → m' - m ≤ L := by
      intro m hm m' hm' hmm' hδ
      set δ := m' - m
      have hm'N := mem_range.1 (mem_filter.1 hm').1
      have hmN := mem_range.1 (mem_filter.1 hm).1
      have hy := cycSparse_of_cycProd_ge hA hθ _ (mem_filter.1 hm).2
      have hy' := cycSparse_of_cycProd_ge hA hθ _ (mem_filter.1 hm').2
      have heq : c * (t : ℤ) ^ m' = ((t ^ δ : ℕ) : ℤ) * (c * (t : ℤ) ^ m) := by
        push_cast; rw [show m' = δ + m by omega, pow_add]; ring
      have hgap : t ^ δ + 2 ≤ 3 ^ (A / (2 * K + 1)) :=
        le_trans (by have := Nat.pow_le_pow_right ht hδ; omega) hD
      obtain ⟨U, V, hU, hV, hUV, hU0⟩ := SparseIdentity.cyclic_pair_identity hA hy hy'
        (heq ▸ Int.ModEq.refl _) hgap
      have hUne : U ≠ 0 := by
        intro h
        apply hnd
        have := hU0 h
        obtain ⟨j, hj⟩ : ∃ j, N = m + j := ⟨N - m, by omega⟩
        rw [hj, pow_add]
        have h2 := this.mul_right ((t : ℤ) ^ j)
        rwa [show 2 * (c * (t : ℤ) ^ m) * (t : ℤ) ^ j = 2 * c * ((t : ℤ) ^ m * (t : ℤ) ^ j) by ring] at h2
      exact hL δ (hS K δ U V hU hV hUne (by rw [← hUV]; push_cast; ring))
    have hc := card_cluster_le hLD Bad (filter_subset _ _ |>.trans le_rfl) hcl
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    have hmax : max (D : ℝ) 1 = D := max_eq_left hD1
    have hdiv : ((N / D : ℕ) : ℝ) + 1 ≤ 2 * N / D := by
      have h1 : ((N / D : ℕ) : ℝ) ≤ (N : ℝ) / D := Nat.cast_div_le
      have h2 : (1 : ℝ) ≤ N / D := by
        rw [le_div_iff₀ (by linarith)]; simp; exact_mod_cast hDN
      have : 2 * (N : ℝ) / D = N / D + N / D := by ring
      linarith
    have : (Bad.card : ℝ) ≤ (((N / D : ℕ) : ℝ) + 1) * ((L : ℝ) + 1) := by exact_mod_cast hc
    calc (Bad.card : ℝ) ≤ (((N / D : ℕ) : ℝ) + 1) * ((L : ℝ) + 1) := this
      _ ≤ 2 * N / D * ((L : ℝ) + 1) := mul_le_mul_of_nonneg_right hdiv (by positivity)
      _ = N * r := by simp only [r, hmax]; ring
  have hfin : (Bad.card : ℝ) ≤ N * min 1 r := by
    rcases le_total 1 r with h | h
    · rw [min_eq_left h]; simpa using hBN
    · rw [min_eq_right h]
      apply hclust
      by_contra hDL; push Not at hDL
      have : 1 < r := by
        simp only [r]
        rw [lt_div_iff₀ (by positivity)]
        have : (D : ℝ) ≤ L := by exact_mod_cast hDL
        rcases le_total (D : ℝ) 1 with h' | h'
        · rw [max_eq_right h']; linarith [(Nat.cast_nonneg L : (0:ℝ) ≤ L)]
        · rw [max_eq_left h']; linarith
      linarith
  nlinarith


theorem factorial_le_runStart (k : ℕ) : k.factorial ≤ runStart k := by
  induction k with
  | zero => simp [runStart]
  | succ k ih => rw [runStart_succ_eq, Nat.factorial_succ]; nlinarith

end RunOrbit

/-- **Run orbit decay from sparse identities (PROVED 2026-10-08 from `SparseIdentityBound`).**

English proof.  Fix `k`, `A = a_k`, `N = N_k`, `K = ⌊√k⌋ + 1`, `θ = 2 cos(π/9)^K`, and let `L_K`
be the bound of `SparseIdentityBound t`, `L_K ≤ exp(C(K+1)²) = exp(O(k))`.  Call `m < N` bad if
`cycProd A (c tᵐ) ≥ θ`; good terms contribute `≤ Nθ`.  A bad `m` has `c tᵐ` cyclically
`K`-sparse (`cycSparse_of_cycProd_ge`), and non-degenerate (`2 c tᵐ ≢ 0`, since degeneracy is
inherited by `m + 1, …, N`).  Let `D` be the largest `δ` with `t^δ + 2 ≤ 3^{⌊A/(2K+1)⌋}`, so
`D ≥ A/((2K+1) log₃ t) − 2`.  For bad `m < m'` with `δ = m' − m ≤ D`, `c t^{m'} ≡ t^δ · c tᵐ`, and
`SparseIdentity.cyclic_pair_identity` gives `t^δ U = V` with `U ≠ 0`, so `δ ≤ L_K`.  As
`L_K < D` for large `k` (`A = a_k ≥ 2^k k!`), `card_cluster_le` bounds the bad `m` by
`(N/D + 1)(L_K + 1) = O(K k log t · L_K)`.  So `ψ_k = θ + O(K k L_K)/a_k`, and
`Σ ψ_k (k+3)⁴ < ∞` since `θ = 2cos(π/9)^{⌊√k⌋+1}` and `L_K/a_k ≤ exp(O(k) − k log k)`. -/
theorem runOrbitDecay_of_sparse {t : ℕ} (ht : 2 ≤ t) (h3 : ¬ 3 ∣ t)
    (hS : SparseIdentity.SparseIdentityBound t) : RunOrbitDecay t := by
  obtain ⟨C0, hC0⟩ := hS
  set C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hS' : ∀ (K δ : ℕ) (U V : ℤ), SparseIdentity.IsSparse3 K U → SparseIdentity.IsSparse3 K V →
      U ≠ 0 → (t : ℤ) ^ δ * U = V → (δ : ℝ) ≤ Real.exp (C * (K + 1) ^ 2) := by
    intro K δ U V hU hV hU0 h
    refine (hC0 K δ U V hU hV hU0 h).trans (Real.exp_le_exp.2 ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  set cc := Real.cos (Real.pi / 9)
  have hcc0 : 0 < cc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcc1 : cc < 1 := by
    rw [← Real.cos_zero]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith [Real.pi_pos]) (by positivity)
  let K : ℕ → ℕ := fun k => Nat.sqrt k + 1
  let L : ℕ → ℕ := fun k => ⌊Real.exp (C * ((K k : ℝ) + 1) ^ 2)⌋₊
  let g : ℕ → ℕ := fun k => runStart k / (2 * K k + 1)
  let D : ℕ → ℕ := fun k => (g k - 1) / t
  let ψ : ℕ → ℝ := fun k => 2 * cc ^ K k + min 1 (2 * ((L k : ℝ) + 1) / max (D k : ℝ) 1)
  have hψ0 : ∀ k, 0 ≤ ψ k := fun k => by
    have : 0 ≤ min 1 (2 * ((L k : ℝ) + 1) / max (D k : ℝ) 1) := le_min zero_le_one (by positivity)
    have : 0 ≤ 2 * cc ^ K k := by positivity
    simp only [ψ]; linarith
  refine ⟨ψ, hψ0, ?_, 0, fun k _ c hnd => ?_⟩
  swap
  · -- the bound
    have hA : 1 ≤ runStart k := le_trans (Nat.one_le_pow _ _ (by norm_num)) (four_pow_le_runStart k)
    have hK3 : 2 * K k + 1 ≤ runStart k := by
      have h1 : Nat.sqrt k ≤ k := Nat.sqrt_le_self k
      have h2' : ∀ n : ℕ, 2 * n + 3 ≤ 4 ^ (n + 1) := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih => rw [pow_succ]; omega
      have h2 := h2' k
      have := four_pow_le_runStart k
      simp only [K]; omega
    have hg1 : 1 ≤ g k := (Nat.le_div_iff_mul_le (by omega)).2 (by simpa using hK3)
    refine orbit_sum_le (by omega) hA hS' (θ := 2 * cc ^ K k) (by have := pow_pos hcc0 (K k); linarith)
      (by positivity) (fun δ hδ => Nat.le_floor hδ) ?_ ?_ c hnd
    · have h1 : t ^ D k ≤ 3 ^ (g k - 1) := by
        calc t ^ D k ≤ (3 ^ t) ^ D k := Nat.pow_le_pow_left (Nat.lt_pow_self (by norm_num)).le _
          _ = 3 ^ (t * D k) := by rw [← pow_mul]
          _ ≤ 3 ^ (g k - 1) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_div_le _ _)
      have h2 : 3 ^ (g k) = 3 * 3 ^ (g k - 1) := by
        rw [← pow_succ']; congr 1; omega
      have h3 : 1 ≤ 3 ^ (g k - 1) := Nat.one_le_pow _ _ (by norm_num)
      show t ^ D k + 2 ≤ 3 ^ g k
      omega
    · have : D k ≤ g k := (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
      have : g k ≤ runStart k := Nat.div_le_self _ _
      nlinarith
  -- summability
  have hsum1 := (summable_sqrt_geom hcc0.le hcc1).mul_left 2
  set E := Real.exp (2 * C)
  have hsum2 := (summable_poly_exp_div_fact 5 (x := E) (by positivity)).mul_left
    (24 * Real.exp (8 * C) * t)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hψ0 k) (by positivity)) (fun k => ?_)
    (hsum1.add hsum2)
  simp only [ψ, add_mul]
  refine add_le_add (by simp [K]; ring_nf; rfl) ?_
  -- the cluster part
  set r := 2 * ((L k : ℝ) + 1) / max (D k : ℝ) 1
  have hAle : (runStart k : ℝ) ≤ 3 * t * (2 * K k + 1) * max (D k : ℝ) 1 := by
    have e1 : runStart k < g k * (2 * K k + 1) + (2 * K k + 1) := Nat.lt_div_mul_add (by omega)
    have e2 : g k - 1 < (g k - 1) / t * t + t := Nat.lt_div_mul_add (by omega)
    have e3 : runStart k ≤ (2 * K k + 1) * (t * (D k + 1) + 1) := by
      have : g k ≤ t * (D k + 1) := by
        simp only [D]
        have : t * ((g k - 1) / t + 1) = (g k - 1) / t * t + t := by ring
        omega
      nlinarith
    have e3' : (runStart k : ℝ) ≤ (2 * K k + 1) * (t * (D k + 1) + 1) := by exact_mod_cast e3
    have ht1 : (2 : ℝ) ≤ t := by exact_mod_cast ht
    rcases Nat.eq_zero_or_pos (D k) with h0 | h0
    · rw [h0] at e3' ⊢; simp at e3' ⊢; nlinarith
    · have hD1 : (1 : ℝ) ≤ D k := by exact_mod_cast h0
      rw [max_eq_left hD1]
      have h : (t : ℝ) * (D k + 1) + 1 ≤ 3 * t * D k := by nlinarith
      have : (0 : ℝ) ≤ 2 * K k + 1 := by positivity
      nlinarith
  have hA0 : (0 : ℝ) < runStart k := by
    exact_mod_cast lt_of_lt_of_le (Nat.factorial_pos k) (factorial_le_runStart k)
  have hfact : ((k.factorial : ℕ) : ℝ) ≤ runStart k := by exact_mod_cast factorial_le_runStart k
  have hr : r ≤ 6 * t * (2 * K k + 1) * ((L k : ℝ) + 1) / runStart k := by
    simp only [r]
    rw [div_le_div_iff₀ (by positivity) hA0]
    nlinarith [(by positivity : (0 : ℝ) ≤ (L k : ℝ) + 1)]
  have hKk : (2 * (K k : ℝ) + 1) ≤ 2 * (k + 3) := by
    have : Nat.sqrt k ≤ k := Nat.sqrt_le_self k
    have : 2 * K k + 1 ≤ 2 * (k + 3) := by simp only [K]; omega
    exact_mod_cast this
  have hK2 : ((K k : ℝ) + 1) ^ 2 ≤ 2 * k + 8 := by
    have h1 : Nat.sqrt k * Nat.sqrt k ≤ k := Nat.sqrt_le k
    have : (Nat.sqrt k + 2) ^ 2 ≤ 2 * k + 8 := by
      nlinarith [Nat.sub_add_cancel (Nat.le_refl 0), sq_nonneg ((Nat.sqrt k : ℤ) - 2)]
    have : ((Nat.sqrt k + 2 : ℕ) : ℝ) ^ 2 ≤ ((2 * k + 8 : ℕ) : ℝ) := by exact_mod_cast this
    simp only [K]; push_cast at this ⊢; linarith
  have hL1 : (L k : ℝ) + 1 ≤ 2 * (Real.exp (8 * C) * E ^ k) := by
    have h1 : (L k : ℝ) ≤ Real.exp (C * ((K k : ℝ) + 1) ^ 2) := Nat.floor_le (by positivity)
    have h2 : Real.exp (C * ((K k : ℝ) + 1) ^ 2) ≤ Real.exp (8 * C) * E ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    have h3 : 1 ≤ Real.exp (C * ((K k : ℝ) + 1) ^ 2) := Real.one_le_exp (by positivity)
    linarith
  have hmin : min 1 r ≤ r := min_le_right _ _
  have hk3 : (0 : ℝ) ≤ ((k : ℝ) + 3) ^ 4 := by positivity
  calc min 1 r * ((k : ℝ) + 3) ^ 4 ≤ r * ((k : ℝ) + 3) ^ 4 := mul_le_mul_of_nonneg_right hmin hk3
    _ ≤ 6 * t * (2 * K k + 1) * ((L k : ℝ) + 1) / runStart k * ((k : ℝ) + 3) ^ 4 :=
        mul_le_mul_of_nonneg_right hr hk3
    _ ≤ 6 * t * (2 * (k + 3)) * (2 * (Real.exp (8 * C) * E ^ k)) / k.factorial * ((k : ℝ) + 3) ^ 4 := by
        gcongr
    _ = 24 * Real.exp (8 * C) * t * (((k : ℝ) + 3) ^ 5 * E ^ k / k.factorial) := by ring

section DegRows

theorem pow_padicVal_le_of_dvd {p a b : ℕ} [Fact p.Prime] (hb : b ≠ 0) (h : a ∣ b) :
    padicValNat p a ≤ padicValNat p b :=
  (padicValNat_dvd_iff_le hb).1 ((pow_padicValNat_dvd).trans h)

/-- LTE bound: the `p`-part of `3^A − 1` is at most `2A·3^{2(p−1)}`. -/
theorem pow_padicVal_three_pow_sub_one_le {p A : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hA : 1 ≤ A) :
    p ^ padicValNat p (3 ^ A - 1) ≤ 2 * A * 3 ^ (2 * (p - 1)) := by
  have := Fact.mk hp
  set x := 3 ^ (2 * (p - 1))
  have hx1 : 1 < x := Nat.one_lt_pow (by have := hp.two_le; omega) (by norm_num)
  have hq0 : 3 ^ A - 1 ≠ 0 := by have : 3 ≤ 3 ^ A := Nat.le_self_pow (by omega) 3; omega
  have hdvd : 3 ^ A - 1 ∣ x ^ (2 * A) - 1 := by
    have : x ^ (2 * A) = (3 ^ A) ^ (4 * (p - 1)) := by
      simp only [x]; rw [← pow_mul, ← pow_mul]; ring_nf
    rw [this]
    simpa using Nat.sub_dvd_pow_sub_pow (x := 3 ^ A) (y := 1) (n := 4 * (p - 1))
  have hX0 : x ^ (2 * A) - 1 ≠ 0 := by
    have : 1 < x ^ (2 * A) := Nat.one_lt_pow (by omega) hx1
    omega
  have hle := pow_padicVal_le_of_dvd (p := p) hX0 hdvd
  have h2A : p ^ padicValNat p (2 * A) ≤ 2 * A := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have hx9 : x = 9 := by simp [x]
    have h := padicValNat.pow_two_sub_one (x := x) (n := 2 * A) hx1 (by rw [hx9]; decide) (by omega)
      (by simp)
    rw [hx9] at h
    have h10 : padicValNat 2 10 = 1 := by
      rw [show (10 : ℕ) = 2 * 5 from rfl, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)]
    have h8 : padicValNat 2 8 = 3 := by
      rw [show (8 : ℕ) = 2 ^ 3 from rfl, padicValNat.prime_pow]
    simp only [show 9 + 1 = 10 from rfl, show 9 - 1 = 8 from rfl, h10, h8] at h
    rw [hx9] at hle
    calc 2 ^ padicValNat 2 (3 ^ A - 1) ≤ 2 ^ (3 + padicValNat 2 (2 * A)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 8 * 2 ^ padicValNat 2 (2 * A) := by rw [pow_add]; norm_num
      _ ≤ 8 * (2 * A) := by omega
      _ ≤ 2 * A * 3 ^ (2 * (2 - 1)) := by norm_num; nlinarith
  · have hpx : p ∣ x - 1 := by
      have hc : ¬ p ∣ 3 := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
      have hf := Nat.ModEq.pow_totient (n := p) (x := 3) (Nat.Coprime.symm
        ((Nat.Prime.coprime_iff_not_dvd hp).2 hc))
      rw [Nat.totient_prime hp] at hf
      have : x ≡ 1 [MOD p] := by
        simp only [x]; rw [mul_comm, pow_mul]; simpa using hf.pow 2
      exact (Nat.modEq_iff_dvd' hx1.le).1 this.symm
    have h := padicValNat.pow_sub_pow (p := p) hodd (x := x) (y := 1) hx1 hpx
      (fun h => by
        have : p ∣ x - (x - 1) := Nat.dvd_sub h hpx
        rw [show x - (x - 1) = 1 by omega] at this
        exact hp.one_lt.ne' (Nat.dvd_one.1 this)) (n := 2 * A) (by omega)
    rw [one_pow] at h
    have hx' : p ^ padicValNat p (x - 1) ≤ x - 1 := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    calc p ^ padicValNat p (3 ^ A - 1) ≤ p ^ (padicValNat p (x - 1) + padicValNat p (2 * A)) :=
          Nat.pow_le_pow_right hp.pos (by omega)
      _ = p ^ padicValNat p (x - 1) * p ^ padicValNat p (2 * A) := pow_add _ _ _
      _ ≤ (x - 1) * (2 * A) := Nat.mul_le_mul hx' h2A
      _ ≤ 2 * A * x := by rw [mul_comm]; exact Nat.mul_le_mul_left _ (by omega)

theorem gcd_three_pow_sub_one_le {t A N : ℕ} (ht : 1 ≤ t) (h3 : ¬ 3 ∣ t) (hA : 1 ≤ A) :
    Nat.gcd (3 ^ A - 1) (t ^ N) ≤ (2 * A * 9 ^ t) ^ (t + 1) := by
  set g := Nat.gcd (3 ^ A - 1) (t ^ N)
  have hq0 : 3 ^ A - 1 ≠ 0 := by have : 3 ≤ 3 ^ A := Nat.le_self_pow (by omega) 3; omega
  have hg0 : g ≠ 0 := Nat.gcd_ne_zero_left hq0
  have hB : 1 ≤ 2 * A * 9 ^ t := by have := Nat.one_le_pow t 9 (by norm_num); nlinarith
  rw [← Nat.prod_factorization_pow_eq_self hg0]
  have hsub : g.primeFactors ⊆ Finset.range (t + 1) := by
    intro p hp
    have hpd : p ∣ t := (Nat.prime_of_mem_primeFactors hp).dvd_of_dvd_pow
      ((Nat.dvd_of_mem_primeFactors hp).trans (Nat.gcd_dvd_right _ _))
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hpd))
  calc g.factorization.prod (fun p k => p ^ k) = ∏ p ∈ g.primeFactors, p ^ g.factorization p := rfl
    _ ≤ ∏ _p ∈ g.primeFactors, 2 * A * 9 ^ t := by
      refine Finset.prod_le_prod' fun p hp => ?_
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd : p ∣ t := hpp.dvd_of_dvd_pow
        ((Nat.dvd_of_mem_primeFactors hp).trans (Nat.gcd_dvd_right _ _))
      have hp3 : p ≠ 3 := by rintro rfl; exact h3 hpd
      have hpt : p ≤ t := Nat.le_of_dvd (by omega) hpd
      have h1 : g.factorization p ≤ (3 ^ A - 1).factorization p :=
        (Nat.factorization_le_iff_dvd hg0 hq0).2 (Nat.gcd_dvd_left _ _) p
      rw [Nat.factorization_def (3 ^ A - 1) hpp] at h1
      calc p ^ g.factorization p ≤ p ^ padicValNat p (3 ^ A - 1) :=
            Nat.pow_le_pow_right hpp.pos h1
        _ ≤ 2 * A * 3 ^ (2 * (p - 1)) := pow_padicVal_three_pow_sub_one_le hpp hp3 hA
        _ ≤ 2 * A * 9 ^ t := by
            rw [show (9 : ℕ) ^ t = 3 ^ (2 * t) by rw [pow_mul]; norm_num]
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    _ = (2 * A * 9 ^ t) ^ g.primeFactors.card := Finset.prod_const _
    _ ≤ (2 * A * 9 ^ t) ^ (t + 1) := Nat.pow_le_pow_right hB
        ((Finset.card_le_card hsub).trans (by simp))

theorem dvd_of_dvd_mul_gcd {q X Y : ℕ} (hq : q ≠ 0) (h : q ∣ Y * X) : q / Nat.gcd q Y ∣ X := by
  have h0 : 0 < Nat.gcd q Y := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hq)
  have hc := Nat.coprime_div_gcd_div_gcd h0 (m := q) (n := Y)
  refine hc.dvd_of_dvd_mul_left ?_
  obtain ⟨u, hu⟩ := h
  refine ⟨u, ?_⟩
  have h1 := Nat.div_mul_cancel (Nat.gcd_dvd_left q Y)
  have h2 := Nat.div_mul_cancel (Nat.gcd_dvd_right q Y)
  apply Nat.eq_of_mul_eq_mul_right h0
  calc Y / q.gcd Y * X * q.gcd Y = Y * X := by rw [mul_right_comm, h2]
    _ = q * u := hu
    _ = q / q.gcd Y * u * q.gcd Y := by rw [mul_right_comm, h1]

/-- Shifts `d` with `Q ∣ b^d − 1` are more than `log_b Q` apart. -/
theorem card_deg_le {b Q N : ℕ} (hb : 2 ≤ b) (hQ : 1 ≤ Q) (hD : 1 ≤ Nat.log b Q) (B : Finset ℕ)
    (hB : B ⊆ Finset.range N) (hdeg : ∀ d ∈ B, Q ∣ b ^ d - 1) :
    B.card ≤ N / Nat.log b Q + 1 := by
  have key : ∀ d₁ ∈ B, ∀ d₂ ∈ B, d₁ < d₂ → Nat.log b Q < d₂ - d₁ := by
    intro d₁ h₁ d₂ h₂ hlt
    set δ := d₂ - d₁
    have hb1 : 1 ≤ b ^ d₁ := Nat.one_le_pow _ _ (by omega)
    have hcop : Nat.Coprime Q (b ^ d₁) := by
      have h := hdeg d₁ h₁
      refine Nat.Coprime.coprime_dvd_left h ?_
      have hc : Nat.Coprime (b ^ d₁ - 1) (b ^ d₁ - 1 + 1) :=
        Nat.coprime_self_add_right.2 (Nat.coprime_one_right _)
      rwa [show b ^ d₁ - 1 + 1 = b ^ d₁ by omega] at hc
    have hdiff : Q ∣ b ^ d₁ * (b ^ δ - 1) := by
      have e : b ^ d₁ * (b ^ δ - 1) = (b ^ d₂ - 1) - (b ^ d₁ - 1) := by
        rw [Nat.mul_sub, mul_one, ← pow_add, show d₁ + δ = d₂ by omega]
        have : b ^ d₁ ≤ b ^ d₂ := Nat.pow_le_pow_right (by omega) hlt.le
        omega
      rw [e]; exact Nat.dvd_sub (hdeg d₂ h₂) (hdeg d₁ h₁)
    have h2 := hcop.dvd_of_dvd_mul_left hdiff
    have hpos : 1 ≤ b ^ δ - 1 := by
      have : b ≤ b ^ δ := Nat.le_self_pow (by omega) b
      omega
    have hQle := Nat.le_of_dvd (by omega) h2
    by_contra hcon; push Not at hcon
    have := Nat.pow_le_pow_right (show 1 ≤ b by omega) hcon
    have := Nat.pow_log_le_self b (show Q ≠ 0 by omega)
    omega
  have := NormalNumbers.CantorRepetition.card_cluster_le (L := 0) hD B hB
    (fun m hm m' hm' hlt hle => absurd hle (not_le.2 (key m hm m' hm' hlt)))
  simpa using this

theorem poly_le_three_pow (c e : ℕ) : ∃ A0 : ℕ, ∀ A, A0 ≤ A → c * A ^ e + 1 ≤ 3 ^ (A / 2) := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt e (by norm_num : (1 : ℝ) < 3)
  have hε : (0 : ℝ) < 1 / (2 * ((c : ℝ) * 3 ^ e + 1)) := by positivity
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds hε))
  refine ⟨2 * M0 + 2, fun A hA => ?_⟩
  set m := A / 2
  have hm : M0 + 1 ≤ m := by omega
  have hAm : A ≤ 3 * m := by omega
  have h1 := hM0 m (by omega)
  have h3m : (0 : ℝ) < 3 ^ m := by positivity
  have h3m2 : (2 : ℝ) ≤ 3 ^ m := by
    have : (3 : ℝ) ≤ 3 ^ m := by
      have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (show 1 ≤ m by omega); simpa using this
    linarith
  rw [div_lt_div_iff₀ h3m (by positivity)] at h1
  have hAe : (A : ℝ) ^ e ≤ 3 ^ e * (m : ℝ) ^ e := by
    rw [← mul_pow]; gcongr; exact_mod_cast hAm
  have : (c : ℝ) * A ^ e + 1 ≤ 3 ^ m := by
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    have : (c : ℝ) * A ^ e ≤ c * 3 ^ e * m ^ e := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hAe hc
    have hme : (0 : ℝ) ≤ (m : ℝ) ^ e := by positivity
    nlinarith
  exact_mod_cast this

end DegRows

/-- **Degenerate rows are few (PROVED 2026-10-08; elementary, LTE).**  Shifts `d < N_k` whose row
`tᵐ h'(b^d − 1)` is degenerate modulo `3^{a_k} − 1` number `O(k + 3)`.

English proof.  Degeneracy means `Q ∣ b^d − 1` for `Q = q/gcd(q, 2h' t^{N_k})`, `q = 3^{a_k} − 1`.
By lifting the exponent, `gcd(q, t^∞) ≤ C_t a_k`, so `Q ≥ q/(2h' C_t a_k) ≥ 3^{a_k/2}` for large
`k`.  The degenerate `d` are multiples of `ord_Q(b) ≥ log_b Q ≥ a_k/(2 log₃ b)`, so there are
`≤ N_k·2 log₃ b/a_k + 1 ≤ 2(k+3) log₃ b + 1` of them. -/
theorem card_degRows_le {s t : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (h3 : ¬ 3 ∣ t) (h' : ℕ)
    (hh : 1 ≤ h') : ∃ C : ℝ, ∃ k₁ : ℕ, ∀ k, k₁ ≤ k →
      (((Finset.Ico 1 ((k + 2) * runStart k + 1)).filter fun d =>
        (3 : ℤ) ^ runStart k - 1 ∣ 2 * ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ d - 1)) *
          (t : ℤ) ^ ((k + 2) * runStart k + 1)).card : ℝ) ≤ C * ((k : ℝ) + 3) := by
  set b := 3 ^ s * t with hbdef
  have hb : 2 ≤ b := by
    have : 3 ≤ 3 ^ s := Nat.le_self_pow (by omega) 3
    nlinarith
  set c0 := 2 * h' * (2 * 9 ^ t) ^ (t + 1)
  obtain ⟨A0, hA0⟩ := poly_le_three_pow c0 (t + 1)
  refine ⟨4 * b + 1, max A0 (4 * b), fun k hk => ?_⟩
  set A := runStart k
  have hAk : k < A := lt_runStart k
  have hAA0 : A0 ≤ A := by omega
  have hA4 : 4 * b ≤ A := by omega
  have hA1 : 1 ≤ A := by omega
  set N := (k + 2) * A + 1
  set q := 3 ^ A - 1
  have hq0 : q ≠ 0 := by have : 3 ≤ 3 ^ A := Nat.le_self_pow (by omega) 3; omega
  set Y := 2 * h' * t ^ N
  set g := Nat.gcd q Y
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hq0)
  have hgle : g ≤ c0 * A ^ (t + 1) := by
    have h1 : g ∣ Nat.gcd q (2 * h') * Nat.gcd q (t ^ N) := gcd_mul_dvd_mul_gcd q (2 * h') (t ^ N)
    have h2 : Nat.gcd q (2 * h') ≤ 2 * h' := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
    have h3' := gcd_three_pow_sub_one_le (N := N) (by omega) h3 hA1
    have := Nat.le_of_dvd (by
      have : 0 < Nat.gcd q (t ^ N) := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hq0)
      have : 0 < Nat.gcd q (2 * h') := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hq0)
      positivity) h1
    calc g ≤ Nat.gcd q (2 * h') * Nat.gcd q (t ^ N) := this
      _ ≤ 2 * h' * (2 * A * 9 ^ t) ^ (t + 1) := Nat.mul_le_mul h2 h3'
      _ = c0 * A ^ (t + 1) := by simp only [c0]; ring
  set Q := q / g
  have hQ : 3 ^ (A / 2) ≤ Q := by
    rw [Nat.le_div_iff_mul_le hg0]
    have h1 := hA0 A hAA0
    have h2 : 3 ^ (A / 2) * 3 ^ (A / 2) ≤ 3 ^ A := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3p : 1 ≤ 3 ^ (A / 2) := Nat.one_le_pow _ _ (by norm_num)
    have : 3 ^ (A / 2) * g ≤ 3 ^ (A / 2) * (3 ^ (A / 2) - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_sub, mul_one] at this
    simp only [q]; omega
  set m := A / (2 * b)
  have hm2 : 2 ≤ m := (Nat.le_div_iff_mul_le (by omega)).2 (by linarith)
  have hbm : b ^ m ≤ Q := by
    calc b ^ m ≤ (3 ^ b) ^ m := Nat.pow_le_pow_left (Nat.lt_pow_self (by norm_num)).le _
      _ = 3 ^ (b * m) := by rw [← pow_mul]
      _ ≤ 3 ^ (A / 2) := Nat.pow_le_pow_right (by norm_num) (by
          rw [Nat.le_div_iff_mul_le (by norm_num)]
          have := Nat.div_mul_le_self A (2 * b)
          simp only [m]; nlinarith)
      _ ≤ Q := hQ
  have hQ1 : 1 ≤ Q := le_trans (Nat.one_le_pow _ _ (by omega)) hbm
  have hmlog : m ≤ Nat.log b Q := Nat.le_log_of_pow_le (by omega) hbm
  -- the degenerate set
  set B := (Finset.Ico 1 N).filter fun d =>
    (3 : ℤ) ^ A - 1 ∣ 2 * ((h' : ℤ) * ((b : ℤ) ^ d - 1)) * (t : ℤ) ^ N
  have hBsub : B ⊆ Finset.range N := fun d hd =>
    Finset.mem_range.2 (Finset.mem_Ico.1 (Finset.mem_filter.1 hd).1).2
  have hdeg : ∀ d ∈ B, Q ∣ b ^ d - 1 := by
    intro d hd
    have h := (Finset.mem_filter.1 hd).2
    have hbd : 1 ≤ b ^ d := Nat.one_le_pow _ _ (by omega)
    have hcast : ((q : ℕ) : ℤ) ∣ ((Y * (b ^ d - 1) : ℕ) : ℤ) := by
      have e1 : ((q : ℕ) : ℤ) = (3 : ℤ) ^ A - 1 := by
        simp only [q]; rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]; push_cast; ring
      have e2 : ((Y * (b ^ d - 1) : ℕ) : ℤ) = 2 * ((h' : ℤ) * ((b : ℤ) ^ d - 1)) * (t : ℤ) ^ N := by
        simp only [Y]; rw [Nat.cast_mul, Nat.cast_sub hbd]; push_cast; ring
      rw [e1, e2]; exact h
    exact dvd_of_dvd_mul_gcd hq0 (Int.natCast_dvd_natCast.1 hcast)
  have hcard := card_deg_le hb hQ1 (by omega) B hBsub hdeg
  -- real bound
  have hN : (N / Nat.log b Q : ℕ) ≤ N / m := Nat.div_le_div_left hmlog (by omega)
  have hmA : (A : ℝ) ≤ 4 * b * m := by
    have h1 : A < (m + 1) * (2 * b) := by
      have := Nat.lt_div_mul_add (a := A) (b := 2 * b) (by omega); simp only [m]; nlinarith
    have : A ≤ 4 * b * m := by nlinarith
    exact_mod_cast this
  have hNm : ((N / m : ℕ) : ℝ) ≤ 4 * b * ((k : ℝ) + 3) := by
    refine Nat.cast_div_le.trans ?_
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rw [div_le_iff₀ hm0]
    have hNr : (N : ℝ) = (k + 2) * A + 1 := by simp only [N]; push_cast; ring
    rw [hNr]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hb0 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
    nlinarith
  have hc : (B.card : ℝ) ≤ ((N / m : ℕ) : ℝ) + 1 := by exact_mod_cast hcard.trans (by omega)
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  push_cast at hbdef
  calc (B.card : ℝ) ≤ 4 * b * ((k : ℝ) + 3) + 1 := by linarith
    _ ≤ (4 * b + 1) * ((k : ℝ) + 3) := by nlinarith

section CopyRun
open Finset

/-- Folding a symmetric double sum onto rows `d = n − m`. -/
theorem sum_sym_le_rows (N : ℕ) (F : ℕ → ℕ → ℝ) (G : ℕ → ℕ → ℝ) (hG : ∀ d m, 0 ≤ G d m)
    (hsym : ∀ n m, F n m = F m n) (hFG : ∀ m d, F (m + d) m = G d m) :
    ∑ n ∈ range N, ∑ m ∈ range N, F n m ≤ 2 * ∑ d ∈ range N, ∑ m ∈ range N, G d m := by
  have hF0 : ∀ n m, 0 ≤ F n m := by
    intro n m
    rcases le_total m n with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h; rw [hFG]; exact hG _ _
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h; rw [hsym, hFG]; exact hG _ _
  have hsplit : ∑ n ∈ range N, ∑ m ∈ range N, F n m =
      ∑ n ∈ range N, ∑ m ∈ range N, (if m ≤ n then F n m else 0) +
      ∑ n ∈ range N, ∑ m ∈ range N, (if n < m then F n m else 0) := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun n _ => ?_
    rw [← sum_add_distrib]; refine sum_congr rfl fun m _ => ?_
    by_cases h : m ≤ n
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  have hswap : ∑ n ∈ range N, ∑ m ∈ range N, (if n < m then F n m else 0) ≤
      ∑ n ∈ range N, ∑ m ∈ range N, (if m ≤ n then F n m else 0) := by
    rw [sum_comm]
    refine sum_le_sum fun n _ => sum_le_sum fun m _ => ?_
    by_cases h : m < n
    · rw [if_pos h, if_pos h.le, hsym]
    · rw [if_neg h]; split_ifs <;> first | exact hF0 _ _ | exact le_rfl
  have hrows : ∑ n ∈ range N, ∑ m ∈ range N, (if m ≤ n then F n m else 0) ≤
      ∑ d ∈ range N, ∑ m ∈ range N, G d m := by
    rw [sum_comm, sum_comm (s := range N) (t := range N) (f := fun d m => G d m)]
    refine sum_le_sum fun m hm => ?_
    have hmN := mem_range.1 hm
    rw [← sum_filter]
    have hfil : (range N).filter (fun n => m ≤ n) = Ico m N := by
      ext n; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [hfil, sum_Ico_eq_sum_range]
    simp only [hFG]
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun d _ _ => hG _ _
  linarith


theorem not_dvd_two_mul_pow {t h' : ℕ} (ht : 1 ≤ t) (h3 : ¬ 3 ∣ t) (hh : 1 ≤ h') :
    ∃ A0 : ℕ, ∀ A N : ℕ, A0 ≤ A → 1 ≤ A →
      ¬ ((3 : ℤ) ^ A - 1 ∣ 2 * (h' : ℤ) * (t : ℤ) ^ N) := by
  obtain ⟨A0, hA0⟩ := poly_le_three_pow (2 * h' * (2 * 9 ^ t) ^ (t + 1)) (t + 1)
  refine ⟨A0, fun A N hA hA1 hdvd => ?_⟩
  set q := 3 ^ A - 1
  have hq0 : q ≠ 0 := by have : 3 ≤ 3 ^ A := Nat.le_self_pow (by omega) 3; omega
  have hY : q ∣ 2 * h' * t ^ N := by
    have e1 : ((q : ℕ) : ℤ) = (3 : ℤ) ^ A - 1 := by
      simp only [q]; rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]; push_cast; ring
    exact Int.natCast_dvd_natCast.1 (by rw [e1]; push_cast; exact hdvd)
  have hg : Nat.gcd q (2 * h' * t ^ N) = q := Nat.gcd_eq_left hY
  have h1 : Nat.gcd q (2 * h' * t ^ N) ∣ Nat.gcd q (2 * h') * Nat.gcd q (t ^ N) :=
    gcd_mul_dvd_mul_gcd q (2 * h') (t ^ N)
  have h2 : Nat.gcd q (2 * h') ≤ 2 * h' := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
  have h3' := gcd_three_pow_sub_one_le (N := N) ht h3 hA1
  have hp1 : 0 < Nat.gcd q (t ^ N) := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hq0)
  have hp2 : 0 < Nat.gcd q (2 * h') := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hq0)
  have := Nat.le_of_dvd (by positivity) h1
  have hle : q ≤ 2 * h' * (2 * 9 ^ t) ^ (t + 1) * A ^ (t + 1) := by
    calc q = Nat.gcd q (2 * h' * t ^ N) := hg.symm
      _ ≤ Nat.gcd q (2 * h') * Nat.gcd q (t ^ N) := this
      _ ≤ 2 * h' * (2 * A * 9 ^ t) ^ (t + 1) := Nat.mul_le_mul h2 h3'
      _ = _ := by ring
  have h4 := hA0 A hA
  have h5 : 3 * 3 ^ (A / 2) ≤ 3 ^ A := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  simp only [q] at hle
  generalize 2 * h' * (2 * 9 ^ t) ^ (t + 1) * A ^ (t + 1) = P at hle h4
  omega

end CopyRun

/-- **Per-run copy total (PROVED 2026-10-08; elementary from the two nodes above).**  The run sums
of `repPairPos_explicit`'s copy term are `≤ N_k² ψ_k` with `Σ ψ_k (k+3)⁴ < ∞`.
English proof: `pair_sum_le` (rows `d`, `G d m = cycProd(tᵐ h'(b^d − 1))`, `cycProd_pairH`);
non-degenerate rows by `RunOrbitDecay`, degenerate rows by `1` and counted by `card_degRows_le`;
the single orbit `c = h'` is non-degenerate for large `k` (`2h'·gcd(q, t^∞) < q`).  So
`ψ'_k = 3ψ_k + (1 + 2C(k+3))/a_k`, and `a_k ≥ 4^{k+1}`. -/
theorem copyRun_psi {s t : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (h3 : ¬ 3 ∣ t) (hR : RunOrbitDecay t)
    (h' : ℕ) (hh : 1 ≤ h') :
    ∃ ψ : ℕ → ℝ, (∀ k, 0 ≤ ψ k) ∧ Summable (fun k => ψ k * ((k : ℝ) + 3) ^ 4) ∧ ∃ k₁ : ℕ,
      ∀ k, k₁ ≤ k →
        ∑ n ∈ Finset.range ((k + 2) * runStart k + 1),
          ∑ m ∈ Finset.range ((k + 2) * runStart k + 1),
            (cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ m))
              + cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ n)) ≤
          ((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2 * ψ k := by
  open Finset in
  obtain ⟨ψ, hψ0, hψs, k₁, hRb⟩ := hR
  obtain ⟨Cd, k₂, hCd⟩ := card_degRows_le hs ht h3 h' hh
  obtain ⟨A0, hA0⟩ := not_dvd_two_mul_pow (t := t) (by omega) h3 hh
  let Nk : ℕ → ℝ := fun k => (((k + 2) * runStart k + 1 : ℕ) : ℝ)
  have hNk : ∀ k, (k.factorial : ℝ) ≤ Nk k := fun k => by
    have := factorial_le_runStart k
    have : k.factorial ≤ (k + 2) * runStart k + 1 := by nlinarith
    simp only [Nk]; exact_mod_cast this
  have hNk0 : ∀ k, 0 < Nk k := fun k => by simp only [Nk]; positivity
  let ψ' : ℕ → ℝ := fun k => 3 * ψ k + 2 * (1 + |Cd| * ((k : ℝ) + 3)) / Nk k
  refine ⟨ψ', fun k => by
    have := hψ0 k; have := hNk0 k
    simp only [ψ']; positivity, ?_, max k₁ (max k₂ A0), fun k hk => ?_⟩
  · -- summability
    have hs2 := (summable_poly_exp_div_fact 5 (x := 1) zero_le_one).mul_left (2 * (1 + |Cd|))
    refine Summable.of_nonneg_of_le
      (fun k => by have := hψ0 k; have := hNk0 k; simp only [ψ']; positivity) (fun k => ?_)
      ((hψs.mul_left 3).add hs2)
    simp only [ψ', add_mul]
    refine add_le_add (le_of_eq (by ring)) ?_
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have h1 : 1 + |Cd| * ((k : ℝ) + 3) ≤ (1 + |Cd|) * ((k : ℝ) + 3) := by
      nlinarith [abs_nonneg Cd]
    rw [div_mul_eq_mul_div, one_pow, mul_one, div_le_iff₀ (hNk0 k)]
    calc 2 * (1 + |Cd| * ((k : ℝ) + 3)) * ((k : ℝ) + 3) ^ 4
        ≤ 2 * ((1 + |Cd|) * ((k : ℝ) + 3)) * ((k : ℝ) + 3) ^ 4 := by gcongr
      _ = 2 * (1 + |Cd|) * (((k : ℝ) + 3) ^ 5 / k.factorial) * k.factorial := by
        field_simp
      _ ≤ 2 * (1 + |Cd|) * (((k : ℝ) + 3) ^ 5 / k.factorial) * Nk k := by
        gcongr; exact hNk k
  -- the bound
  set A := runStart k
  set N := (k + 2) * A + 1
  have hAk : k < A := lt_runStart k
  have hA1 : 1 ≤ A := by omega
  have hN : (N : ℝ) = Nk k := rfl
  set b : ℕ := 3 ^ s * t
  have hRk := hRb k (by omega)
  -- the pair part
  set G : ℕ → ℕ → ℝ := fun d m => cycProd A ((t : ℤ) ^ m * ((h' : ℤ) * ((b : ℤ) ^ d - 1)))
  have hpair := sum_sym_le_rows N (fun n m => cycProd A ((h' : ℤ) * ((b : ℤ) ^ n - (b : ℤ) ^ m))) G
    (fun d m => cycProd_nonneg _ _)
    (fun n m => by
      rw [show (h' : ℤ) * ((b : ℤ) ^ n - (b : ℤ) ^ m) = -((h' : ℤ) * ((b : ℤ) ^ m - (b : ℤ) ^ n))
        by ring, cycProd_neg])
    (fun m d => cycProd_pairH A s t m d h')
  -- the rows
  set Dg := insert 0 ((Finset.Ico 1 N).filter fun d =>
    (3 : ℤ) ^ A - 1 ∣ 2 * ((h' : ℤ) * ((b : ℤ) ^ d - 1)) * (t : ℤ) ^ N)
  have hrow : ∀ d ∈ range N, ∑ m ∈ range N, G d m ≤ N * ψ k + (if d ∈ Dg then (N : ℝ) else 0) := by
    intro d hd
    have hle1 : ∑ m ∈ range N, G d m ≤ N := by
      have := sum_le_sum (s := range N) fun m _ => cycProd_le_one A
        ((t : ℤ) ^ m * ((h' : ℤ) * ((b : ℤ) ^ d - 1)))
      simpa using this
    have hNψ : 0 ≤ (N : ℝ) * ψ k := mul_nonneg (Nat.cast_nonneg _) (hψ0 k)
    split_ifs with hDg
    · linarith
    · have hd1 : 1 ≤ d := by
        by_contra h0; apply hDg; rw [show d = 0 by omega]; exact mem_insert_self _ _
      have hnd : ¬ ((3 : ℤ) ^ A - 1 ∣ 2 * ((h' : ℤ) * ((b : ℤ) ^ d - 1)) * (t : ℤ) ^ N) := by
        intro hdv; apply hDg
        exact mem_insert_of_mem (mem_filter.2 ⟨mem_Ico.2 ⟨hd1, mem_range.1 hd⟩, hdv⟩)
      have := hRk ((h' : ℤ) * ((b : ℤ) ^ d - 1)) hnd
      have e : ∑ m ∈ range N, G d m = ∑ m ∈ range N,
          cycProd A ((h' : ℤ) * ((b : ℤ) ^ d - 1) * (t : ℤ) ^ m) :=
        sum_congr rfl fun m _ => by simp only [G]; rw [mul_comm]
      rw [e]; linarith
  have hDgc : (((range N).filter (· ∈ Dg)).card : ℝ) ≤ 1 + Cd * ((k : ℝ) + 3) := by
    have h1 : (range N).filter (· ∈ Dg) ⊆ Dg := fun x hx => (mem_filter.1 hx).2
    have h2 := card_le_card h1
    have h3 := card_insert_le 0 ((Finset.Ico 1 N).filter fun d =>
      (3 : ℤ) ^ A - 1 ∣ 2 * ((h' : ℤ) * ((b : ℤ) ^ d - 1)) * (t : ℤ) ^ N)
    have h4 := hCd k (by omega)
    have : (((range N).filter (· ∈ Dg)).card : ℝ) ≤
        (((Finset.Ico 1 N).filter fun d =>
          (3 : ℤ) ^ A - 1 ∣ 2 * ((h' : ℤ) * ((b : ℤ) ^ d - 1)) * (t : ℤ) ^ N).card : ℝ) + 1 := by
      exact_mod_cast h2.trans h3
    push_cast [b] at h4 this ⊢
    linarith
  have hrows : ∑ d ∈ range N, ∑ m ∈ range N, G d m ≤ N * (N * ψ k) + N * (1 + Cd * ((k : ℝ) + 3)) := by
    refine (sum_le_sum hrow).trans ?_
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_filter, sum_const, nsmul_eq_mul]
    have := mul_le_mul_of_nonneg_right hDgc (Nat.cast_nonneg N)
    linarith
  -- the single orbit
  have hsingle : ∑ n ∈ range N, cycProd A ((h' : ℤ) * (t : ℤ) ^ n) ≤ N * ψ k :=
    hRk h' (hA0 A N (by omega) hA1 |> fun h hd => h (by simpa [mul_assoc] using hd))
  -- assemble
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  have hN0 : (0 : ℝ) < N := by positivity
  have hfin : (N : ℝ) * (1 + Cd * ((k : ℝ) + 3)) ≤ (N : ℝ) ^ 2 * ((1 + |Cd| * ((k : ℝ) + 3)) / N) := by
    rw [sq, mul_assoc, mul_div_cancel₀ _ hN0.ne']
    exact mul_le_mul_of_nonneg_left (by nlinarith [le_abs_self Cd, (by positivity : (0:ℝ) ≤ (k:ℝ) + 3)]) hN0.le
  simp only [ψ', ← hN]
  have e2 : (N : ℝ) ^ 2 * (3 * ψ k + 2 * (1 + |Cd| * ((k : ℝ) + 3)) / N) =
      3 * (N * (N * ψ k)) + 2 * ((N : ℝ) ^ 2 * ((1 + |Cd| * ((k : ℝ) + 3)) / N)) := by ring
  rw [e2]
  have := mul_le_mul_of_nonneg_left hsingle hN0.le
  simp only [G] at hpair hrows
  have e3 : ∑ x ∈ range N, (N : ℝ) * cycProd A ((h' : ℤ) * (t : ℤ) ^ x) =
      N * ∑ x ∈ range N, cycProd A ((h' : ℤ) * (t : ℤ) ^ x) := (mul_sum _ _ _).symm
  linarith [hpair, hrows, hfin, e3]

section SchedTail

noncomputable def gT (x : ℝ) : ℝ := (Real.sqrt x + 1 / 2) * Real.exp (-2 * Real.sqrt x)

theorem hasDerivAt_gT {x : ℝ} (hx : 0 < x) : HasDerivAt gT (-Real.exp (-2 * Real.sqrt x)) x := by
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := by
    have := (hasDerivAt_id x).sqrt hx.ne'; simpa using this
  have h1 := (hs.add_const (1 / 2)).mul ((hs.const_mul (-2)).exp)
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  unfold gT
  refine h1.congr_deriv ?_
  field_simp
  ring

theorem gT_step (j : ℕ) : Real.exp (-2 * Real.sqrt (j + 1)) ≤ gT j - gT (j + 1) := by
  have hcont : ContinuousOn gT (Set.Icc (j : ℝ) (j + 1)) := by
    unfold gT; fun_prop
  obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope gT (fun x => -Real.exp (-2 * Real.sqrt x))
    (by linarith : (j : ℝ) < j + 1) hcont
    (fun x hx => hasDerivAt_gT (lt_of_le_of_lt (Nat.cast_nonneg j) hx.1))
  have : gT (j + 1) - gT j = -Real.exp (-2 * Real.sqrt ξ) := by
    rw [hd]; ring
  have hle : Real.exp (-2 * Real.sqrt (j + 1)) ≤ Real.exp (-2 * Real.sqrt ξ) := by
    apply Real.exp_le_exp.2
    have := Real.sqrt_le_sqrt hξ.2.le
    linarith
  linarith

theorem sum_exp_sqrt_tele (J n : ℕ) :
    ∑ j ∈ Finset.Ico (J + 1) (J + 1 + n), Real.exp (-2 * Real.sqrt j) ≤ gT J - gT (J + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have hstep := gT_step (J + n)
    push_cast at hstep ⊢
    rw [show (J : ℝ) + 1 + n = J + n + 1 by ring]
    rw [show (J : ℝ) + (n + 1) = J + n + 1 by ring]
    linarith

theorem sum_exp_sqrt_le (J n : ℕ) :
    ∑ j ∈ Finset.Ico (J + 1) (J + 1 + n), Real.exp (-2 * Real.sqrt j) ≤ gT J := by
  have := sum_exp_sqrt_tele J n
  have hpos : 0 ≤ gT (J + n) := by unfold gT; positivity
  linarith

theorem exp_sqrt_le_sched (j : ℕ) : Real.exp (Real.sqrt j) ≤ sched j := by
  unfold sched; push_cast
  have h1 := Nat.lt_floor_add_one (Real.exp (Real.sqrt j))
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    linarith

theorem sched_le_three_exp (j : ℕ) : (sched j : ℝ) ≤ 3 * Real.exp (Real.sqrt j) := by
  unfold sched; push_cast
  have h1 := Nat.floor_le (Real.exp_pos (Real.sqrt j)).le
  have h2 : (j : ℝ) ≤ 2 * Real.exp (Real.sqrt j) := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
    have := Real.quadratic_le_exp_of_nonneg (Real.sqrt_nonneg (j : ℝ))
    nlinarith [Real.sqrt_nonneg (j : ℝ)]
  linarith

theorem decr_aux {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b + 3 / 2) * Real.exp (-2 * b) ≤ (a + 3 / 2) * Real.exp (-2 * a) := by
  have h := Real.add_one_le_exp (2 * (b - a))
  have e : Real.exp (-2 * a) = Real.exp (-2 * b) * Real.exp (2 * (b - a)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hp := Real.exp_pos (-2 * b)
  have h2 : b + 3 / 2 ≤ (a + 3 / 2) * Real.exp (2 * (b - a)) := by
    have : b + 3 / 2 ≤ (a + 3 / 2) * (2 * (b - a) + 1) := by nlinarith
    exact this.trans (mul_le_mul_of_nonneg_left h (by linarith))
  calc (b + 3 / 2) * Real.exp (-2 * b) ≤ (a + 3 / 2) * Real.exp (2 * (b - a)) * Real.exp (-2 * b) :=
        mul_le_mul_of_nonneg_right h2 hp.le
    _ = _ := by ring

theorem sched_tail (X : ℝ) (hX : 1 ≤ X) (n : ℕ) :
    ∑ j ∈ Finset.range n, (if X ≤ (sched j : ℝ) then 1 / (sched j : ℝ) ^ 2 else 0) ≤
      9 * (Real.log X + 3) / X ^ 2 := by
  set y := max (Real.log (X / 3)) 0
  have hy0 : 0 ≤ y := le_max_right _ _
  set J := ⌈y ^ 2⌉₊
  have hJ : y ≤ Real.sqrt J := by
    rw [← Real.sqrt_sq hy0]; exact Real.sqrt_le_sqrt (Nat.le_ceil _)
  have hpt : ∀ j ∈ Finset.range n, (if X ≤ (sched j : ℝ) then 1 / (sched j : ℝ) ^ 2 else 0) ≤
      if J ≤ j then Real.exp (-2 * Real.sqrt j) else 0 := by
    intro j _
    split_ifs with h1 h2
    · have h3 := exp_sqrt_le_sched j
      have hsp : (0 : ℝ) < sched j := lt_of_lt_of_le (Real.exp_pos _) h3
      rw [div_le_iff₀ (by positivity)]
      calc (1 : ℝ) = Real.exp (-2 * Real.sqrt j) * (Real.exp (Real.sqrt j) * Real.exp (Real.sqrt j)) := by
            rw [← Real.exp_add, ← Real.exp_add, show -2 * Real.sqrt j + (Real.sqrt j + Real.sqrt j) = 0 by ring,
              Real.exp_zero]
        _ ≤ Real.exp (-2 * Real.sqrt j) * (sched j : ℝ) ^ 2 := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            rw [sq]; exact mul_le_mul h3 h3 (Real.exp_pos _).le hsp.le
    · exfalso; apply h2
      have h3 := (h1.trans (sched_le_three_exp j))
      have hl : Real.log (X / 3) ≤ Real.sqrt j := by
        rw [Real.log_le_iff_le_exp (by positivity)]; linarith
      have hyj : y ≤ Real.sqrt j := max_le hl (Real.sqrt_nonneg _)
      have : y ^ 2 ≤ j := by
        have := pow_le_pow_left₀ hy0 hyj 2
        rwa [Real.sq_sqrt (Nat.cast_nonneg _)] at this
      exact Nat.ceil_le.2 this
    · positivity
    · exact le_rfl
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.sum_filter]
  have hsub : (Finset.range n).filter (fun j => J ≤ j) ⊆ insert J (Finset.Ico (J + 1) (J + 1 + n)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    rcases hj.2.eq_or_lt with h | h
    · rw [← h]; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_Ico.2 ⟨h, by omega⟩)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => (Real.exp_pos _).le).trans ?_
  rw [Finset.sum_insert (by simp)]
  have h1 := sum_exp_sqrt_le J n
  -- (√J + 3/2) e^{-2√J} ≤ (y + 3/2) e^{-2y}
  have h2 := decr_aux hy0 hJ
  have hg : Real.exp (-2 * Real.sqrt J) + gT J = (Real.sqrt J + 3 / 2) * Real.exp (-2 * Real.sqrt J) := by
    unfold gT; ring
  have hfin : (y + 3 / 2) * Real.exp (-2 * y) ≤ 9 * (Real.log X + 3) / X ^ 2 := by
    have hX0 : 0 < X := by linarith
    have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
    have hl3 : Real.log 3 < 2 := by
      have := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 3) (by norm_num); linarith
    have hl3' : 0 < Real.log 3 := Real.log_pos (by norm_num)
    rcases le_total (Real.log (X / 3)) 0 with h | h
    · have hy : y = 0 := max_eq_right h
      rw [hy]; simp only [mul_zero, Real.exp_zero, mul_one, zero_add]
      have hX3 : X ≤ 3 := by
        have := (Real.log_nonpos_iff (by positivity)).1 h
        rw [div_le_one (by norm_num)] at this; exact this
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · have hy : y = Real.log (X / 3) := max_eq_left h
      rw [hy, Real.log_div hX0.ne' (by norm_num)]
      have he : Real.exp (-2 * (Real.log X - Real.log 3)) = 9 / X ^ 2 := by
        rw [show -2 * (Real.log X - Real.log 3) = 2 * Real.log 3 - 2 * Real.log X by ring,
          Real.exp_sub, ← Real.log_rpow (by norm_num), ← Real.log_rpow hX0, Real.exp_log (by positivity),
          Real.exp_log (by positivity)]
        norm_num
      rw [he]
      rw [mul_div_assoc', div_le_div_iff_of_pos_right (by positivity)]
      nlinarith
  linarith

end SchedTail

section CopySched

theorem runStart_le_pow (k : ℕ) : runStart k ≤ (2 * k + 4) ^ (k + 1) := by
  induction k with
  | zero => simp [runStart]
  | succ k ih =>
    rw [runStart_succ_eq]
    calc 2 * (k + 2) * runStart k ≤ (2 * (k + 1) + 4) * (2 * k + 4) ^ (k + 1) := by
          apply Nat.mul_le_mul (by omega) ih
      _ ≤ (2 * (k + 1) + 4) * (2 * (k + 1) + 4) ^ (k + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by ring

theorem log_runStart_le (k : ℕ) : Real.log (runStart k) ≤ 2 * ((k : ℝ) + 3) ^ 2 - 3 := by
  have h1 : (runStart k : ℝ) ≤ ((2 * k + 4 : ℕ) : ℝ) ^ (k + 1) := by exact_mod_cast runStart_le_pow k
  have hpos : (0 : ℝ) < runStart k := by exact_mod_cast (Nat.zero_lt_of_lt (lt_runStart k))
  have h2 := Real.log_le_log hpos h1
  rw [Real.log_pow] at h2
  have h3 : Real.log ((2 * k + 4 : ℕ) : ℝ) ≤ ((2 * k + 4 : ℕ) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  push_cast at h2 h3
  have : ((k + 1 : ℕ) : ℝ) * Real.log (2 * k + 4) ≤ ((k : ℝ) + 1) * (2 * k + 3) := by
    push_cast; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  push_cast at this
  nlinarith

/-- The per-run weight bound: `N_k² · 9(log X_k + 3)/X_k² ≤ 288 s² (k+3)⁴` with `X_k = a_k/(4s)`. -/
theorem run_tail_weight {s : ℕ} (hs : 1 ≤ s) (k : ℕ) (hX : 1 ≤ (runStart k : ℝ) / (4 * s)) :
    ((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2 *
        (9 * (Real.log ((runStart k : ℝ) / (4 * s)) + 3) / ((runStart k : ℝ) / (4 * s)) ^ 2) ≤
      288 * (s : ℝ) ^ 2 * ((k : ℝ) + 3) ^ 4 := by
  set a : ℝ := (runStart k : ℝ) with had
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have ha : 4 * (s : ℝ) ≤ a := by rwa [le_div_iff₀ (by positivity), one_mul] at hX
  have ha0 : 0 < a := by linarith
  have hN : ((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ≤ ((k : ℝ) + 3) * a := by
    push_cast; nlinarith
  have hlog : Real.log (a / (4 * s)) + 3 ≤ 2 * ((k : ℝ) + 3) ^ 2 := by
    have := log_runStart_le k
    have : Real.log (a / (4 * s)) ≤ Real.log a :=
      Real.log_le_log (by positivity) (div_le_self ha0.le (by linarith))
    linarith
  have hl0 : 0 ≤ Real.log (a / (4 * s)) := Real.log_nonneg hX
  rw [div_pow, mul_div_assoc', div_div_eq_mul_div, mul_comm]
  rw [div_le_iff₀ (by positivity)]
  have hNsq : ((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2 ≤ ((k : ℝ) + 3) ^ 2 * a ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hN 2
  have hk : (0 : ℝ) ≤ ((k : ℝ) + 3) ^ 2 := by positivity
  have h1 : ((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2 * (9 * (Real.log (a / (4 * s)) + 3)) ≤
      ((k : ℝ) + 3) ^ 2 * a ^ 2 * (9 * (2 * ((k : ℝ) + 3) ^ 2)) :=
    mul_le_mul hNsq (by linarith) (by positivity) (by positivity)
  calc (4 * (s : ℝ)) ^ 2 * (((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2 * (9 * (Real.log (a / (4 * s)) + 3)))
      ≤ (4 * (s : ℝ)) ^ 2 * (((k : ℝ) + 3) ^ 2 * a ^ 2 * (9 * (2 * ((k : ℝ) + 3) ^ 2))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

/-- The copy-run sum of run `k` (the `hCopy` summand of `repPairPos_explicit`). -/
noncomputable def runCopy (s t h' k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range ((k + 2) * runStart k + 1), ∑ m ∈ Finset.range ((k + 2) * runStart k + 1),
    (cycProd (runStart k) ((h' : ℤ) * (((3 ^ s * t : ℕ) : ℤ) ^ n - ((3 ^ s * t : ℕ) : ℤ) ^ m))
      + cycProd (runStart k) ((h' : ℤ) * (t : ℤ) ^ n))

theorem runCopy_nonneg (s t h' k : ℕ) : 0 ≤ runCopy s t h' k :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    add_nonneg (cycProd_nonneg _ _) (cycProd_nonneg _ _)

/-- **Copy sums are summable along `sched`** (the sum swap).  From per-run bounds
`runCopy k ≤ N_k² ψ_k` (`k ≥ k₁`) with `Σ ψ_k (k+3)⁴ < ∞`: for fixed `k` the `j` with
`a_k ≤ 2s·sched j + e` have `sched j ≥ a_k/(4s)`, and `sched_tail` bounds their weight. -/
theorem summable_copy_sched {s t e h' : ℕ} (hs : 1 ≤ s) (ψ : ℕ → ℝ) (hψ0 : ∀ k, 0 ≤ ψ k)
    (hψs : Summable (fun k => ψ k * ((k : ℝ) + 3) ^ 4)) (k₁ : ℕ)
    (hb : ∀ k, k₁ ≤ k → runCopy s t h' k ≤ ((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2 * ψ k) :
    Summable fun j => (∑ k ∈ (Finset.range (Nat.log 4 (s * (2 * sched j) + e) + 1)).filter
        (fun k => runStart k ≤ s * (2 * sched j) + e), runCopy s t h' k) / ((sched j : ℝ) ^ 2) := by
  set k₃ := max k₁ (2 * e + 4 * s)
  set C₀ := ∑ k ∈ Finset.range k₃, runCopy s t h' k
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg fun _ _ => runCopy_nonneg _ _ _ _
  let F : ℕ → ℕ → ℝ := fun k j => if k₃ ≤ k ∧ runStart k ≤ s * (2 * sched j) + e then
    ((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2 * ψ k / (sched j : ℝ) ^ 2 else 0
  have hF0 : ∀ k j, 0 ≤ F k j := fun k j => by
    simp only [F]; split_ifs
    · exact div_nonneg (mul_nonneg (by positivity) (hψ0 k)) (by positivity)
    · exact le_rfl
  let G : ℕ → ℝ := fun j => ∑ k ∈ Finset.range (s * (2 * sched j) + e + 1), F k j
  have hsch : ∀ j, (0 : ℝ) < sched j := fun j => by exact_mod_cast one_le_sched j
  -- pointwise split
  have hpt : ∀ j, (∑ k ∈ (Finset.range (Nat.log 4 (s * (2 * sched j) + e) + 1)).filter
        (fun k => runStart k ≤ s * (2 * sched j) + e), runCopy s t h' k) / ((sched j : ℝ) ^ 2) ≤
      C₀ * (sched j : ℝ) ^ (-(2 : ℝ)) + G j := by
    intro j
    set Ks := (Finset.range (Nat.log 4 (s * (2 * sched j) + e) + 1)).filter
        (fun k => runStart k ≤ s * (2 * sched j) + e)
    have hsplit := Finset.sum_filter_add_sum_filter_not Ks (fun k => k < k₃) (runCopy s t h')
    have h1 : ∑ k ∈ Ks.filter (fun k => k < k₃), runCopy s t h' k ≤ C₀ :=
      Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => Finset.mem_range.2 (Finset.mem_filter.1 hk).2)
        fun _ _ _ => runCopy_nonneg _ _ _ _
    have h2 : ∑ k ∈ Ks.filter (fun k => ¬ k < k₃), runCopy s t h' k ≤
        ∑ k ∈ Finset.range (s * (2 * sched j) + e + 1), F k j * (sched j : ℝ) ^ 2 := by
      have hsub : Ks.filter (fun k => ¬ k < k₃) ⊆ Finset.range (s * (2 * sched j) + e + 1) := by
        intro k hk
        have := (Finset.mem_filter.1 (Finset.mem_filter.1 hk).1).2
        have := lt_runStart k
        exact Finset.mem_range.2 (by omega)
      refine (Finset.sum_le_sum fun k hk => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => mul_nonneg (hF0 k j) (by positivity))
      have hk := Finset.mem_filter.1 hk
      have hk2 := (Finset.mem_filter.1 hk.1).2
      have hk3 : k₃ ≤ k := by omega
      simp only [F, if_pos (⟨hk3, hk2⟩ : k₃ ≤ k ∧ _)]
      rw [div_mul_cancel₀ _ (pow_ne_zero 2 (hsch j).ne')]
      exact hb k (le_trans (le_max_left _ _) hk3)
    rw [div_le_iff₀ (pow_pos (hsch j) 2), add_mul, ← hsplit]
    have e1 : C₀ * (sched j : ℝ) ^ (-(2 : ℝ)) * (sched j : ℝ) ^ 2 = C₀ := by
      rw [Real.rpow_neg (hsch j).le, mul_assoc, Real.rpow_two, inv_mul_cancel₀ (pow_ne_zero 2 (hsch j).ne'), mul_one]
    have e2 : G j * (sched j : ℝ) ^ 2 =
        ∑ k ∈ Finset.range (s * (2 * sched j) + e + 1), F k j * (sched j : ℝ) ^ 2 := by
      simp only [G]; rw [Finset.sum_mul]
    rw [e1, e2]; linarith
  refine Summable.of_nonneg_of_le (fun j => div_nonneg (Finset.sum_nonneg fun _ _ =>
    runCopy_nonneg _ _ _ _) (by positivity)) hpt
    (((CantorExactExponentProfile.summable_sched_rpow (by norm_num : (0 : ℝ) < 2)).mul_left C₀).add ?_)
  -- summability of G by the sum swap
  refine summable_of_sum_range_le (fun j => Finset.sum_nonneg fun k _ => hF0 k j)
    (c := 288 * (s : ℝ) ^ 2 * ∑' k, ψ k * ((k : ℝ) + 3) ^ 4) fun n => ?_
  set B := s * (2 * ∑ j ∈ Finset.range n, sched j) + e + 1
  have hext : ∀ j ∈ Finset.range n, G j ≤ ∑ k ∈ Finset.range B, F k j := by
    intro j hj
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 ?_) fun k _ _ => hF0 k j
    have := Finset.single_le_sum (fun i _ => Nat.zero_le (sched i)) hj
    have : s * (2 * sched j) ≤ s * (2 * ∑ j ∈ Finset.range n, sched j) := by
      apply Nat.mul_le_mul_left; omega
    omega
  refine (Finset.sum_le_sum hext).trans ?_
  rw [Finset.sum_comm]
  have hcol : ∀ k, ∑ j ∈ Finset.range n, F k j ≤ 288 * (s : ℝ) ^ 2 * (ψ k * ((k : ℝ) + 3) ^ 4) := by
    intro k
    by_cases hk : k₃ ≤ k
    · set X : ℝ := (runStart k : ℝ) / (4 * s)
      have hk' : 2 * e + 4 * s ≤ k := le_trans (le_max_right _ _) hk
      have hak := lt_runStart k
      have hs' : (0 : ℝ) < 4 * s := by positivity
      have hX1 : 1 ≤ X := by
        rw [le_div_iff₀ hs', one_mul]; exact_mod_cast (by omega : 4 * s ≤ runStart k)
      have hpt2 : ∀ j ∈ Finset.range n, F k j ≤ ((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2 * ψ k *
          (if X ≤ (sched j : ℝ) then 1 / (sched j : ℝ) ^ 2 else 0) := by
        intro j _
        simp only [F]
        split_ifs with h1 h2
        · rw [mul_one_div]
        · exfalso; apply h2
          rw [div_le_iff₀ hs']
          have e1 : s * (2 * sched j) = 2 * (s * sched j) := by ring
          have e2 : 4 * s * sched j = 4 * (s * sched j) := by ring
          have h3 : runStart k ≤ 4 * s * sched j := by have := h1.2; omega
          calc (runStart k : ℝ) ≤ ((4 * s * sched j : ℕ) : ℝ) := by exact_mod_cast h3
            _ = _ := by push_cast; ring
        · exact mul_nonneg (mul_nonneg (by positivity) (hψ0 k)) (by positivity)
        · simp
      refine (Finset.sum_le_sum hpt2).trans ?_
      rw [← Finset.mul_sum]
      have ht := sched_tail X hX1 n
      have hw := run_tail_weight hs k hX1
      have hA : 0 ≤ ((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2 * ψ k :=
        mul_nonneg (by positivity) (hψ0 k)
      calc _ ≤ ((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2 * ψ k * (9 * (Real.log X + 3) / X ^ 2) :=
            mul_le_mul_of_nonneg_left ht hA
        _ = ψ k * (((((k + 2) * runStart k + 1 : ℕ) : ℝ)) ^ 2 * (9 * (Real.log X + 3) / X ^ 2)) := by ring
        _ ≤ ψ k * (288 * (s : ℝ) ^ 2 * ((k : ℝ) + 3) ^ 4) := mul_le_mul_of_nonneg_left hw (hψ0 k)
        _ = _ := by ring
    · have : ∀ j ∈ Finset.range n, F k j = 0 := fun j _ => by
        simp only [F]; rw [if_neg (fun h => hk h.1)]
      rw [Finset.sum_eq_zero this]
      exact mul_nonneg (by positivity) (mul_nonneg (hψ0 k) (by positivity))
  refine (Finset.sum_le_sum fun k _ => hcol k).trans ?_
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (hψs.sum_le_tsum _ fun k _ => mul_nonneg (hψ0 k) (by positivity))
    (by positivity)
/-- **Per-`N` bound with the copy term left explicit.**  `repPairPos_eventually` without the
copy-zone inputs: every class keeps its power saving except the copy runs, which are carried as
`2 Σ_k runCopy k` (bounded run by run in `repPairArith_of_runDecay`). -/
theorem repPairPos_copy {s t : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (h3t : ¬ 3 ∣ t)
    (hB : CantorExactExponentProfile.Literature.BakerLogDiscrepancy)
    (e h' : ℕ) (hh : 1 ≤ h') (hnd : ¬ 3 ∣ h') :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N → ∃ (M : ℕ) (κ : ℕ → ℕ → Option ℕ),
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        repBound M (κ n m) (((3 ^ e * h' : ℕ) : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ n -
          ((3 ^ s * t : ℕ) : ℝ) ^ m)) ≤ C * (N : ℝ) ^ (2 - δ) +
          2 * ∑ k ∈ (Finset.range (Nat.log 4 (s * (2 * N) + e) + 1)).filter
            (fun k => runStart k ≤ s * (2 * N) + e), runCopy s t h' k := by
  obtain ⟨Cb, κb, hκb, hCb⟩ := sum_class_top_le ht h3t hB
  set q : ℕ := ⌈4 / κb⌉₊ + 2 with hqd
  have hq : 1 ≤ q := by omega
  have hq2 : (2 : ℝ) ≤ q := by simp only [hqd]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈4 / κb⌉₊]
  have hqκ : 4 / κb ≤ q := by
    simp only [hqd]; push_cast; linarith [Nat.le_ceil (4 / κb)]
  have hq0 : (0 : ℝ) < q := by linarith
  obtain ⟨Cd, hCd⟩ := badTerm_le hq (3 ^ e * h' + runStart ((t + 2) * (t + 3))) (2 * (s + t))
    (3 ^ e * h' + e)
  have hlg : Real.logb 3 (2 / 3) < 0 := Real.logb_neg (by norm_num) (by norm_num) (by norm_num)
  set η : ℝ := -(Real.logb 3 (2 / 3)) / q
  have hη : 0 < η := div_pos (by linarith) hq0
  set δ : ℝ := min (min η (q : ℝ)⁻¹) (min (κb / 2) (min (1 / 4) (1 / 4)))
  have hδ0 : 0 < δ := lt_min (lt_min hη (by positivity)) (lt_min (by positivity) (lt_min (by norm_num) (by norm_num)))
  have hδη : δ ≤ η := (min_le_left _ _).trans (min_le_left _ _)
  have hδq : δ ≤ (q : ℝ)⁻¹ := (min_le_left _ _).trans (min_le_right _ _)
  have hδκ : δ ≤ κb / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ4 : δ ≤ 1 / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hqinv : (q : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hq0 (by norm_num)]; linarith
  have h2q : 2 * (q : ℝ)⁻¹ ≤ κb / 2 := by
    have : 4 ≤ κb * q := by rwa [div_le_iff₀ hκb, mul_comm] at hqκ
    rw [← div_eq_mul_inv, div_le_iff₀ hq0]; nlinarith
  set cc : ℝ := (3 / 2 : ℝ) ^ CantorLiouvilleAll.tb t
  have hcc : 0 ≤ cc := by positivity
  refine ⟨1 + 2 * (cc * (9 / 2 + 4) + 6 + (8 + 8 * Real.pi) + 18 * |Cb| + |Cd|), δ, hδ0,
    fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have mono : ∀ a : ℝ, a ≤ 2 - δ → (N : ℝ) ^ a ≤ (N : ℝ) ^ (2 - δ) :=
    fun a ha => Real.rpow_le_rpow_of_exponent_le hN1 ha
  set j := Nat.log 3 N / q
  set Btop : ℝ := 3 * N * (2 / 3 : ℝ) ^ (j + 1) + 4 * N * (1 / 3 : ℝ) ^ (j + 1) +
    Cb * 9 ^ (j + 1) * (N : ℝ) ^ (1 - κb)
  have hBtop : ∀ β : ℝ, ∑ m ∈ Finset.range N,
      CantorExactExponentProfile.topProd (j + 1) (Int.fract (m * Real.logb 3 t + β)) ≤ Btop := by
    intro β
    have := hCb N hN (j + 1) 1 (fun _ => β)
    simp only [Finset.sum_range_one, Nat.cast_one, one_mul] at this; exact this
  obtain ⟨M, κ, hMκ⟩ := repPairPos_explicit hs ht h3t hh hnd j N Btop
    (∑ k ∈ (Finset.range (Nat.log 4 (s * (2 * N) + e) + 1)).filter
      (fun k => runStart k ≤ s * (2 * N) + e), runCopy s t h' k) hBtop le_rfl
  refine ⟨M, κ, hMκ.trans ?_⟩
  have e1 : 3 ^ e * h' + 2 * (s + t) * N + e = 2 * (s + t) * N + (3 ^ e * h' + e) := by ring
  rw [e1]
  have hcl := classTerms_le hq hN hcc
  have htop := topTerms_le hq hN Cb κb
  have hbad := hCd N hN
  -- exponents
  have x1 := mono (2 + Real.logb 3 (2 / 3) / q) (by
    have : Real.logb 3 (2 / 3) / q = -η := by simp only [η]; ring
    rw [this]; linarith)
  have x2 := mono (1 + (q : ℝ)⁻¹) (by linarith)
  have x3 := mono (2 - (q : ℝ)⁻¹) (by linarith)
  have x4 := mono (2 + 2 * (q : ℝ)⁻¹ - κb) (by linarith)
  have x6 := mono (3 / 2) (by linarith)
  have x7 := mono 1 (by linarith)
  rw [Real.rpow_one] at x7
  have hP : 0 ≤ (N : ℝ) ^ (2 - δ) := by positivity
  have hpi : 0 ≤ 8 + 8 * Real.pi := by positivity
  have y1 : cc * (9 / 2 * (N : ℝ) ^ (2 + Real.logb 3 (2 / 3) / q) + 4 * (N : ℝ) ^ (1 + (q : ℝ)⁻¹)) ≤
      cc * (9 / 2 + 4) * (N : ℝ) ^ (2 - δ) := by
    rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hcc; linarith
  have y2 : 6 * (N : ℝ) ^ (2 + Real.logb 3 (2 / 3) / q) + (8 + 8 * Real.pi) * (N : ℝ) ^ (2 - (q : ℝ)⁻¹) +
      18 * |Cb| * (N : ℝ) ^ (2 + 2 * (q : ℝ)⁻¹ - κb) ≤
      (6 + (8 + 8 * Real.pi) + 18 * |Cb|) * (N : ℝ) ^ (2 - δ) := by
    have := mul_le_mul_of_nonneg_left x3 hpi
    have := mul_le_mul_of_nonneg_left x4 (by positivity : (0 : ℝ) ≤ 18 * |Cb|)
    nlinarith
  have y4 : Cd * (N : ℝ) ^ ((3 : ℝ) / 2) ≤ |Cd| * (N : ℝ) ^ (2 - δ) :=
    (mul_le_mul_of_nonneg_right (le_abs_self Cd) (by positivity)).trans
      (mul_le_mul_of_nonneg_left x6 (abs_nonneg _))
  have htop' : 2 * (N : ℝ) * Btop + N * N * (Real.pi * (8 / 3 ^ (j + 1))) ≤
      6 * (N : ℝ) ^ (2 + Real.logb 3 (2 / 3) / q) + (8 + 8 * Real.pi) * (N : ℝ) ^ (2 - (q : ℝ)⁻¹) +
        18 * |Cb| * (N : ℝ) ^ (2 + 2 * (q : ℝ)⁻¹ - κb) := htop
  clear_value Btop
  linarith

end CopySched

/-- **Assembly through run orbit decay (PROVED 2026-10-08; `summable_copy_sched`, `repPairPos_copy`).**  Baker + `RunOrbitDecay t`
give `RepPairArith (3ˢt)`.

Plan.  As `repPairArith_of_inputs`, but with the copy term of `repPairPos_explicit` bounded by
`copyRun_psi` run by run: for `N ≥ 1`, `Copy(N) ≤ C₀ + N² Φ(N)` with
`Φ(N) = Σ_{k : a_k ≤ 2sN+e} (N_k/N)² ψ'_k`.  Summability of `Φ ∘ sched`: swap the sums (all
terms `≥ 0`); for fixed `k` the `j` with `sched j ≥ X_k = (a_k − e)/(2s)` contribute
`Σ sched(j)^{−2} ≲ log X_k / X_k²` (`sched j ≥ e^{√j}`), so the double sum is
`≲ Σ_k ψ'_k (k+2)² s² log a_k ≲ Σ_k ψ'_k (k+3)⁴ < ∞` (`log a_k ≤ (k+1) log(2k+4) + 2`).  The other
classes keep their power savings, and a power saving is summable along `sched`
(`summable_sched_rpow`).  The sign / `3`-part reduction is `repPairPower_of_pos` verbatim. -/
theorem repPairArith_of_runDecay {s t : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (h3t : ¬ 3 ∣ t)
    (hB : CantorExactExponentProfile.Literature.BakerLogDiscrepancy) (hR : RunOrbitDecay t) :
    RepPairArith (3 ^ s * t) := by
  intro h hh
  obtain ⟨e, h', hnd, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hh) 3
    (by norm_num)
  have h1 : 1 ≤ h' := Nat.pos_of_ne_zero (by rintro rfl; simp at hnd)
  obtain ⟨ψ, hψ0, hψs, k₁, hψ⟩ := copyRun_psi hs ht h3t hR h' h1
  have hS := summable_copy_sched (e := e) hs ψ hψ0 hψs k₁ hψ
  obtain ⟨C, δ, hδ, hC⟩ := repPairPos_copy hs ht h3t hB e h' h1 hnd
  choose M κ hMκ using fun j => hC (sched j) (one_le_sched j)
  refine ⟨M, κ, ?_⟩
  have habs : ((3 ^ e * h' : ℕ) : ℝ) = |(h : ℝ)| := by
    rw [← he, Nat.cast_natAbs, Int.cast_abs]
  have hsign : ∀ (Mj : ℕ) (κj : ℕ → ℕ → Option ℕ) (N : ℕ),
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        repBound Mj (κj n m) ((h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m)) =
      ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        repBound Mj (κj n m) (((3 ^ e * h' : ℕ) : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ n -
          ((3 ^ s * t : ℕ) : ℝ) ^ m)) := by
    intro Mj κj N
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [habs]
    rcases abs_choice (h : ℝ) with ha | ha <;> rw [ha]
    rw [show -(h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m) =
      -((h : ℝ) * (((3 ^ s * t : ℕ) : ℝ) ^ n - ((3 ^ s * t : ℕ) : ℝ) ^ m)) by ring, repBound_neg]
  refine (((CantorExactExponentProfile.summable_sched_rpow hδ).mul_left C).add
    (hS.mul_left 2)).of_nonneg_of_le
    (fun j => div_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_)
      (by positivity)) (fun j => ?_)
  · rcases κ j _ _ with _ | k <;> simp only [repBound]
    · exact Bf_nonneg _ _ _
    · split_ifs
      · exact Finset.prod_nonneg fun _ _ => abs_nonneg _
      · exact zero_le_one
  · have hN : (0 : ℝ) < sched j := by exact_mod_cast one_le_sched j
    rw [hsign, div_le_iff₀ (by positivity)]
    refine (hMκ j).trans (le_of_eq ?_)
    rw [add_mul, mul_assoc, mul_div_assoc', div_mul_cancel₀ _ (by positivity),
      ← Real.rpow_natCast (sched j : ℝ) 2, ← Real.rpow_add hN]
    norm_num; left; ring_nf

/-- **The crux from the two cited inputs (proved, modulo the leaves above).**  Baker's discrepancy
for `m log₃ t` and Matveev's three-logarithm bound give `RepPairArith b` for every `b = 3ˢt`,
`t > 1`. -/
theorem repPairArith_of_literature (hB : CantorExactExponentProfile.Literature.BakerLogDiscrepancy)
    (hM : SparseIdentity.Literature.MatveevThreeLogs) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b)
    (hpow : ∀ s : ℕ, b ≠ 3 ^ s) : RepPairArith b := by
  obtain ⟨s, t, hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : b ≠ 0) 3 (by norm_num)
  have ht0 : t ≠ 0 := by rintro rfl; simp at hnd
  have ht1 : t ≠ 1 := by rintro rfl; exact hpow s (mul_one _)
  have hs : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at h3; exact absurd h3 hnd
    · exact h
  exact repPairArith_of_runDecay hs (by omega) hnd hB
    (runOrbitDecay_of_sparse (by omega) hnd
      (SparseIdentity.sparseIdentityBound_of_matveev hM (by omega) hnd))

/-- **The crux from Baker and the 3-adic two-logarithm bound (proved).**  As
`repPairArith_of_literature`, with Matveev (three archimedean logarithms) replaced by the 3-adic
chain `SparseIdentity.sparseIdentityBound_of_padic` (two 3-adic logarithms). -/
theorem repPairArith_of_baker_padic
    (hB : CantorExactExponentProfile.Literature.BakerLogDiscrepancy)
    (hP : SparseIdentity.Literature.PadicTwoLogs) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b)
    (hpow : ∀ s : ℕ, b ≠ 3 ^ s) : RepPairArith b := by
  obtain ⟨s, t, hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : b ≠ 0) 3 (by norm_num)
  have ht0 : t ≠ 0 := by rintro rfl; simp at hnd
  have ht1 : t ≠ 1 := by rintro rfl; exact hpow s (mul_one _)
  have hs : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at h3; exact absurd h3 hnd
    · exact h
  exact repPairArith_of_runDecay hs (by omega) hnd hB
    (runOrbitDecay_of_sparse (by omega) hnd
      (SparseIdentity.sparseIdentityBound_of_padic hP (by omega) hnd))

/-- **The shadow zone needs no Baker input (open; believed, 80%).**  `RepPairArith (3ˢt)` from
`SparseIdentityBound t` alone: classes 2 and 4 of `pairMaj` (a window end in the fresh stretch
after an even run, the other end deep inside it), the only users of
`Literature.BakerLogDiscrepancy`, are bounded by the copy-zone orbit count instead.

English proof (review lap 10).  Take a pair with `ξ = 3^v Z`, `v = sm + e`, `Z = h'(bᵈ − 1)tᵐ`,
`v` deep inside even run `k` (`A = a_k`, `E = (k+2)A`) and all places of `[E, top + 2]` fresh
(true for `k ≥ k₀`: the top is `≤ ρ²v` and `a_{k+2}/E = 4(k+3)`).  Split
`Z = Z_top·3^g + Z_low`, `g = E − v`.
1. *Copy option.*  `repBound_some_add` drops `Z_top`: the bound is `cycProdR A (I − f)` with
   `I = 3^{v−A} Z_low ∈ ℤ` and `f = Z_low/3^g ∈ [0, 1)`.  On the coins `i < A − 5` the
   perturbation `f·3ⁱ/(3^A − 1)` is `≤ 3⁻⁵`, so a cyclic digit change of `I` there still costs a
   factor `≤ cos(π/10)`.  Copy option `≥ θ` forces `≤ K₁ + 6` cyclic changes of `I`, where
   `cos(π/10)^{K₁} < θ`.
2. *Free option.*  The fresh place `E − 1 + q` reads `(Z_top + f)/3^q`, whose two leading
   ternary digits are digits `q − 1, q − 2` of `Z_top`; so free option `≥ θ` forces `≤ K₁`
   digit changes of `Z_top`, i.e. `2Z_top` is `IsSparse3 (K₁ + 1)` (`2y = 3y − y`).
3. *Both large.*  `3^{E−A} ≡ 1 (mod 3^A − 1)`, so `2·3^{v−A}Z ≡ 2I + 2Z_top` is a sum of
   `≤ 2K₁ + 8` terms `±3ʲ, ±2·3ʲ` (exponents mod `A`, possibly repeated); carrying gives
   `CycSparse A (C K₁)`.  So the orbit point `c tᵐ`, `c = h'(bᵈ − 1)`, is cyclically sparse.  (If
   the top of `ξ` leaves the fresh stretch, the pair is separated and the same argument runs on
   the low piece `Y = 3^v h' tᵐ` with `c = h'`.)
4. *Count.*  Per row `d`, the `m < N_k` with `c tᵐ` cyclically sparse number
   `≤ (N_k/D + 1)(L_K + 1)` (`card_cluster_le`, `cyclic_pair_identity`, `SparseIdentityBound`, as
   in `runOrbitDecay_of_sparse`); degenerate rows by `card_degRows_le`.  So these pairs cost
   `≤ N²θ + N·O(k K L_K N_k / A)`, the `ψ_k` shape of `copyRun_psi`, summable along `sched` by
   `summable_copy_sched`.
Risk (why 80%): the carry normalization in step 3 with repeated exponents, and the bookkeeping of
the separated sub-case. -/
theorem repPairArith_of_sparse {s t : ℕ} (hs : 1 ≤ s) (ht : 2 ≤ t) (h3t : ¬ 3 ∣ t)
    (hS : SparseIdentity.SparseIdentityBound t) : RepPairArith (3 ^ s * t) := by
  sorry

/-- **The crux from the 3-adic two-logarithm bound alone (proved from `repPairArith_of_sparse`).**
One cited input: `SparseIdentity.Literature.PadicTwoLogs`. -/
theorem repPairArith_of_padic (hP : SparseIdentity.Literature.PadicTwoLogs) {b : ℕ} (hb : 2 ≤ b)
    (h3 : 3 ∣ b) (hpow : ∀ s : ℕ, b ≠ 3 ^ s) : RepPairArith b := by
  obtain ⟨s, t, hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : b ≠ 0) 3 (by norm_num)
  have ht0 : t ≠ 0 := by rintro rfl; simp at hnd
  have ht1 : t ≠ 1 := by rintro rfl; exact hpow s (mul_one _)
  have hs : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at h3; exact absurd h3 hnd
    · exact h
  exact repPairArith_of_sparse hs (by omega) hnd
    (SparseIdentity.sparseIdentityBound_of_padic hP (by omega) hnd)

/-- **The crux, arithmetic form (open).**  This is `repPairArith_of_literature` applied to the
two cited inputs, Baker–Wüstholz with Erdős–Turán
(`CantorExactExponentProfile.Literature.BakerLogDiscrepancy`) and Matveev's three-logarithm bound
(`SparseIdentity.Literature.MatveevThreeLogs`).  Cited results enter only as hypothesis `Prop`s,
so this unconditional form stays a direct `sorry`; the honest conditional headline is
`liouvilleCantorFullProfile_of_literature`, whose every route leaf is proved (2026-10-08), so its
`#print axioms` is the trust base and only the two cited `Prop`s remain as hypotheses.

Review lap 10 (2026-10-08): the live route to this `sorry` is `repPairArith_of_padic`, one cited
input (`SparseIdentity.Literature.PadicTwoLogs`, 3-adic, two logarithms, rational numbers), via
the proved 3-adic chain `sparseIdentityBound_of_padic` and the open Baker-free shadow dichotomy
`repPairArith_of_sparse`.  Closing it means formalizing that 3-adic bound (interpolation
determinants), the campaign set in DIRECTION.md. -/
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

/-- **The full profile, almost surely, from the crux in arithmetic form.** -/
theorem ae_repProfile_of (hcrux : ∀ b : ℕ, 2 ≤ b → 3 ∣ b → (∀ s : ℕ, b ≠ 3 ^ s) → RepPairArith b) :
    ∀ᵐ ω ∂coinMeasure,
    ∀ b : ℕ, 2 ≤ b → (IsNormal b (repReal ω) ↔ ∀ s : ℕ, b ≠ 3 ^ s) := by
  have hall : ∀ᵐ ω ∂coinMeasure, ∀ b : ℕ, 2 ≤ b → (∀ s : ℕ, b ≠ 3 ^ s) →
      IsNormal b (repReal ω) := by
    rw [ae_all_iff]
    intro b
    by_cases hb : 2 ≤ b
    · by_cases hp : ∀ s : ℕ, b ≠ 3 ^ s
      · by_cases h3 : 3 ∣ b
        · filter_upwards [ae_isNormal_rep_of_pairDecay hb (repPairDecay_of_arith (hcrux b hb h3 hp))] with ω hω _ _ using hω
        · filter_upwards [ae_isNormal_rep_of_coprime_three hb h3] with ω hω _ _ using hω
      · exact Eventually.of_forall fun ω _ h => absurd h hp
    · exact Eventually.of_forall fun ω h => absurd h hb
  filter_upwards [hall] with ω hω b hb
  refine ⟨fun hn s hs => ?_, hω b hb⟩
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · subst h0; rw [hs] at hb; norm_num at hb
  · exact not_isNormal_rep_three_pow ω h0 (hs ▸ hn)

/-- **The full profile, almost surely.** -/
theorem ae_repProfile : ∀ᵐ ω ∂coinMeasure,
    ∀ b : ℕ, 2 ≤ b → (IsNormal b (repReal ω) ↔ ∀ s : ℕ, b ≠ 3 ^ s) :=
  ae_repProfile_of fun _ hb h3 hp => repPairArith_of_three_dvd hb h3 hp

/-- The three open inputs of the crux: Baker's discrepancy for `m log₃ t` (cited), and the
copy-zone digit statements for every `b = 3ˢt`, `t > 1`, `3 ∤ t`. -/
def RepInputs : Prop :=
  CantorExactExponentProfile.Literature.BakerLogDiscrepancy ∧
    ∀ s t : ℕ, 1 ≤ s → 2 ≤ t → ¬ 3 ∣ t → TOrbitCyclicDecay t ∧ BadGcdSparseH (3 ^ s * t)

/-- **Crux from the inputs** (proved): `b = 3ˢt` and `repPairArith_of_inputs`. -/
theorem repPairArith_of_three_dvd_of_inputs (hI : RepInputs) {b : ℕ} (hb : 2 ≤ b) (h3 : 3 ∣ b)
    (hpow : ∀ s : ℕ, b ≠ 3 ^ s) : RepPairArith b := by
  obtain ⟨s, t, hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : b ≠ 0) 3 (by norm_num)
  have ht0 : t ≠ 0 := by rintro rfl; simp at hnd
  have ht1 : t ≠ 1 := by rintro rfl; exact hpow s (mul_one _)
  have hs : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at h3; exact absurd h3 hnd
    · exact h
  obtain ⟨hT, hS⟩ := hI.2 s t hs (by omega) hnd
  exact repPairArith_of_inputs hs (by omega) hnd hI.1 hT hS

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

/-- **Conditional headline (proved).**  The three inputs (`RepInputs`) give a Liouville number in
`K` normal exactly to the bases that are not powers of 3. -/
theorem liouvilleCantorFullProfile_of_inputs (hI : RepInputs) : LiouvilleCantorFullProfile := by
  obtain ⟨ω, hω⟩ := (ae_repProfile_of fun _ hb h3 hp =>
    repPairArith_of_three_dvd_of_inputs hI hb h3 hp).exists
  have h2 : IsNormal 2 (repReal ω) := (hω 2 le_rfl).2 fun s hs => by
    rcases s with _ | s
    · norm_num at hs
    · have : 3 ∣ 2 := hs ▸ dvd_pow_self 3 (Nat.succ_ne_zero s)
      norm_num at this
  exact ⟨repReal ω, repReal_mem_cantorSet ω,
    liouville_repReal ω (irrational_of_isNormal_two h2), hω⟩

/-- **Conditional headline from the literature (proved, modulo the sparse-pair leaves).**
Baker's discrepancy (two logarithms) and Matveev's bound (three logarithms) give a Liouville
number in `K` normal exactly to the bases that are not powers of 3. -/
theorem liouvilleCantorFullProfile_of_literature
    (hB : CantorExactExponentProfile.Literature.BakerLogDiscrepancy)
    (hM : SparseIdentity.Literature.MatveevThreeLogs) : LiouvilleCantorFullProfile := by
  obtain ⟨ω, hω⟩ := (ae_repProfile_of fun _ hb h3 hp =>
    repPairArith_of_literature hB hM hb h3 hp).exists
  have h2 : IsNormal 2 (repReal ω) := (hω 2 le_rfl).2 fun s hs => by
    rcases s with _ | s
    · norm_num at hs
    · have : 3 ∣ 2 := hs ▸ dvd_pow_self 3 (Nat.succ_ne_zero s)
      norm_num at this
  exact ⟨repReal ω, repReal_mem_cantorSet ω,
    liouville_repReal ω (irrational_of_isNormal_two h2), hω⟩

/-- **Conditional headline from Baker and the 3-adic two-logarithm bound (proved).** -/
theorem liouvilleCantorFullProfile_of_baker_padic
    (hB : CantorExactExponentProfile.Literature.BakerLogDiscrepancy)
    (hP : SparseIdentity.Literature.PadicTwoLogs) : LiouvilleCantorFullProfile := by
  obtain ⟨ω, hω⟩ := (ae_repProfile_of fun _ hb h3 hp =>
    repPairArith_of_baker_padic hB hP hb h3 hp).exists
  have h2 : IsNormal 2 (repReal ω) := (hω 2 le_rfl).2 fun s hs => by
    rcases s with _ | s
    · norm_num at hs
    · have : 3 ∣ 2 := hs ▸ dvd_pow_self 3 (Nat.succ_ne_zero s)
      norm_num at this
  exact ⟨repReal ω, repReal_mem_cantorSet ω,
    liouville_repReal ω (irrational_of_isNormal_two h2), hω⟩

/-- **Conditional headline from one cited input (wired; open only through
`repPairArith_of_sparse`).**  The 3-adic two-logarithm bound gives a Liouville number in `K`
normal exactly to the bases that are not powers of 3. -/
theorem liouvilleCantorFullProfile_of_padic (hP : SparseIdentity.Literature.PadicTwoLogs) :
    LiouvilleCantorFullProfile := by
  obtain ⟨ω, hω⟩ := (ae_repProfile_of fun _ hb h3 hp => repPairArith_of_padic hP hb h3 hp).exists
  have h2 : IsNormal 2 (repReal ω) := (hω 2 le_rfl).2 fun s hs => by
    rcases s with _ | s
    · norm_num at hs
    · have : 3 ∣ 2 := hs ▸ dvd_pow_self 3 (Nat.succ_ne_zero s)
      norm_num at this
  exact ⟨repReal ω, repReal_mem_cantorSet ω,
    liouville_repReal ω (irrational_of_isNormal_two h2), hω⟩

end NormalNumbers.CantorRepetition
